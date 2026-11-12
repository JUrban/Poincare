(* ========================================================================= *)
(* pc_apx_chain: chains of eps-necks (MT Lemmas A.15, A.17-A.18, Prop A.19   *)
(* and the termination lemma T3b of pc_apx_defs): the frontier               *)
(* of a positively infinite chain, extension of a balanced chain at its      *)
(* positive end, finiteness of balanced chains centred in a compact set, and *)
(* covering a compact connected set of neck centres by the union of a finite *)
(* balanced chain, which is an eps-tube (A13).                               *)
(* ========================================================================= *)

needs "src/pc_apx_a13.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The context apx_ch_ctx at a fixed scale eps: N2 at alpha                 *)
(* 1/100 and 1/200, the scale comparison of overlapping necks, and the       *)
(* comparison of the scalar curvature at a point of a neck with that at its  *)
(* centre.  Then the basic metric facts: levels of a neck through a deep     *)
(* point of another neck lie in it, and points near a centre are deep.       *)
(* ------------------------------------------------------------------------- *)

let apx_ch_ctx = new_definition
 `apx_ch_ctx (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (eps:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    &0 < eps /\ eps <= &1 / &1024 /\
    apx_eng_n2 top atlas g eps (&1 / &100) /\ apx_eng_n2 top atlas g eps (&1 / &200) /\
    (!x1 (e1:real^3->A) x2 e2 v.
        rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
        v IN rfs_neck_dom eps /\ e2 v IN IMAGE e1 (rfs_neck_dom eps)
        ==> inv(sqrt(mfd_scalar atlas g x2)) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g x1))) /\
    (!x1 (e1:real^3->A) y.
        rfs_neck (top,atlas) g eps x1 e1 /\ y IN rfs_neck_dom eps
        ==> mfd_scalar atlas g x1 <= &2 * mfd_scalar atlas g (e1 y))`;;


let APX_DEEP_LEVELS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) x' (e':real^3->A) z0 x0 K v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < eps /\
     apx_eng_n2 top atlas g eps (&1 / &100) /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
     inv(sqrt(mfd_scalar atlas g x')) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g x)) /\
     z0 IN rfs_neck_dom eps /\ abs(apx_sval z0) <= K /\
     x0 IN sphere(vec 0,&1) /\ e' x0 = e z0 /\ v IN rfs_neck_dom eps /\
     &101 / &100 * &3 / &2 * (abs(apx_sval v) + &24 / &5) < &99 / &100 * (inv eps - K)
     ==> e' v IN IMAGE e (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x'))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x':A`; `e':real^3->A`; `x0:real^3`; `v:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN STRIP_TAC THEN
  ABBREV_TAC `ri = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `ri' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x'))` THEN
  ABBREV_TAC `D1 = mfd_dist (top,atlas) (g:A->real^3^3) (e(z0:real^3)) (e'(v:real^3))` THEN
  ABBREV_TAC `rx = (&1 - &1 / &100) * ri * (inv eps - abs(apx_sval(z0:real^3)))` THEN
  SUBGOAL_THEN `D1 < rx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &100) * ri' * (abs(apx_sval(v:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&101 / &100 * (&3 / &2 * ri) * (abs(apx_sval(v:real^3)) + &24 / &5)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= p /\ p <= q
                               ==> (&1 + &1 / &100) * p <= &101 / &100 * q`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MP_TAC APX_SQRT2_PI THEN
        SUBGOAL_THEN `&0 <= sqrt(&2) * pi` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
          ALL_TAC] THEN
        MP_TAC(ISPEC `apx_sval(v:real^3)` REAL_ABS_POS) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&99 / &100 * ri * (inv eps - K)` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `ri * (&101 / &100 * &3 / &2 * (abs(apx_sval(v:real^3)) + &24 / &5)) <
                      ri * (&99 / &100 * (inv eps - K))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        EXPAND_TAC "rx" THEN
        SUBGOAL_THEN `ri * (inv eps - K) <= ri * (inv eps - abs(apx_sval(z0:real^3)))`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(e:real^3->A) z0`; `(e':real^3->A) v`; `rx:real`] APX_DIST_SHORT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z0:real^3`; `z0:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `&0`; `&1`] o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_CENTRE_DEEP_BALL = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < eps /\
     apx_eng_n2 top atlas g eps (&1 / &100) /\ rfs_neck (top,atlas) g eps x e /\
     mfd_joinable (top,atlas) x q /\
     mfd_dist (top,atlas) g x q <
     &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * inv(&8 * eps)
     ==> ?z. z IN rfs_neck_dom eps /\ abs(apx_sval z) < inv(&8 * eps) /\ e z = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (e:real^3->A) x0 = x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ inv(&8 * eps) = inv eps / &8` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ri = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `(q:A) IN IMAGE e (rfs_neck_dom eps)` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `q:A`; `&99 / &100 * ri * inv(&8 * eps)`] APX_DIST_SHORT_CURVE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `x0:real^3`; `x0:real^3`] o
      REWRITE_RULE[apx_eng_n2] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
        can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `&0`; `&1`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&0 <= ri * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `x0:real^3`; `z:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x q < &99 / &100 * ri * inv(&8 * eps)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ri * ((&1 - &1 / &100) *
                      min (abs(apx_sval(z:real^3))) (&2 * inv eps - abs(apx_sval z))) <
                ri * (&99 / &100 * inv eps / &8)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
  UNDISCH_TAC `abs(apx_sval(z:real^3)) < inv eps` THEN
  UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* T3b.  In a chain (clause (2): later necks miss the negative              *)
(* quarters of earlier ones, earlier necks miss the positive quarters of     *)
(* later ones) no centre lies in the middle region |s| <= 1/(8 eps) of       *)
(* another neck, so centres are uniformly separated where the scales are     *)
(* bounded below; a chain centred in a compact set is finite.                *)
(* ------------------------------------------------------------------------- *)

let APX_CHAIN_NO_DEEP_CENTRE = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) i j z.
     apx_ch_ctx top atlas g eps /\ apx_chain (top,atlas) g eps Ix x e /\
     i IN Ix /\ j IN Ix /\ ~(i = j) /\
     z IN rfs_neck_dom eps /\ abs(apx_sval z) <= inv(&8 * eps) /\ e i z = x j
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_chain] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain")) (concl th))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i) /\
                rfs_neck (top,atlas) g eps (x j) (e j)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (e:int->real^3->A) j x0 = x j`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) j)
                          ((e:int->real^3->A) j)` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x0:real^3) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:int->real^3->A) j x0 = e i z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) j))) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g (x i)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`(e:int->real^3->A) i`; `(e:int->real^3->A) j`; `x0:real^3`] THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ inv(&2 * eps) = inv eps / &2 /\
                inv(&8 * eps) = inv eps / &8` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t = inv(&2 * eps) + &1 / &2` THEN
  SUBGOAL_THEN
   `!sg. (sg = &1 \/ sg = -- &1)
         ==> (e:int->real^3->A) j (exp((sg * t) / sqrt(&2)) % x0) IN
             IMAGE (e i) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [X_GEN_TAC `sg:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_DEEP_LEVELS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `(x:int->A) i`; `(x:int->A) j`; `z:real^3`;
                          `x0:real^3`; `inv(&8 * eps)`] THEN
    ASM_SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL] THEN
    SUBGOAL_THEN `abs(sg * t) = t` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(i:int) < j` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:int`; `j:int`] o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A) j (exp(t / sqrt(&2)) % x0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `-- &1`) THEN
    REWRITE_TAC[REAL_ARITH `-- &1 * t = --t`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:int`; `i:int`] o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~((i:int) < j)` THEN UNDISCH_TAC `~(i:int = j)` THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A) j (exp(--t / sqrt(&2)) % x0)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC]);;

let APX_CHAIN_FINITE_CORE = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) K.
     apx_ch_ctx top atlas g eps /\ apx_chain (top,atlas) g eps Ix x e /\
     compact_in top K /\ (!i. i IN Ix ==> x i IN K)
     ==> FINITE Ix`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `!i. i IN Ix ==> rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Rm. &1 <= Rm /\ !p. p IN K ==> mfd_scalar atlas (g:A->real^3^3) p <= Rm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `mfd_scalar atlas (g:A->real^3^3)`;
                   `K:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN
    EXISTS_TAC `max (&1) B` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt Rm) /\ &0 < inv(&8 * eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `r = &99 / &100 * inv(sqrt Rm) * inv(&8 * eps)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* separation of the centres *)
  SUBGOAL_THEN
   `!i j. i IN Ix /\ j IN Ix /\ mfd_joinable (top,atlas) ((x:int->A) i) (x j) /\
          mfd_dist (top,atlas) (g:A->real^3^3) (x i) (x j) < r ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `r <= &99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i))) *
                       inv(&8 * eps)` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
          is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist"))
                              (concl th)))) THEN
        SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `(x:int->A) i`; `(e:int->real^3->A) i`; `(x:int->A) j`]
                  APX_CENTRE_DEEP_BALL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC APX_CHAIN_NO_DEEP_CENTRE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `eps:real`; `Ix:int->bool`; `x:int->A`;
                          `e:int->real^3->A`; `i:int`; `j:int`; `z:real^3`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* a finite cover of K by balls of radius r / 2 *)
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `{mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      EXISTS_TAC `p:A` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i IN Ix ==> ?B. B IN V /\ (x:int->A) i IN B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:int->A) i IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\i. @B. B IN V /\ (x:int->A) i IN B) Ix)` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:int`; `j:int`] THEN BETA_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B0 = @B. B IN V /\ (x:int->A) i IN B` THEN
  SUBGOAL_THEN `B0 IN V /\ (x:int->A) i IN B0 /\ x j IN B0` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(j:int) IN Ix`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. p IN K /\ B0 = mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `B0 IN (V:(A->bool)->bool)` THEN
    UNDISCH_TAC `V SUBSET {mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:int->A) i IN B0` THEN UNDISCH_TAC `(x:int->A) j IN B0` THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) ((x:int->A) i) p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(x:int->A) i`;
                   `p:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `r:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:int->A) i) p +
                mfd_dist (top,atlas) g p (x j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `(x:int->A) i`; `p:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The pair structure of consecutive chain necks at a scale eps              *)
(* (apx_ch_pair: APX_CHAIN_PAIR_STRUCT with alpha1 = 1/2560^2, so the        *)
(* comparison error is 1/(32 eps)), the constants (the context holds for all *)
(* small eps), and T3b: APX_CHAIN_FINITE.                                    *)
(* ------------------------------------------------------------------------- *)

let apx_ch_pair = new_definition
 `apx_ch_pair (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              (eps:real) <=>
    !x1 (e1:real^3->A) x2 e2 (ei:A->real^3).
      rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
      (!z. z IN rfs_neck_dom eps ==> ei(e1 z) = z) /\
      IMAGE e1 (apx_slab (inv(&2 * eps)) (inv eps)) UNION
      IMAGE e2 (apx_slab (--inv eps) (--inv(&2 * eps)))
      SUBSET IMAGE e1 (rfs_neck_dom eps) INTER IMAGE e2 (rfs_neck_dom eps) /\
      IMAGE e1 (rfs_neck_dom eps) INTER IMAGE e2 (rfs_neck_dom eps)
      SUBSET IMAGE e1 (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
             IMAGE e2 (apx_slab (--inv eps) (inv(&2 * eps)))
      ==> ?Delta. inv(&2 * eps) <= Delta /\ Delta <= &3 * inv(&2 * eps) /\
                  (!v. v IN rfs_neck_dom eps /\ e2 v IN IMAGE e1 (rfs_neck_dom eps)
                       ==> abs(apx_sval(ei(e2 v)) - apx_sval v - Delta) <= inv(&32 * eps)) /\
                  (!v. v IN rfs_neck_dom eps /\
                       apx_sval v < inv eps - Delta - inv(&32 * eps)
                       ==> e2 v IN IMAGE e1 (rfs_neck_dom eps))`;;

let APX_CH_CTX_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &6553600`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&1 / &100` th) THEN MP_TAC(SPEC `&1 / &200` th)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2b"))) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2a"))) THEN
  ABBREV_TAC `alpha1 = &1 / &6553600` THEN
  SUBGOAL_THEN `&0 < alpha1 /\ alpha1 <= &1 / &4096 /\ sqrt alpha1 = &1 / &2560`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha1" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `eps1 = min eps2 alpha1` THEN
  SUBGOAL_THEN `&0 < eps1 /\ eps1 <= alpha1 /\ eps1 <= eps2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
      &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
      rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
      ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
          <= alpha1 /\
          (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                   lricci (cylinder_flow (&0)) y w w)
               <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_TRANSITION_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "tr")] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_PAIR_STRUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ps")] THEN
  EXISTS_TAC `min (min eps1 (&1 / &1024)) (min eps3 eps4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= &1 / &1024 /\ eps <= eps3 /\ eps <= eps4 /\
                eps <= eps2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_ch_ctx; apx_ch_pair] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apx_eng_n2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n2a" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `y1:real^3`; `z1:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[apx_eng_n2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n2b" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `y1:real^3`; `z1:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e1:real^3->A`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "tr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
      `ei:A->real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_INV_SQRT_RATIO THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x2 e2` THEN SIMP_TAC[rfs_neck];
      ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x1:A`; `e1:real^3->A`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x1:A`; `e1:real^3->A`] APX_NECK_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x1` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e1:real^3->A) (g:A->real^3^3)`;
                   `mfd_scalar atlas (g:A->real^3^3) x1`; `y:real^3`] LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `rfs_neck_dom eps`; `e1:real^3->A`; `y:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 <= mfd_scalar atlas (g:A->real^3^3) ((e1:real^3->A) y) /
                             mfd_scalar atlas g x1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "ps" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
      `ei:A->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `Delta:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&80 * sqrt alpha1 * inv eps = inv(&32 * eps)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* T3b: a balanced chain centred in a compact set is finite. *)

let APX_CHAIN_FINITE = prove
 (`!u:A->bool. APX_CHAIN_FINITE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_CHAIN_FINITE_STATEMENT] THEN
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx")) APX_CH_CTX_HOLDS THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `Ix:int->bool = {}` THENL [ASM_REWRITE_TAC[FINITE_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x (e:int->real^3->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apx_balanced]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~(Ix:int->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x (e:int->real^3->A)` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC APX_CHAIN_FINITE_CORE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `eps:real`; `x:int->A`; `e:int->real^3->A`;
                        `K:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* T2, MT Lemma A.15.  Short curves from a point of a neck stay              *)
(* in it; every point of a positively infinite chain is deep in some neck or *)
(* lies in the bottom region of N_0; a frontier point p of the union has a   *)
(* neighbourhood (scalar curvature below R(p) + 1, metric ball) meeting the  *)
(* union only in the negative quarter of N_0 (a deep neighbour would contain *)
(* p by its exit length).                                                    *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_EXIT_BALL = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < eps /\
     apx_eng_n2 top atlas g eps (&1 / &100) /\ rfs_neck (top,atlas) g eps x e /\
     z IN rfs_neck_dom eps /\ mfd_joinable (top,atlas) (e z) q /\
     mfd_dist (top,atlas) g (e z) q <
     &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * (inv eps - abs(apx_sval z))
     ==> q IN IMAGE e (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(e:real^3->A) z`; `q:A`;
                 `&99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                  (inv eps - abs(apx_sval(z:real^3)))`] APX_DIST_SHORT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z:real^3`; `z:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `&0`; `&1`] o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_INF_CHAIN_COVER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) q.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
     q IN apx_chain_union eps {i:int | &0 <= i} e
     ==> ?i z. &0 <= i /\ z IN rfs_neck_dom eps /\ e i z = q /\
               (abs(apx_sval z) <= &7 / &8 * inv eps - &10 \/
                (i = &0 /\ apx_sval z < --(&7 / &8 * inv eps - &10)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_chain; IN_ELIM_THM] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain")) (concl th))) THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ inv(&2 * eps) = inv eps / &2 /\
                inv(&32 * eps) = inv eps / &32` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `q IN apx_chain_union eps {i:int | &0 <= i} (e:int->real^3->A)` THEN
  REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  ASM_CASES_TAC `abs(apx_sval(z:real^3)) <= &7 / &8 * inv eps - &10` THENL
   [MAP_EVERY EXISTS_TAC [`i:int`; `z:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `&0 < apx_sval(z:real^3)` THENL
   [SUBGOAL_THEN `&0 <= (i:int) + &1` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 <= (i:int)` THEN INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i) /\
                  rfs_neck (top,atlas) g eps (x(i + &1)) (e(i + &1))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
        if is_forall (concl th) &&
           can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
           not (can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))
        then MATCH_MP_TAC th else failwith "not the neck clause") THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i) ((e:int->real^3->A) i)` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(x:int->A) i`; `(e:int->real^3->A) i`; `(x:int->A)(i + &1)`;
                                `(e:int->real^3->A)(i + &1)`; `ei:A->real^3`] o
      REWRITE_RULE[apx_ch_pair] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_pair")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:A) IN IMAGE ((e:int->real^3->A)(i + &1)) (rfs_neck_dom eps)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE ((e:int->real^3->A) i) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
                   IMAGE (e(i + &1)) (apx_slab (--inv eps) (--inv(&2 * eps)))
                   SUBSET IMAGE (e i) (rfs_neck_dom eps) INTER
                          IMAGE (e(i + &1)) (rfs_neck_dom eps)` THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
      ANTS_TAC THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ei:A->real^3)((e:int->real^3->A)(i + &1) v) = z` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`(i:int) + &1`; `v:real^3`] THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:int = &0` THENL
   [MAP_EVERY EXISTS_TAC [`i:int`; `z:real^3`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?j:int. &0 <= j /\ i = j + &1`
  (X_CHOOSE_THEN `j:int` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [EXISTS_TAC `(i:int) - &1` THEN UNDISCH_TAC `~(i:int = &0)` THEN
    UNDISCH_TAC `&0 <= (i:int)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) j) ((e:int->real^3->A) j) /\
                rfs_neck (top,atlas) g eps (x(j + &1)) (e(j + &1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      if is_forall (concl th) &&
         can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
         not (can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))
      then MATCH_MP_TAC th else failwith "not the neck clause") THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A) j`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) j) ((e:int->real^3->A) j)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:int` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:int->A) j`; `(e:int->real^3->A) j`; `(x:int->A)(j + &1)`;
                              `(e:int->real^3->A)(j + &1)`; `ei:A->real^3`] o
    REWRITE_RULE[apx_ch_pair] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_pair")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q:A) IN IMAGE ((e:int->real^3->A) j) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((e:int->real^3->A) j) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
                 IMAGE (e(j + &1)) (apx_slab (--inv eps) (--inv(&2 * eps)))
                 SUBSET IMAGE (e j) (rfs_neck_dom eps) INTER
                        IMAGE (e(j + &1)) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
    ANTS_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `(e:int->real^3->A)(j + &1) z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`j:int`; `(ei:A->real^3) q`] THEN
  SUBGOAL_THEN `(ei:A->real^3) q IN rfs_neck_dom eps /\ (e:int->real^3->A) j (ei q) = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:A) IN IMAGE ((e:int->real^3->A) j) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC);;

let APX_A15_CORE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
     ==> top frontier_of (apx_chain_union eps {i:int | &0 <= i} e) SUBSET
         top closure_of (IMAGE (e (&0)) (apx_slab (--inv eps) (--inv(&2 * eps))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `!i. &0 <= i ==> rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union eps {i:int | &0 <= i} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `&0 <= (i:int)`) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar"))
                            (concl th)))) THEN
      SIMP_TAC[rfs_neck];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = max (mfd_scalar atlas (g:A->real^3^3) p) (&0) + &1` THEN
  SUBGOAL_THEN `&0 < c /\ mfd_scalar atlas (g:A->real^3^3) p < c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `hs = inv(sqrt(&2 * c))` THEN
  SUBGOAL_THEN `&0 < hs` ASSUME_TAC THENL
   [EXPAND_TAC "hs" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = &99 / &100 * hs * (inv eps / &8 + &10)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `O = {q:A | q IN topspace top /\ mfd_scalar atlas (g:A->real^3^3) q IN
                         {t | t < c}} INTER mfd_ball (top,atlas) g p r` THEN
  SUBGOAL_THEN `open_in top (O:A->bool) /\ (p:A) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
      REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS; GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT];
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  (* the union meets O only in the negative quarter of N_0 *)
  SUBGOAL_THEN
   `!q. q IN U /\ q IN O
        ==> q IN IMAGE ((e:int->real^3->A)(&0)) (apx_slab (--inv eps) (--inv(&2 * eps)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:int->A`; `e:int->real^3->A`; `q:A`] APX_INF_CHAIN_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
    MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [(* deep: p would lie in the neck *)
      MATCH_MP_TAC(TAUT `F ==> p`) THEN UNDISCH_TAC `~((p:A) IN U)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:A) IN IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)` MP_TAC THENL
       [ALL_TAC;
        EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_TAC THEN EXISTS_TAC `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN O` THEN EXPAND_TAC "O" THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; mfd_ball] THEN STRIP_TAC THEN
      MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `(x:int->A) i`; `z:real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `q:A`; `p:A`] MFD_JOINABLE_SYM) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "r" THEN
      SUBGOAL_THEN `hs <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)))`
      ASSUME_TAC THENL
       [EXPAND_TAC "hs" THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) /\
                      mfd_scalar atlas g (x i) <= &2 * c` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i)
                                  ((e:int->real^3->A) i)` THEN SIMP_TAC[rfs_neck];
            MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `&2 * mfd_scalar atlas (g:A->real^3^3) q` THEN CONJ_TAC THENL
             [UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
              FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
                is_forall (concl th) && can (find_term (fun t -> t = `&2`)) (concl th) &&
                can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar"))
                    (concl th) &&
                not (can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt"))
                         (concl th)))) THEN
              ASM_REWRITE_TAC[];
              ASM_REAL_ARITH_TAC]];
          ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE]];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv eps / &8 + &10 <= inv eps - abs(apx_sval(z:real^3))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      (* bottom of N_0 *)
      UNDISCH_TAC `(e:int->real^3->A)(&0) z = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_CLOSURE_OF] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:A) IN top closure_of U` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
  DISCH_THEN(MP_TAC o SPEC `t INTER O:A->bool` o CONJUNCT2) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:A` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `O:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* T2, MT Lemma A.15. *)

let APX_A15 = prove
 (`!u:A->bool. APX_A15_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A15_STATEMENT] THEN
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx")) APX_CH_CTX_HOLDS THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x
                           (e:int->real^3->A)` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&0:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_LE_REFL] THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC APX_A15_CORE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reversed neck.  apx_rev e = e o (y -> y/|y|^2); the                  *)
(* inversion is a diffeomorphism of the neck domain and an isometry of the  *)
(* cylinder metric cylinder_flow 0, so by LCK_DIST2_PULLBACK the reversed   *)
(* chart of an eps-neck is an eps-neck with the same centre.                *)
(* ------------------------------------------------------------------------- *)

let APX_MPULLBACK_CHAIN = prove
 (`!(h:real^N->real^N) (k:real^N->real^N) G z.
     h differentiable at z /\ k differentiable at (h z)
     ==> mpullback h (mpullback k G) z = mpullback (k o h) G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN
   `frechet_derivative ((k:real^N->real^N) o (h:real^N->real^N)) (at z) =
    frechet_derivative k (at (h z)) o frechet_derivative h (at z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^N` THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `z:real^N`; `u:real^N`]
                  LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at z)) /\
                linear(frechet_derivative (k:real^N->real^N) (at (h z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let APX_RFS_PULLBACK_PRECOMP = prove
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
  REWRITE_TAC[o_ASSOC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_MPULLBACK_CHAIN THEN
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

let APX_INVERSION_CYL0 = prove
 (`!y:real^3.
        ~(y = vec 0)
        ==> mpullback (\z:real^3. inv(norm z pow 2) % z) (cylinder_flow (&0)) y =
            cylinder_flow (&0) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPEC `y:real^3` RFB_INVERSION_HAS_DERIVATIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)] THEN
                       ASSUME_TAC th) THEN
  SUBGOAL_THEN `!w:real^3. cylinder_flow (&0) w = (&2 / norm w pow 2) %% mat 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[MATRIX_CMUL_LID; MATRIX_CMUL_LZERO; MATRIX_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) RFB_CONGRUENCE_DOT (lhand w))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. inv(norm z pow 2) % z`; `at(y:real^3)`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; DOT_LMUL;
              DOT_LSUB; DOT_RSUB; NORM_POW_2; REAL_POW_INV] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let APX_REV_NECK = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e
     ==> rfs_neck (top,atlas) g eps x (apx_rev e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  STRIP_TAC THEN
  ABBREV_TAC `iv = \z:real^3. inv(norm z pow 2) % z` THEN
  SUBGOAL_THEN `apx_rev (e:real^3->A) = e o iv` SUBST1_TAC THENL
   [EXPAND_TAC "iv" THEN REWRITE_TAC[apx_rev; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom eps) (iv:real^3->real^3) iv`
  ASSUME_TAC THENL
   [EXPAND_TAC "iv" THEN REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM] THEN
    MP_TAC(INST_TYPE [`:3`,`:N`] (SPECL [`exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
                  SMT_DIFFEO_INVERSION_ANNULUS)) THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG; REAL_INV_INV; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[GSYM REAL_EXP_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `&0 < inv eps * inv(sqrt(&2))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((e:real^3->A) o iv)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `rfs_neck_dom eps`; `iv:real^3->real^3`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x0:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "iv" THEN UNDISCH_TAC `(x0:real^3) IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_close_on (rfs_kreg eps) eps (rfs_neck_dom eps) (cylinder_flow (&0))
                 (\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y)` THEN
  REWRITE_TAC[rfs_close_on] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(iv:real^3->real^3) y IN rfs_neck_dom eps` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom eps) (iv:real^3->real^3) iv` THEN
    REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                (\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y)
                ((iv:real^3->real^3) y)` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_neck_dom eps`; `rfs_neck_dom eps`; `iv:real^3->real^3`;
                 `iv:real^3->real^3`; `cylinder_flow (&0)`;
                 `\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y`;
                 `y:real^3`] LCK_DIST2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "iv" THEN ASM_SIMP_TAC[APX_INVERSION_CYL0]; ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `rfs_neck_dom eps`; `iv:real^3->real^3`;
                 `iv:real^3->real^3`; `w:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* More facts at the scale eps (apx_ch_more): the scalar                     *)
(* curvature ratio and the derivative alignment of overlapping necks (from  *)
(* APX_TRANSITION_DERIV with alpha1 = 1/2560^2), the 1% scale comparison,    *)
(* and N4 (neck spheres inside necks are sections).                          *)
(* ------------------------------------------------------------------------- *)

let apx_ch_more = new_definition
 `apx_ch_more (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              (eps:real) <=>
    (!x1 (e1:real^3->A) x2 e2 v.
       rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
       v IN rfs_neck_dom eps /\ e2 v IN IMAGE e1 (rfs_neck_dom eps)
       ==> abs(mfd_scalar atlas g x1 / mfd_scalar atlas g x2 - &1) <= &1 / &1638400 /\
           inv(sqrt(mfd_scalar atlas g x2)) <= &101 / &100 * inv(sqrt(mfd_scalar atlas g x1))) /\
    (!x1 (e1:real^3->A) x2 e2 (ei:A->real^3) v.
       rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
       (!z. z IN rfs_neck_dom eps ==> ei(e1 z) = z) /\
       v IN rfs_neck_dom eps /\ e2 v IN IMAGE e1 (rfs_neck_dom eps)
       ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                !k. abs(sqrt(&2) * (ei(e2 v) dot frechet_derivative (ei o e2) (at v) k) /
                        (ei(e2 v) dot ei(e2 v)) -
                        sg * sqrt(mfd_scalar atlas g x1 / mfd_scalar atlas g x2) *
                        sqrt(&2) * (v dot k) / (v dot v))
                    <= &7 / &2560 * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
    (!x1 (e1:real^3->A) x2 e2.
       rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
       IMAGE e2 (sphere(vec 0,&1)) SUBSET IMAGE e1 (rfs_neck_dom eps)
       ==> apx_section e1 (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                       (IMAGE e2 (sphere(vec 0,&1))))`;;

let APX_INV_SQRT_RATIO_GEN = prove
 (`!r1 r2 c. &0 < r1 /\ &0 < r2 /\ &0 < c /\ r1 / r2 <= c pow 2
             ==> inv(sqrt r2) <= c * inv(sqrt r1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt r1 /\ &0 < sqrt r2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt r1 <= c * sqrt r2` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(r1 / r2) <= sqrt(c pow 2)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; SQRT_DIV; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * inv(sqrt r1) = inv(inv c * sqrt r1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `inv c * sqrt r1 <= inv c * (c * sqrt r2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]]);;

let APX_CH_MORE_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> apx_ch_more top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &6553600`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_SECTION_UNCOND) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4"))) THEN
  ABBREV_TAC `alpha1 = &1 / &6553600` THEN
  SUBGOAL_THEN `&0 < alpha1 /\ alpha1 <= &1 / &4096 /\ sqrt alpha1 = &1 / &2560 /\
                &4 * alpha1 = &1 / &1638400`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha1" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `eps1 = min eps2 alpha1` THEN
  SUBGOAL_THEN `&0 < eps1 /\ eps1 <= alpha1 /\ eps1 <= eps2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
      &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
      rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
      ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
          <= alpha1 /\
          (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                   lricci (cylinder_flow (&0)) y w w)
               <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_TRANSITION_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "tr")] THEN
  EXISTS_TAC `min eps1 eps4` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= eps4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_ch_more] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e1:real^3->A`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "tr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
      `ei:A->real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_INV_SQRT_RATIO_GEN THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x2 e2` THEN SIMP_TAC[rfs_neck];
      REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
      `ei:A->real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sg:real` THEN
    REWRITE_TAC[REAL_ARITH `&7 * &1 / &2560 * x = &7 / &2560 * x`];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n4" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
      `&1`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM; REAL_LT_01]; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A.17, part 1.  N4 for spheres of any radius in the neck                   *)
(* domain (apx_ch_n4r); a point z outside a neck e in the closure of its     *)
(* positive quarter: distances from z to points of the neck, approximating  *)
(* points of the top end, and the positive quarter of e lies in any eps-neck *)
(* centred at z (Claim A).                                                   *)
(* ------------------------------------------------------------------------- *)

let apx_ch_n4r = new_definition
 `apx_ch_n4r (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (eps:real) <=>
    !x1 (e1:real^3->A) x2 e2 r.
       rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\ &0 < r /\
       sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
       IMAGE e2 (sphere(vec 0,r)) SUBSET IMAGE e1 (rfs_neck_dom eps)
       ==> apx_section e1 (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                       (IMAGE e2 (sphere(vec 0,r)))`;;

let APX_CH_N4R_HOLDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g
        ==> apx_ch_n4r top atlas g eps`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_SECTION_UNCOND) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT; apx_ch_n4r] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "n4" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`; `r:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let APX_FRONTIER_LOWER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z y.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps x e /\
     ~(z IN IMAGE e (rfs_neck_dom eps)) /\ y IN rfs_neck_dom eps /\
     mfd_joinable (top,atlas) z (e y)
     ==> &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * (inv eps - abs(apx_sval y)) <=
         mfd_dist (top,atlas) g z (e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((z:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(e:real^3->A) y`; `z:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `(e:real^3->A) y`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let APX_FRONTIER_POINT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z d.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps x e /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps)) /\ &0 < d
     ==> ?y. y IN apx_slab (inv(&2 * eps)) (inv eps) /\
             mfd_joinable (top,atlas) z (e y) /\ mfd_dist (top,atlas) g z (e y) < d /\
             &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * (inv eps - apx_sval y) <=
             mfd_dist (top,atlas) g z (e y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(z:A) IN top closure_of
               (IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)))` THEN
  REWRITE_TAC[IN_CLOSURE_OF] THEN
  DISCH_THEN(MP_TAC o SPEC `mfd_ball (top,atlas) (g:A->real^3^3) z d` o CONJUNCT2) THEN
  ASM_SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL] THEN
  REWRITE_TAC[IN_IMAGE; mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `y:real^3` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) z ((e:real^3->A) y) /\
                mfd_dist (top,atlas) (g:A->real^3^3) z (e y) < d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:A) = (e:real^3->A) y` THEN DISCH_THEN(SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y) = apx_sval y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `&0 < inv(&2 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `y:real^3`] APX_FRONTIER_LOWER) THEN
  ASM_REWRITE_TAC[]);;

(* Claim A: the positive quarter of e lies in every eps-neck centred at z. *)

let APX_FRONTIER_QUARTER_IN = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A).
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps x e /\
     rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET IMAGE ez (rfs_neck_dom eps) /\
         inv(sqrt(mfd_scalar atlas g x)) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (ez:real^3->A) x0 = z` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z ez` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) /\ &0 < inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  (* the exit from z *)
  SUBGOAL_THEN
   `!q. mfd_joinable (top,atlas) z q /\
        mfd_dist (top,atlas) (g:A->real^3^3) z q < &99 / &100 * h' * inv eps
        ==> q IN IMAGE (ez:real^3->A) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `z:A`; `x0:real^3`] THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO];
    ALL_TAC] THEN
  (* scale comparison from an overlap point *)
  SUBGOAL_THEN `h <= &3 / &2 * h'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `&99 / &100 * h' * inv eps`]
                  APX_FRONTIER_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^3->A) y IN IMAGE (ez:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["h"; "h'"] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`ez:real^3->A`; `e:real^3->A`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `h:real`] APX_FRONTIER_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y'':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ (y'':real^3) IN rfs_neck_dom eps /\
                abs(apx_sval y'' - apx_sval y) < inv eps / &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
    UNDISCH_TAC `(y'':real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `y'':real^3`; `y:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `h':real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist")) (concl th))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(e:real^3->A) y''` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) z ((e:real^3->A) y'') +
              mfd_dist (top,atlas) g (e y'') (e y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) y'') (e y) <=
                (&1 + &1 / &100) * h * (inv eps / &2 + &24 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &100) * h * (abs(apx_sval(y'':real^3) - apx_sval(y:real^3)) +
                                        sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h * (&1 + (&1 + &1 / &100) * (inv eps / &2 + &24 / &5)) <=
                (&3 / &2 * h') * (&1 + (&1 + &1 / &100) * (inv eps / &2 + &24 / &5))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h' * (&3 / &2 * (&1 + (&1 + &1 / &100) * (inv eps / &2 + &24 / &5))) <=
                h' * (&99 / &100 * inv eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A.17, part 2.  Orienting a radial section with levels away               *)
(* from 0 (reverse the chart if the levels are positive), and the section of *)
(* the new neck given by the level 5/(8 eps) sphere of the old neck.         *)
(* ------------------------------------------------------------------------- *)

let APX_SECTION_ORIENT = prove
 (`!(ez:real^3->A) (u:real^3->real) a b eps S.
     (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
     (!w. w IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
     S = IMAGE (\w. ez(u w % w)) (sphere(vec 0,&1)) /\ &0 < a /\
     (!w. w IN sphere(vec 0,&1)
          ==> a <= abs(apx_sval(u w % w)) /\ abs(apx_sval(u w % w)) <= b)
     ==> ?ez' (u':real^3->real).
           (ez' = ez \/ ez' = apx_rev ez) /\
           (\x. lift(u' x)) continuous_on sphere(vec 0,&1) /\
           (!w. w IN sphere(vec 0,&1)
                ==> exp(--inv eps / sqrt(&2)) < u' w /\ u' w < exp(inv eps / sqrt(&2))) /\
           S = IMAGE (\w. ez'(u' w % w)) (sphere(vec 0,&1)) /\
           (!w. w IN sphere(vec 0,&1)
                ==> --b <= apx_sval(u' w % w) /\ apx_sval(u' w % w) <= --a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN sphere(vec 0,&1)
        ==> &0 < (u:real^3->real) w /\ norm w = &1 /\
            apx_sval(u w % w) = sqrt(&2) * log(u w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) w` ASSUME_TAC THENL
     [MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(w:real^3) = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[apx_sval; NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!w. w IN sphere(vec 0,&1) ==> (u:real^3->real) w < &1) \/
                (!w. w IN sphere(vec 0,&1) ==> &1 < (u:real^3->real) w)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`\x:real^3. lift((u:real^3->real) x)`; `sphere(vec 0:real^3,&1)`]
                  CONNECTED_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift((u:real^3->real) w2)`; `lift((u:real^3->real) w1)`;
                               `lift(&1)`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `w2:real^3` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `w1:real^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; LIFT_EQ] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `a:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 = (u:real^3->real) w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    (* levels negative: keep ez *)
    MAP_EVERY EXISTS_TAC [`ez:real^3->A`; `u:real^3->real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `a:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `&1`)) (concl th))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `apx_sval((u:real^3->real) w % w) < &0` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&0 < --y <=> y < &0`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    (* levels positive: reverse ez *)
    MAP_EVERY EXISTS_TAC [`apx_rev(ez:real^3->A)`; `\w:real^3. inv((u:real^3->real) w)`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^3->real`; `sphere(vec 0:real^3,&1)`] CONTINUOUS_ON_INV) THEN
      ASM_SIMP_TAC[o_DEF; REAL_LT_IMP_NZ];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG] THEN
      SUBGOAL_THEN `&0 < exp(inv eps * inv(sqrt(&2)))` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
      SPEC_TAC(`exp(inv eps * inv(sqrt(&2)))`,`q:real`) THEN
      SPEC_TAC(`(u:real^3->real) w`,`p:real`) THEN REPEAT GEN_TAC THEN
      REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv q` THEN
        ASM_SIMP_TAC[REAL_LT_INV];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV]];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
        `(!w:real^3. w IN s ==> (f:real^3->A) w = g w) ==> IMAGE f s = IMAGE g s`) THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
      STRIP_TAC THEN REWRITE_TAC[apx_rev] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; VECTOR_MUL_ASSOC; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < (u:real^3->real) w` THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `a:real`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `&1`)) (concl th))) THEN
      REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `apx_sval(inv((u:real^3->real) w) % w) = --apx_sval(u w % w) /\
                    &0 < apx_sval(u w % w)` MP_TAC THENL
       [ASM_REWRITE_TAC[apx_sval; NORM_MUL; REAL_ABS_INV; REAL_MUL_RID] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; LOG_INV] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
          MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]];
        ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* A.17, part 3.  Levels in a neck ez centred at a frontier                  *)
(* point z of the points of the old neck e: a point at e-level at least s0   *)
(* has ez-level at most 103/100 (1/eps - s0) + 13/2 (it is near z), and a    *)
(* point at e-level at most 5/8 of 1/eps has ez-level at least 9/25 of 1/eps *)
(* (it is far from z).  Distances from N2 at 1/200, the 1% scale comparison. *)
(* ------------------------------------------------------------------------- *)

let APX_FRONTIER_LEVELS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A) y v.
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps)) /\
     y IN rfs_neck_dom eps /\ v IN rfs_neck_dom eps /\ e y = ez v
     ==> (!s0. s0 <= apx_sval y
               ==> abs(apx_sval v) <= &103 / &100 * (inv eps - s0) + &13 / &2) /\
         (abs(apx_sval y) <= &5 / &8 * inv eps
          ==> &9 / &25 * inv eps <= abs(apx_sval v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (ez:real^3->A) x0 = z` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z ez` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) /\ &0 < inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(y:real^3)) < inv eps /\ abs(apx_sval(v:real^3)) < inv eps`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  (* the scale comparisons in both directions *)
  SUBGOAL_THEN `(e:real^3->A) y IN IMAGE ez (rfs_neck_dom eps) /\
                (ez:real^3->A) v IN IMAGE e (rfs_neck_dom eps)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <=
    &101 / &100 * inv(sqrt(mfd_scalar atlas g z)) /\
    inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) <=
    &101 / &100 * inv(sqrt(mfd_scalar atlas g x))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[apx_ch_more] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_more")) (concl th))) THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`z:A`; `ez:real^3->A`; `x:A`; `e:real^3->A`; `y:real^3`] th) THEN
      MP_TAC(SPECL [`x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`; `v:real^3`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  (* N2 at 1/200 for the neck at z, between x0 and v *)
  FIRST_ASSUM(MP_TAC o SPECL [`z:A`; `ez:real^3->A`; `x0:real^3`; `v:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &200`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `min (abs(apx_sval(v:real^3))) (&2 * inv eps - abs(apx_sval v)) =
                abs(apx_sval v)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `tv = abs(apx_sval(v:real^3))` THEN
  ABBREV_TAC `pp = sqrt(&2) * pi` THEN
  SUBGOAL_THEN `&0 <= pp /\ pp <= &24 / &5` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[APX_SQRT2_PI] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `h / &2`] APX_FRONTIER_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y'':real^3` MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y'':real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(apx_sval(y'':real^3)) < inv eps` ASSUME_TAC THENL
     [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    SUBGOAL_THEN `inv eps - apx_sval(y'':real^3) < &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(&1 <= a) ==> a < &1`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `h * &1 <= h * (inv eps - apx_sval(y'':real^3))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `y'':real^3`; `y:real^3`] o
      REWRITE_RULE[apx_eng_n2] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
        can (find_term (fun t -> t = `&1 / &200`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:A->real^3^3) z ((ez:real^3->A) v) <=
      mfd_dist (top,atlas) g z ((e:real^3->A) y'') + mfd_dist (top,atlas) g (e y'') (ez v)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `ww = inv eps - s0` THEN
    ABBREV_TAC `da = abs(apx_sval(y'':real^3) - apx_sval(y:real^3))` THEN
    SUBGOAL_THEN `&0 <= ww /\ da <= ww + &1` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ww"; "da"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h * da <= h * (ww + &1) /\ h * pp <= h * (&24 / &5) /\
                  h * ww <= (&101 / &100 * h') * ww /\ &0 <= h' * ww`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `h' * tv <= h' * (&103 / &100 * ww + &13 / &2)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `y:real^3`] APX_FRONTIER_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `h * abs(apx_sval(y:real^3)) <= h * (&5 / &8 * inv eps) /\
                h' * inv eps <= (&101 / &100 * h) * inv eps /\
                h' * pp <= h' * (&24 / &5) /\ h' * &1024 <= h' * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h' * (&9 / &25 * inv eps) <= h' * tv` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ]);;

(* The sphere of radius exp(t/sqrt 2) is the level set t of apx_sval, and   *)
(* its image under e is the image of the unit sphere under the rescaled e.  *)

let APX_SPHERE_LEVEL = prove
 (`!t. sphere(vec 0:real^3,exp(t / sqrt(&2))) = {y | ~(y = vec 0) /\ apx_sval y = t}`,
  GEN_TAC THEN REWRITE_TAC[APX_SVAL_LEVEL_SPHERE] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`]
    (MATCH_MP SPHERE_SCALING (SPEC `t / sqrt(&2)` REAL_EXP_POS_LT))) THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; REAL_MUL_RID]);;

let APX_SPHERE_IMAGE_SCALE = prove
 (`!(e:real^3->A) r. &0 < r
        ==> IMAGE e (sphere(vec 0,r)) = IMAGE (\x. e(r % x)) (sphere(vec 0,&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`] (MATCH_MP SPHERE_SCALING (ASSUME `&0 < r`))) THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF]);;

(* The level 5/(8 eps) sphere Sigma of the old neck e is a section of the   *)
(* new neck, oriented so that its levels lie in [-2/5, -9/25] (1/eps).      *)

let APX_FRONTIER_SIGMA = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> ?ez' (u:real^3->real).
           (ez' = ez \/ ez' = apx_rev ez) /\
           (\w. lift(u w)) continuous_on sphere(vec 0,&1) /\
           (!w. w IN sphere(vec 0,&1)
                ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
           IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))) =
           IMAGE (\w. ez'(u w % w)) (sphere(vec 0,&1)) /\
           (!w. w IN sphere(vec 0,&1)
                ==> --(&2 / &5 * inv eps) <= apx_sval(u w % w) /\
                    apx_sval(u w % w) <= --(&9 / &25 * inv eps))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1024 <= inv eps /\ inv(&2 * eps) = inv eps / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_MUL] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &5 / &8 * inv eps` THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,exp(c1 / sqrt(&2))) SUBSET
                apx_slab (inv(&2 * eps)) (inv eps)` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SPHERE_LEVEL; SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c1" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`]
                APX_FRONTIER_QUARTER_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `apx_section (ez:real^3->A) (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                (IMAGE (e:real^3->A) (sphere(vec 0,exp(c1 / sqrt(&2)))))`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[apx_ch_n4r] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_n4r")) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `x:A`] THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP APX_SECTION_DATA) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ez:real^3->A`; `u:real^3->real`; `&9 / &25 * inv eps`;
                 `&2 / &5 * inv eps`; `eps:real`;
                 `IMAGE (e:real^3->A) (sphere(vec 0,exp(c1 / sqrt(&2))))`]
                APX_SECTION_ORIENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
                 APX_SECTION_BASICS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(ez:real^3->A)((u:real^3->real) w % w) IN
                  IMAGE (e:real^3->A) (sphere(vec 0,exp(c1 / sqrt(&2))))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ apx_sval y = c1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN sphere(vec 0,exp(c1 / sqrt(&2)))` THEN
      REWRITE_TAC[APX_SPHERE_LEVEL; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`; `y:real^3`;
                   `(u:real^3->real) w % w`] APX_FRONTIER_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `c1:real`) MP_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `abs c1 <= &5 / &8 * inv eps` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "c1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c1" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A.17, part 4.  The two sides of Sigma.  Every level sphere                *)
(* of a neck separates (apx_sphere_sep for the rescaled chart); the parts of *)
(* the new neck below and above the section Sigma, and the parts of the old *)
(* neck below and above Sigma, lie on the two sides: the lower parts in the  *)
(* component K of a point just below Sigma, the upper parts outside K.       *)
(* ------------------------------------------------------------------------- *)

let APX_LOG_43 = prove
 (`&0 < sqrt(&2) * log(&4 / &3) /\ sqrt(&2) * log(&4 / &3) < &3 / &2 /\
   --(&3 / &2) < sqrt(&2) * log(&3 / &4) /\ sqrt(&2) * log(&3 / &4) < &0`,
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `log(&1) < log(&4 / &3) /\ log(&4 / &3) < log(&2) /\
                log(&1 / &2) < log(&3 / &4) /\ log(&3 / &4) < log(&1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LOG_1]) THEN
  SUBGOAL_THEN `sqrt(&2) * &0 < sqrt(&2) * log(&4 / &3) /\
                sqrt(&2) * log(&4 / &3) < sqrt(&2) * log(&2) /\
                sqrt(&2) * log(&1 / &2) < sqrt(&2) * log(&3 / &4) /\
                sqrt(&2) * log(&3 / &4) < sqrt(&2) * &0` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC);;

let APX_SVAL_SCALED_BASIS = prove
 (`!c k. &0 < k
         ==> ~(exp(c / sqrt(&2)) % (k % basis 1:real^3) = vec 0) /\
             apx_sval(exp(c / sqrt(&2)) % (k % basis 1:real^3)) = c + sqrt(&2) * log k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k % basis 1:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; BASIS_NONZERO; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
  REWRITE_TAC[apx_sval; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`]);;

(* Every level sphere of a neck separates the two nearby points on the axis. *)

let APX_LEVEL_SPHERE_SEP = prove
 (`!top atlas (e:real^3->A) eps c.
     smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     mfd_param top atlas (rfs_neck_dom eps) e /\
     --inv eps + &3 / &2 <= c /\ c + &3 / &2 <= inv eps
     ==> apx_separates top (IMAGE e (sphere(vec 0,exp(c / sqrt(&2)))))
           (e(exp(c / sqrt(&2)) % (&3 / &4 % basis 1)))
           (e(exp(c / sqrt(&2)) % (&4 / &3 % basis 1)))`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (\x. (e:real^3->A)(exp(c / sqrt(&2)) % x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart; APX_ANNULUS_HALF_TWO] THEN
    SUBGOAL_THEN `(\x. (e:real^3->A)(exp(c / sqrt(&2)) % x)) =
                  e o (\x. exp(c / sqrt(&2)) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_neck_dom eps`;
      `apx_slab (--(sqrt(&2) * log(&2)) + c) (sqrt(&2) * log(&2) + c)`;
      `\x:real^3. exp(--c / sqrt(&2)) % x`] THEN
    ASM_REWRITE_TAC[APX_SLAB_SCALE_DIFFEO] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  REWRITE_TAC[apx_sphere_sep] THEN
  DISCH_THEN(MP_TAC o SPEC `\x. (e:real^3->A)(exp(c / sqrt(&2)) % x)`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e:real^3->A`; `exp(c / sqrt(&2))`] APX_SPHERE_IMAGE_SCALE) THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[]);;

(* The abstract side argument. *)

let APX_SIDES_ABSTRACT = prove
 (`!top S (Nl:A->bool) Nh Cm Cp pm pp.
     connected_in top Nl /\ connected_in top Nh /\ connected_in top Cm /\
     connected_in top Cp /\
     DISJOINT S Nl /\ DISJOINT S Nh /\ DISJOINT S Cm /\ DISJOINT S Cp /\
     ~(DISJOINT Nh Cp) /\ pm IN Cm /\ pp IN Cp /\ pm IN S UNION Nl UNION Nh /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) pm pp)
     ==> pm IN topspace top DIFF S /\
         Cm UNION Nl SUBSET connected_component_of (subtopology top (topspace top DIFF S)) pm /\
         DISJOINT (connected_component_of (subtopology top (topspace top DIFF S)) pm)
                  (Cp UNION Nh)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Nl SUBSET topspace top /\ Nh SUBSET topspace top /\
                Cm SUBSET topspace top /\ Cp SUBSET topspace (top:A topology)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in (subtopology top (topspace top DIFF S)) (Nh UNION Cp:A->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (connected_component_of (subtopology top (topspace top DIFF S)) pm)
             (Cp UNION Nh:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [IN] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `~(connected_component_of (subtopology top (topspace top DIFF S)) (pm:A) pp)` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN EXISTS_TAC `q:A` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[connected_component_of] THEN EXISTS_TAC `Nh UNION Cp:A->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pm:A) IN topspace top DIFF S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(pm:A) IN connected_component_of (subtopology top (topspace top DIFF S)) pm`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [IN] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pm:A) IN Nl` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* A level sphere of e misses the images of the slabs below and above it.  *)

let APX_LEVEL_SPHERE_DISJOINT = prove
 (`!top atlas (e:real^3->A) eps c a b.
     mfd_param top atlas (rfs_neck_dom eps) e /\
     sphere(vec 0,exp(c / sqrt(&2))) SUBSET rfs_neck_dom eps /\
     apx_slab a b SUBSET rfs_neck_dom eps /\ (b <= c \/ c <= a)
     ==> DISJOINT (IMAGE e (sphere(vec 0,exp(c / sqrt(&2))))) (IMAGE e (apx_slab a b))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `y1:real^3 = y2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y2:real^3) IN sphere(vec 0,exp(c / sqrt(&2)))` THEN
  UNDISCH_TAC `(y2:real^3) IN apx_slab a b` THEN
  REWRITE_TAC[APX_SPHERE_LEVEL; APX_SLAB_SVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* The sides of a level sphere c of e that is a section u of ez, given that *)
(* e is in ez from the level c - 2 on and the top of e meets the part of ez *)
(* above the section.                                                        *)

let APX_SIGMA_SIDES = prove
 (`!top atlas (e:real^3->A) (ez:real^3->A) (u:real^3->real) eps c.
     smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\ &0 < eps /\
     mfd_param top atlas (rfs_neck_dom eps) e /\ mfd_param top atlas (rfs_neck_dom eps) ez /\
     --inv eps + &2 <= c /\ c + &2 <= inv eps /\
     (\w. lift(u w)) continuous_on sphere(vec 0,&1) /\
     (!w. w IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
     IMAGE e (sphere(vec 0,exp(c / sqrt(&2)))) = IMAGE (\w. ez(u w % w)) (sphere(vec 0,&1)) /\
     IMAGE e (apx_slab (c - &2) (inv eps)) SUBSET IMAGE ez (rfs_neck_dom eps) /\
     ~(DISJOINT (IMAGE e (apx_slab c (inv eps)))
                (IMAGE ez {v | ~(v = vec 0) /\ u(inv(norm v) % v) < norm v /\
                               norm v < exp(inv eps / sqrt(&2))}))
     ==> ?pm. pm IN topspace top DIFF IMAGE e (sphere(vec 0,exp(c / sqrt(&2)))) /\
              IMAGE e (apx_slab (--inv eps) c) UNION
              IMAGE ez {v | ~(v = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm v /\
                            norm v < u(inv(norm v) % v)}
              SUBSET connected_component_of
                       (subtopology top (topspace top DIFF
                                         IMAGE e (sphere(vec 0,exp(c / sqrt(&2)))))) pm /\
              DISJOINT (connected_component_of
                          (subtopology top (topspace top DIFF
                                            IMAGE e (sphere(vec 0,exp(c / sqrt(&2)))))) pm)
                       (IMAGE e (apx_slab c (inv eps)) UNION
                        IMAGE ez {v | ~(v = vec 0) /\ u(inv(norm v) % v) < norm v /\
                                      norm v < exp(inv eps / sqrt(&2))})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `IMAGE (e:real^3->A) (sphere(vec 0,exp(c / sqrt(&2))))`)) THEN
  STRIP_ASSUME_TAC APX_LOG_43 THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  (* the separation by the level sphere *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `eps:real`; `c:real`] APX_LEVEL_SPHERE_SEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
  (* the split of the new neck along the section *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ez:real^3->A`;
                 `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`; `u:real^3->real`]
                APX_SECTION_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the old neck below and above the level *)
  SUBGOAL_THEN `apx_slab (--inv eps) c SUBSET rfs_neck_dom eps /\
                apx_slab c (inv eps) SUBSET rfs_neck_dom eps /\
                sphere(vec 0:real^3,exp(c / sqrt(&2))) SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[APX_SPHERE_LEVEL; SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (IMAGE (e:real^3->A) (apx_slab (--inv eps) c)) /\
                connected_in top (IMAGE (e:real^3->A) (apx_slab c (inv eps)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (e:real^3->A) (sphere(vec 0,exp(c / sqrt(&2)))))
             (IMAGE e (apx_slab (--inv eps) c)) /\
    DISJOINT (IMAGE (e:real^3->A) (sphere(vec 0,exp(c / sqrt(&2)))))
             (IMAGE e (apx_slab c (inv eps)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_LEVEL_SPHERE_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `eps:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* the two axis points *)
  SUBGOAL_THEN `exp(c / sqrt(&2)) % (&3 / &4 % basis 1:real^3) IN apx_slab (--inv eps) c /\
                exp(c / sqrt(&2)) % (&3 / &4 % basis 1:real^3) IN apx_slab (c - &2) (inv eps) /\
                exp(c / sqrt(&2)) % (&4 / &3 % basis 1:real^3) IN apx_slab c (inv eps)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_SVAL] THEN
    MP_TAC(SPECL [`c:real`; `&3 / &4`] APX_SVAL_SCALED_BASIS) THEN
    MP_TAC(SPECL [`c:real`; `&4 / &3`] APX_SVAL_SCALED_BASIS) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &3 / &4`; REAL_ARITH `&0 < &4 / &3`] THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A)(exp(c / sqrt(&2)) % (&3 / &4 % basis 1)) IN
                IMAGE ez (rfs_neck_dom eps)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `c - &2`)) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~(DISJOINT (IMAGE (ez:real^3->A) {v | ~(v = vec 0) /\ u(inv(norm v) % v) < norm v /\
                                         norm v < exp(inv eps / sqrt(&2))})
               (IMAGE (e:real^3->A) (apx_slab c (inv eps))))`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(e:real^3->A)(exp(c / sqrt(&2)) % (&3 / &4 % basis 1))` THEN
  MATCH_MP_TAC APX_SIDES_ABSTRACT THEN
  EXISTS_TAC `(e:real^3->A)(exp(c / sqrt(&2)) % (&4 / &3 % basis 1))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* A.17, part 5.  Continuation downwards along a ray: a real                 *)
(* function whose derivative is within kappa of +/- rho on an open set S,   *)
(* which is at most f(t0) on S left of t0 and can only leave S through the   *)
(* ends of the domain, stays in S all the way down, increasing at rate rho.  *)
(* For the ray of the new neck through a point of Sigma this puts the part  *)
(* of the new neck below Sigma inside the old neck.                          *)
(* ------------------------------------------------------------------------- *)

let APX_1D_DOWN_CONT = prove
 (`!f f' S a t0 c rho kappa.
     a < t0 /\ &0 <= kappa /\ kappa < rho /\ &0 < c /\ t0 IN S /\ f t0 < c /\
     (!t. t IN S ==> ?d. &0 < d /\ !t'. abs(t' - t) < d ==> t' IN S) /\
     (!t. t IN S ==> (f has_real_derivative f' t) (atreal t) /\
                     (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)) /\
     (!t. t IN S /\ a < t /\ t < t0 ==> f t <= f t0) /\
     (!t m. a < t /\ t < t0 /\ ~(t IN S) /\ m < c
            ==> ?d. &0 < d /\ !t'. t' IN S /\ abs(t' - t) < d ==> m < abs(f t')) /\
     --(c / &2) < f t0 - (rho + kappa) * (t0 - a)
     ==> !t. a < t /\ t <= t0
             ==> t IN S /\ f t0 - (rho + kappa) * (t0 - t) <= f t /\
                 f t <= f t0 - (rho - kappa) * (t0 - t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "open") (CONJUNCTS_THEN2 (LABEL_TAC "der")
    (CONJUNCTS_THEN2 (LABEL_TAC "side") (CONJUNCTS_THEN2 (LABEL_TAC "exit")
     ASSUME_TAC)))))))))) THEN
  USE_THEN "open" (fun th -> MP_TAC(MP (SPEC `t0:real` th) (ASSUME `(t0:real) IN S`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  (* on an interval (p,t0] inside S, f is increasing with the MVT bounds *)
  SUBGOAL_THEN
   `!p. a <= p /\ p < t0 /\ (!t. p < t /\ t <= t0 ==> t IN S)
        ==> (!x y. p < x /\ x < y /\ y < t0 + d0 ==> (f:real->real) x < f y) /\
            (!t. p < t /\ t < t0
                 ==> (rho - kappa) * (t0 - t) <= f t0 - f t /\
                     f t0 - f t <= (rho + kappa) * (t0 - t))`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `p:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!t. p < t /\ t < t0 + d0 ==> t IN S` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t <= t0` THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun u -> u = `p:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun u -> u = `d0:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. p < t /\ t < t0 + d0
          ==> ((f:real->real) has_real_derivative f' t) (atreal t) /\
              (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "der" MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `p:real`; `t0 + d0`; `rho:real`;
                   `kappa:real`] APX_1D_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [ALL_TAC;
      DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      SUBGOAL_THEN `(f:real->real) t0 < f((p + t0) / &2)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "side" (MP_TAC o SPEC `(p + t0) / &2`) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (find_term (fun u -> u = `p:real`)) (concl th) &&
            not (can (find_term (fun u -> u = `d0:real`)) (concl th)) &&
            is_forall (concl th))) THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC]] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `p:real`; `t0 + d0`; `rho:real`;
                   `kappa:real`] APX_1D_INCR_DERIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC APX_1D_MVT_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`f':real->real`; `p:real`; `t0 + d0`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (a,t0] lies in S *)
  SUBGOAL_THEN `!t. a < t /\ t <= t0 ==> t IN S` ASSUME_TAC THENL
   [X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPEC `{t:real | t1 <= t /\ t <= t0 /\ ~(t IN S)}` SUP) THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
       [EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        EXISTS_TAC `t0:real` THEN SIMP_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `p = sup {t:real | t1 <= t /\ t <= t0 /\ ~(t IN S)}` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pub" o REWRITE_RULE[IN_ELIM_THM])
                               (LABEL_TAC "plub" o REWRITE_RULE[IN_ELIM_THM])) THEN
    SUBGOAL_THEN `t1 <= p /\ p <= t0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        USE_THEN "plub" MATCH_MP_TAC THEN SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real) IN S)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "open" (fun th -> MP_TAC(MP (SPEC `p:real` th) (ASSUME `(p:real) IN S`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "plub" (MP_TAC o SPEC `p - d / &2`) THEN ANTS_TAC THENL
       [X_GEN_TAC `z:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `z <= p:real` ASSUME_TAC THENL
         [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `~(p - d / &2 < z) ==> z <= p - d / &2`) THEN DISCH_TAC THEN
        UNDISCH_TAC `~((z:real) IN S)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!t. p < t /\ t <= t0 ==> t IN S` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_TAC THEN SUBGOAL_THEN `t <= p:real` MP_TAC THENL
       [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `p < t0` ASSUME_TAC THENL
     [ASM_CASES_TAC `p:real = t0` THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    USE_THEN "inc" (MP_TAC o SPEC `p:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC APX_1D_BAD_LEFT THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `{t:real | p < t /\ t < t0}`; `p:real`; `t0:real`;
                          `c:real`; `(p + t0) / &2`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term (fun u -> u = `rho - kappa`)) (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(rho + kappa) * (t0 - t) <= (rho + kappa) * (t0 - a) /\
                    &0 <= (rho - kappa) * (t0 - t)` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `m:real` THEN DISCH_TAC THEN
      USE_THEN "exit" (MP_TAC o SPECL [`p:real`; `m:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t':real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `p:real`)) (concl th) &&
        not (can (find_term (fun u -> u = `d0:real`)) (concl th)) &&
        is_forall (concl th) &&
        can (find_term (fun u -> u = `(S:real->bool)`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "inc" (MP_TAC o SPEC `a:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = t0` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    can (find_term (fun u -> u = `rho - kappa`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The ray of ez in direction om, from a point at level t0 in e, stays in e *)
(* all the way down when its e-levels below t0 are at most that at t0.      *)

let APX_RAY_DOWN_IN = prove
 (`!top atlas (e:real^3->A) ez (ei:A->real^3) eps rho kappa (om:real^3) t0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
     mfd_param top atlas (rfs_neck_dom eps) e /\
     mfd_param top atlas (rfs_neck_dom eps) ez /\
     (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\ norm om = &1 /\
     &0 <= kappa /\ kappa < rho /\
     (!v. v IN rfs_neck_dom eps /\ ez v IN IMAGE e (rfs_neck_dom eps)
          ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                   !k. abs(sqrt(&2) * (ei(ez v) dot frechet_derivative (ei o ez) (at v) k) /
                           (ei(ez v) dot ei(ez v)) -
                           sg * rho * sqrt(&2) * (v dot k) / (v dot v))
                       <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
     --inv eps < t0 /\ t0 < inv eps /\
     ez(exp(t0 / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps) /\
     (!t. --inv eps < t /\ t < t0 /\
          ez(exp(t / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps)
          ==> apx_sval(ei(ez(exp(t / sqrt(&2)) % om))) <=
              apx_sval(ei(ez(exp(t0 / sqrt(&2)) % om)))) /\
     --(inv eps / &2) <
     apx_sval(ei(ez(exp(t0 / sqrt(&2)) % om))) - (rho + kappa) * (t0 + inv eps)
     ==> !t. --inv eps < t /\ t <= t0
             ==> ez(exp(t / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps) /\
                 apx_sval(ei(ez(exp(t0 / sqrt(&2)) % om))) - (rho + kappa) * (t0 - t) <=
                 apx_sval(ei(ez(exp(t / sqrt(&2)) % om)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "align")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "side")
     ASSUME_TAC)))))))))))))) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `ez:real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`\t. apx_sval((ei:A->real^3)((ez:real^3->A)(exp(t / sqrt(&2)) % om)))`;
                 `\t. sqrt(&2) * ((ei:A->real^3)((ez:real^3->A)(exp(t / sqrt(&2)) % om)) dot
                         frechet_derivative (ei o ez) (at (exp(t / sqrt(&2)) % om))
                           (inv(sqrt(&2)) % exp(t / sqrt(&2)) % om)) /
                      (ei(ez(exp(t / sqrt(&2)) % om)) dot ei(ez(exp(t / sqrt(&2)) % om)))`;
                 `{t | --inv eps < t /\ t < inv eps /\
                       (ez:real^3->A)(exp(t / sqrt(&2)) % om) IN
                       IMAGE (e:real^3->A) (rfs_neck_dom eps)}`;
                 `--inv eps`; `t0:real`; `inv eps`; `rho:real`; `kappa:real`]
                APX_1D_DOWN_CONT) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "tr" (MP_TAC o SPEC `exp(t0 / sqrt(&2)) % (om:real^3)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[APX_RAY_IN_DOM]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP APX_SVAL_NECK_DOM o CONJUNCT1) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`{v:real^3 | v IN rfs_neck_dom eps /\
                        (ez:real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}`;
                     `om:real^3`; `t:real`] APX_RAY_OPEN_PRE) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[APX_RAY_IN_DOM] THEN
      REWRITE_TAC[CONJ_ASSOC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `exp(t / sqrt(&2)) % (om:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [ASM_SIMP_TAC[APX_RAY_IN_DOM]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(ei:A->real^3)((ez:real^3->A)(exp(t / sqrt(&2)) % om)) IN rfs_neck_dom eps /\
        (e:real^3->A)(ei(ez(exp(t / sqrt(&2)) % om))) = ez(exp(t / sqrt(&2)) % om)`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "tr" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`(ei:A->real^3) o (ez:real^3->A)`; `om:real^3`; `t:real`]
                      APX_RAY_SVAL_DERIV) THEN
        REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
            EXISTS_TAC `{v:real^3 | v IN rfs_neck_dom eps /\
                          (ez:real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}` THEN
            ASM_REWRITE_TAC[IN_ELIM_THM];
            ASM_MESON_TAC[APX_SVAL_NECK_DOM]];
          REWRITE_TAC[]];
        USE_THEN "align" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPEC `inv(sqrt(&2)) % exp(t / sqrt(&2)) % (om:real^3)`))) THEN
        MP_TAC(SPEC `exp(t / sqrt(&2)) % (om:real^3)` APX_RAY_UNIT_FACTS) THEN
        ASM_SIMP_TAC[APX_RAY_NONZERO; SQRT_1; REAL_MUL_RID] THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "side" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `m:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `t < inv eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `e:real^3->A`; `ez:real^3->A`; `ei:A->real^3`; `eps:real`;
                     `om:real^3`] APX_RAY_EXIT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        can (find_term (fun u -> u = `t:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `--(inv eps / &2) <
      apx_sval((ei:A->real^3)((ez:real^3->A)(exp(t0 / sqrt(&2)) % om))) -
      (rho + kappa) * (t0 + inv eps)` THEN
    REWRITE_TAC[REAL_ARITH `t0 - --i = t0 + i`];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A.18, part 1.  The balanced distance from the centre of the               *)
(* old neck to the frontier point z, from N2 at 1/200 and a point of the top *)
(* end of the old neck within h/10 of z.                                      *)
(* ------------------------------------------------------------------------- *)

let APX_FRONTIER_DIST = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z.
     apx_ch_ctx top atlas g eps /\ rfs_neck (top,atlas) g eps x e /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> mfd_joinable (top,atlas) x z /\
         &99 / &100 * inv(sqrt(mfd_scalar atlas g x)) * inv eps
         <= mfd_dist (top,atlas) g x z /\
         mfd_dist (top,atlas) g x z
         <= &101 / &100 * inv(sqrt(mfd_scalar atlas g x)) * inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (e:real^3->A) x0 = x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\ &0 < inv eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `h / &10`] APX_FRONTIER_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(y:real^3)) < inv eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `x0:real^3`; `y:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &200`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) (x:A) z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(e:real^3->A) y` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `z:A`; `(e:real^3->A) y`] MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `x0:real^3`]
                  APX_FRONTIER_LOWER) THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `x:A`; `z:A`] MFD_JOINABLE_SYM) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x ((e:real^3->A) y) +
              mfd_dist (top,atlas) g (e y) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `z:A`; `(e:real^3->A) y`] MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `(e:real^3->A) y`; `z:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `h * abs(apx_sval(y:real^3)) <= h * inv eps /\
                h * sqrt(&2) * pi <= h * (&24 / &5) /\ h * &1024 <= h * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; APX_SQRT2_PI];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_SVAL_LT_NORM = prove
 (`!v w:real^3. ~(v = vec 0) /\ ~(w = vec 0)
                ==> (apx_sval v < apx_sval w <=> norm v < norm w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN MATCH_MP_TAC LOG_MONO_LT THEN
  ASM_REWRITE_TAC[NORM_POS_LT]);;

(* The set-up of A.18 for the pair (e, ez'): Sigma, its orientation, Claim A *)
(* for ez', and the component K of the points just below Sigma.             *)

let APX_A18_SETUP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> ?ez' (u:real^3->real) pm.
           (ez' = ez \/ ez' = apx_rev ez) /\ rfs_neck (top,atlas) g eps z ez' /\
           (\w. lift(u w)) continuous_on sphere(vec 0,&1) /\
           (!w. w IN sphere(vec 0,&1)
                ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
           IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))) =
           IMAGE (\w. ez'(u w % w)) (sphere(vec 0,&1)) /\
           (!w. w IN sphere(vec 0,&1)
                ==> --(&2 / &5 * inv eps) <= apx_sval(u w % w) /\
                    apx_sval(u w % w) <= --(&9 / &25 * inv eps)) /\
           IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
           IMAGE ez' (rfs_neck_dom eps) /\
           pm IN topspace top DIFF
                 IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))) /\
           IMAGE e (apx_slab (--inv eps) (&5 / &8 * inv eps)) UNION
           IMAGE ez' {v | ~(v = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm v /\
                          norm v < u(inv(norm v) % v)}
           SUBSET connected_component_of
                    (subtopology top (topspace top DIFF
                       IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))))) pm /\
           DISJOINT (connected_component_of
                       (subtopology top (topspace top DIFF
                          IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))))) pm)
                    (IMAGE e (apx_slab (&5 / &8 * inv eps) (inv eps)) UNION
                     IMAGE ez' {v | ~(v = vec 0) /\ u(inv(norm v) % v) < norm v /\
                                    norm v < exp(inv eps / sqrt(&2))})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1024 <= inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN
    MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`]
                APX_FRONTIER_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (X_CHOOSE_THEN `u:real^3->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z ez'` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN (fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_disj(concl th) && can (find_term (fun t -> t = `ez':real^3->A`)) (concl th))) THEN
    ASM_SIMP_TAC[APX_REV_NECK];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez':real^3->A`]
                APX_FRONTIER_QUARTER_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (ez':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `c1 = &5 / &8 * inv eps` THEN
  (* a point near the top of e lies above the section *)
  MP_TAC(SPECL [`inv eps - &1 / &2`; `&1`] APX_SVAL_SCALED_BASIS) THEN
  REWRITE_TAC[REAL_LT_01; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ABBREV_TAC `y1 = exp((inv eps - &1 / &2) / sqrt(&2)) % (&1 % basis 1:real^3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y1:real^3) IN apx_slab c1 (inv eps) /\
                y1 IN apx_slab (inv(&2 * eps)) (inv eps) /\ y1 IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL; APX_SLAB_NECK_DOM] THEN EXPAND_TAC "c1" THEN
    REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?v1. v1 IN rfs_neck_dom eps /\ (ez':real^3->A) v1 = (e:real^3->A) y1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
                 IMAGE ez' (rfs_neck_dom eps)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `y1:real^3`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez':real^3->A`; `y1:real^3`;
                 `v1:real^3`] APX_FRONTIER_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv eps - &1 / &2` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(v1:real^3 = vec 0) /\ abs(apx_sval v1) < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
               APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(norm v1) % (v1:real^3)` o CONJUNCT1) THEN
  SUBGOAL_THEN `inv(norm v1) % (v1:real^3) IN sphere(vec 0,&1)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^3->real)(inv(norm v1) % v1) < norm(v1:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`(u:real^3->real)(inv(norm v1) % v1) % inv(norm v1) % (v1:real^3)`;
                  `v1:real^3`] APX_SVAL_LT_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
      ASM_REWRITE_TAC[NORM_0] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `inv(norm v1) % (v1:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
      MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `inv(norm v1) % (v1:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `&9 / &25 * inv eps`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v1:real^3) < exp(inv eps / sqrt(&2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(v1:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM; annulus; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `ez':real^3->A`; `u:real^3->real`; `eps:real`; `c1:real`]
                APX_SIGMA_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "c1" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "c1" THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC APX_SLAB_SUBSET THEN EXPAND_TAC "c1" THEN
      REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A) y1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `v1:real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pm:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ez':real^3->A`; `u:real^3->real`; `pm:A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A.18, part 2.  The part of the new neck below the section                 *)
(* Sigma lies in the old neck, at old levels above -1/(2 eps): ray           *)
(* continuation from Sigma, with rho = sqrt(R(x)/R(z)) in [1/2, 3/2] and     *)
(* kappa = 7/2560, the side condition from the component K.                  *)
(* ------------------------------------------------------------------------- *)

let APX_RAY_BASICS = prove
 (`!(om:real^3) t.
     norm om = &1
     ==> ~(exp(t / sqrt(&2)) % om = vec 0) /\
         norm(exp(t / sqrt(&2)) % om) = exp(t / sqrt(&2)) /\
         inv(norm(exp(t / sqrt(&2)) % om)) % (exp(t / sqrt(&2)) % om) = om /\
         apx_sval(exp(t / sqrt(&2)) % om) = t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[APX_RAY_NONZERO; APX_RAY_SVAL] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_EXP; REAL_MUL_RID; VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_EXP_NZ; VECTOR_MUL_LID]);;

let APX_EXP_HALF_MONO_LT = prove
 (`!a b. exp(a / sqrt(&2)) < exp(b / sqrt(&2)) <=> a < b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  MATCH_MP_TAC REAL_LT_DIV2_EQ THEN SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]);;

let APX_SECTION_EXP_LEVEL = prove
 (`!(u:real^3->real) om.
     norm om = &1 /\ &0 < u om
     ==> exp(apx_sval(u om % om) / sqrt(&2)) = u om /\
         exp(apx_sval(u om % om) / sqrt(&2)) % om = u om % om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(apx_sval((u:real^3->real) om % om) / sqrt(&2)) = u om` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[apx_sval; NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * l) / s = l`; EXP_LOG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let APX_A18_LOW = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) (ei:A->real^3) z (ez':real^3->A)
    (u:real^3->real) K.
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez' /\
     (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
     (!w. w IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
     IMAGE (\w. ez'(u w % w)) (sphere(vec 0,&1)) =
     IMAGE e (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))) /\
     (!w. w IN sphere(vec 0,&1)
          ==> --(&2 / &5 * inv eps) <= apx_sval(u w % w) /\
              apx_sval(u w % w) <= --(&9 / &25 * inv eps)) /\
     IMAGE ez' {v | ~(v = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm v /\
                    norm v < u(inv(norm v) % v)} SUBSET K /\
     DISJOINT K (IMAGE e (apx_slab (&5 / &8 * inv eps) (inv eps)))
     ==> !v. v IN rfs_neck_dom eps /\ norm v < u(inv(norm v) % v)
             ==> ez' v IN IMAGE e (rfs_neck_dom eps) /\
                 --(inv eps / &2) < apx_sval(ei(ez' v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1024 <= inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN
    MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (ez':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `ez':real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "tr"))) THEN
  MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
               APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  DISCH_THEN(LABEL_TAC "bas" o CONJUNCT1) THEN
  (* every section point is on Sigma, at old level 5/(8 eps) *)
  SUBGOAL_THEN
   `!w. w IN sphere(vec 0,&1)
        ==> (ez':real^3->A)((u:real^3->real) w % w) IN IMAGE e (rfs_neck_dom eps) /\
            apx_sval((ei:A->real^3)(ez'(u w % w))) = &5 / &8 * inv eps`
  (LABEL_TAC "sig") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ez':real^3->A)((u:real^3->real) w % w) IN
                  IMAGE (e:real^3->A) (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2))))` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (lhs(concl th)))) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
      REWRITE_RULE[IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM]) THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* rho *)
  ABBREV_TAC `rho = sqrt(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g z)` THEN
  SUBGOAL_THEN `&1 / &2 <= rho /\ rho <= &3 / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `basis 1:real^3 IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    USE_THEN "bas" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `basis 1:real^3 IN sphere(vec 0,&1)`))) THEN
    USE_THEN "sig" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `basis 1:real^3 IN sphere(vec 0,&1)`))) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[apx_ch_more] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_more")) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z:A`; `ez':real^3->A`;
                               `(u:real^3->real)(basis 1) % basis 1:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0) /\ abs(apx_sval v) < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(om:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  USE_THEN "bas" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (ASSUME `(om:real^3) IN sphere(vec 0,&1)`))) THEN
  USE_THEN "sig" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (ASSUME `(om:real^3) IN sphere(vec 0,&1)`))) THEN
  SUBGOAL_THEN `&0 < (u:real^3->real) om` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(om:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
    MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`u:real^3->real`; `om:real^3`] APX_SECTION_EXP_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `t0 = apx_sval((u:real^3->real) om % om)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(&2 / &5 * inv eps) <= t0 /\ t0 <= --(&9 / &25 * inv eps)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(v:real^3) < t0` ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN
    MP_TAC(SPECL [`v:real^3`; `(u:real^3->real) om % om`] APX_SVAL_LT_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
      ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the ray lemma *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `ez':real^3->A`; `ei:A->real^3`; `eps:real`; `rho:real`; `&7 / &2560`;
                 `om:real^3`; `t0:real`] APX_RAY_DOWN_IN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[apx_ch_more] o
        check (fun th -> can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "apx_ch_more")) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z:A`; `ez':real^3->A`;
                                 `ei:A->real^3`; `w:real^3`]) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`om:real^3`; `t:real`] APX_RAY_BASICS) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(ez':real^3->A)(exp(t / sqrt(&2)) % om) IN K` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> t = `K:A->bool`)) (concl th) &&
          not (is_neg (concl th)) &&
          can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `exp(t0 / sqrt(&2)) = (u:real^3->real) om` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[APX_EXP_HALF_MONO_LT];
        ALL_TAC] THEN
      USE_THEN "tr" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[APX_RAY_IN_DOM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      MATCH_MP_TAC(REAL_ARITH `~(c < s) ==> s <= c`) THEN DISCH_TAC THEN
      UNDISCH_TAC `DISJOINT K (IMAGE (e:real^3->A) (apx_slab (&5 / &8 * inv eps) (inv eps)))` THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(ez':real^3->A)(exp(t / sqrt(&2)) % om)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(ei:A->real^3)((ez':real^3->A)(exp(t / sqrt(&2)) % om))` THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
      MP_TAC(SPECL [`eps:real`;
                    `(ei:A->real^3)((ez':real^3->A)(exp(t / sqrt(&2)) % om))`]
                   APX_SVAL_NECK_DOM) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(rho + &7 / &2560) * (t0 + inv eps) <=
                    (&3 / &2 + &7 / &2560) * (t0 + inv eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `apx_sval(v:real^3)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(rho + &7 / &2560) * (t0 - apx_sval(v:real^3)) <=
                (&3 / &2 + &7 / &2560) * (t0 + inv eps)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A.18, part 3.  The pair lemma: the oriented new neck ez'                  *)
(* satisfies the chain clauses (1) and (2) with the old neck e, and the       *)
(* component K of a point below Sigma (Sigma in the positive quarter of e)   *)
(* absorbs every connected set off Sigma meeting it, contains the negative   *)
(* quarter of e, misses the positive quarter of ez' and meets ez' only in e. *)
(* ------------------------------------------------------------------------- *)

let APX_CC_ABSORB = prove
 (`!top S (p:A) C.
     connected_in top C /\ C SUBSET topspace top DIFF S /\
     ~(DISJOINT C (connected_component_of (subtopology top (topspace top DIFF S)) p))
     ==> C SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top (topspace top DIFF S)) p =
    connected_component_of (subtopology top (topspace top DIFF S)) (q:A)`
  SUBST1_TAC THENL
   [UNDISCH_TAC
     `(q:A) IN connected_component_of (subtopology top (topspace top DIFF S)) p` THEN
    GEN_REWRITE_TAC LAND_CONV [IN] THEN SIMP_TAC[CONNECTED_COMPONENT_OF_EQUIV];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]);;

(* Comparing a point of the neck domain with the section in its direction. *)

let APX_SECTION_CMP = prove
 (`!(u:real^3->real) eps v.
     (!w. w IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u w /\ u w < exp(inv eps / sqrt(&2))) /\
     v IN rfs_neck_dom eps
     ==> inv(norm v) % v IN sphere(vec 0,&1) /\
         u(inv(norm v) % v) % inv(norm v) % v IN rfs_neck_dom eps /\
         (norm v < u(inv(norm v) % v) <=>
          apx_sval v < apx_sval(u(inv(norm v) % v) % inv(norm v) % v)) /\
         (u(inv(norm v) % v) < norm v <=>
          apx_sval(u(inv(norm v) % v) % inv(norm v) % v) < apx_sval v) /\
         (norm v = u(inv(norm v) % v) ==> v = u(inv(norm v) % v) % inv(norm v) % v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(om:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
               APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  DISCH_THEN(MP_TAC o SPEC `om:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~((u:real^3->real) om % om = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_LT_NORM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3) = norm v % om` SUBST1_TAC THENL
   [UNDISCH_TAC `inv(norm v) % (v:real^3) = om` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID; ASSUME `~(v:real^3 = vec 0)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Images of disjoint slabs under a parametrization of the neck domain. *)

let APX_IMAGE_SLABS_DISJOINT = prove
 (`!top atlas (e:real^3->A) eps a b c d.
     mfd_param top atlas (rfs_neck_dom eps) e /\
     apx_slab a b SUBSET rfs_neck_dom eps /\ apx_slab c d SUBSET rfs_neck_dom eps /\
     b <= c
     ==> DISJOINT (IMAGE e (apx_slab a b)) (IMAGE e (apx_slab c d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `y1:real^3 = y2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y2:real^3) IN apx_slab a b` THEN
  UNDISCH_TAC `(y2:real^3) IN apx_slab c d` THEN
  REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

let APX_A18_PAIR = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> ?ez' S K.
           (ez' = ez \/ ez' = apx_rev ez) /\ rfs_neck (top,atlas) g eps z ez' /\
           IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) UNION
           IMAGE ez' (apx_slab (--inv eps) (--inv(&2 * eps)))
           SUBSET IMAGE e (rfs_neck_dom eps) INTER IMAGE ez' (rfs_neck_dom eps) /\
           IMAGE e (rfs_neck_dom eps) INTER IMAGE ez' (rfs_neck_dom eps)
           SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                  IMAGE ez' (apx_slab (--inv eps) (inv(&2 * eps))) /\
           DISJOINT (IMAGE ez' (rfs_neck_dom eps))
                    (IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
           DISJOINT (IMAGE e (rfs_neck_dom eps))
                    (IMAGE ez' (apx_slab (inv(&2 * eps)) (inv eps))) /\
           S SUBSET IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) /\
           K SUBSET topspace top DIFF S /\
           (!C. connected_in top C /\ C SUBSET topspace top DIFF S /\ ~(DISJOINT C K)
                ==> C SUBSET K) /\
           IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET K /\
           DISJOINT K (IMAGE ez' (apx_slab (inv(&2 * eps)) (inv eps))) /\
           K INTER IMAGE ez' (rfs_neck_dom eps) SUBSET IMAGE e (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1024 <= inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN
    MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`] APX_A18_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (X_CHOOSE_THEN `u:real^3->real`
    (X_CHOOSE_THEN `pm:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
     STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (ez':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  (* the part of ez' below the section *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `ei:A->real^3`; `z:A`; `ez':real^3->A`;
                 `u:real^3->real`;
                 `connected_component_of
                    (subtopology top (topspace top DIFF
                       IMAGE (e:real^3->A)
                         (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2)))))) pm`]
                APX_A18_LOW) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `pm:A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      SET_TAC[];
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `pm:A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      SET_TAC[]];
    DISCH_THEN(LABEL_TAC "low")] THEN
  (* the split of ez' along the section *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ez':real^3->A`;
                 `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`; `u:real^3->real`]
                APX_SECTION_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
               APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* abbreviations *)
  ABBREV_TAC `Sg = IMAGE (e:real^3->A) (sphere(vec 0,exp((&5 / &8 * inv eps) / sqrt(&2))))` THEN
  ABBREV_TAC `Kc = connected_component_of (subtopology top (topspace top DIFF Sg)) (pm:A)` THEN
  ABBREV_TAC `Vl = {v:real^3 | ~(v = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm v /\
                               norm v < (u:real^3->real)(inv(norm v) % v)}` THEN
  ABBREV_TAC `Vh = {v:real^3 | ~(v = vec 0) /\ (u:real^3->real)(inv(norm v) % v) < norm v /\
                               norm v < exp(inv eps / sqrt(&2))}` THEN
  (* membership in Vl and Vh *)
  SUBGOAL_THEN
   `!v:real^3. v IN rfs_neck_dom eps
               ==> (v IN Vl <=> norm v < (u:real^3->real)(inv(norm v) % v)) /\
                   (v IN Vh <=> u(inv(norm v) % v) < norm v)`
  (LABEL_TAC "mem") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(v:real^3 = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm v /\
                  norm v < exp(inv eps / sqrt(&2))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
      UNDISCH_TAC `(v:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM; annulus; IN_ELIM_THM];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Vl"; "Vh"] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* points of the old neck above the section *)
  SUBGOAL_THEN
   `!v. v IN rfs_neck_dom eps /\ (u:real^3->real)(inv(norm v) % v) < norm v /\
        (ez':real^3->A) v IN IMAGE e (rfs_neck_dom eps)
        ==> &5 / &8 * inv eps < apx_sval((ei:A->real^3)(ez' v)) /\
            abs(apx_sval v) <= &2 / &5 * inv eps`
  (LABEL_TAC "high") THENL
   [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
      check (fun th -> concl th = `(ez':real^3->A) v IN IMAGE e (rfs_neck_dom eps)`)) THEN
    SUBGOAL_THEN `(ei:A->real^3)((ez':real^3->A) v) = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(ez':real^3->A) v IN IMAGE (ez':real^3->A) Vh` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "mem" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN `&5 / &8 * inv eps < apx_sval(y:real^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(s < c) /\ ~(s = c) ==> c < s`) THEN CONJ_TAC THEN
      DISCH_TAC THENL
       [SUBGOAL_THEN `(e:real^3->A) y IN IMAGE e (apx_slab (--inv eps) (&5 / &8 * inv eps))`
        ASSUME_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
          MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT Kc (IMAGE (e:real^3->A) (apx_slab (&5 / &8 * inv eps) (inv eps)) UNION
                                  IMAGE (ez':real^3->A) Vh)` THEN
        UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&5 / &8 * inv eps)) UNION
                     IMAGE (ez':real^3->A) Vl SUBSET Kc` THEN
        UNDISCH_TAC `(ez':real^3->A) v IN IMAGE (ez':real^3->A) Vh` THEN
        UNDISCH_TAC `(e:real^3->A) y IN IMAGE e (apx_slab (--inv eps) (&5 / &8 * inv eps))` THEN
        UNDISCH_TAC `(ez':real^3->A) v = (e:real^3->A) y` THEN
        SET_TAC[];
        SUBGOAL_THEN `(e:real^3->A) y IN Sg` ASSUME_TAC THENL
         [EXPAND_TAC "Sg" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[APX_SPHERE_LEVEL; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[APX_SVAL_NECK_DOM];
          ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT Sg (IMAGE (ez':real^3->A) Vh)` THEN
        UNDISCH_TAC `(ez':real^3->A) v IN IMAGE (ez':real^3->A) Vh` THEN
        UNDISCH_TAC `(e:real^3->A) y IN Sg` THEN
        UNDISCH_TAC `(ez':real^3->A) v = (e:real^3->A) y` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez':real^3->A`; `y:real^3`;
                   `v:real^3`] APX_FRONTIER_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&5 / &8 * inv eps` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* clause (1), first part *)
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
    IMAGE (ez':real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps)))
    SUBSET IMAGE e (rfs_neck_dom eps) INTER IMAGE ez' (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` THEN
        UNDISCH_TAC `apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET rfs_neck_dom eps` THEN
        SET_TAC[]; ALL_TAC] THEN
      USE_THEN "low" (MP_TAC o SPEC `v:real^3`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`u:real^3->real`; `eps:real`; `v:real^3`] APX_SECTION_CMP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `inv(norm v) % (v:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `&9 / &25 * inv eps`)) (concl th))) THEN
      UNDISCH_TAC `(v:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* clause (1), second part *)
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) (rfs_neck_dom eps) INTER IMAGE (ez':real^3->A) (rfs_neck_dom eps)
    SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
           IMAGE ez' (apx_slab (--inv eps) (inv(&2 * eps)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE])
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE])) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `q:A = (e:real^3->A) y`)) THEN
    SUBGOAL_THEN `(ez':real^3->A) v IN IMAGE e (rfs_neck_dom eps)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ei:A->real^3)((ez':real^3->A) v) = y` ASSUME_TAC THENL
     [FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
        concl th = `(e:real^3->A) y = (ez':real^3->A) v`)) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`u:real^3->real`; `eps:real`; `v:real^3`] APX_SECTION_CMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `inv(norm v) % (v:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `&9 / &25 * inv eps`)) (concl th))) THEN
    STRIP_TAC THEN
    ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN
    SUBGOAL_THEN `--inv(&2 * eps) < apx_sval(y:real^3) /\
                  apx_sval(v:real^3) < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN
      DISJ_CASES_TAC(REAL_ARITH
        `norm(v:real^3) < (u:real^3->real) om \/ norm v = u om \/ u om < norm v`) THENL
       [USE_THEN "low" (MP_TAC o SPEC `v:real^3`) THEN
        ANTS_TAC THENL
         [CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[ASSUME `inv(norm v) % (v:real^3) = om`] THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `norm(v:real^3) < (u:real^3->real) om` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(v:real^3) = (u:real^3->real) om % om` ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(e:real^3->A) y IN Sg` MP_TAC THENL
         [FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
            concl th = `(e:real^3->A) y = (ez':real^3->A) v`)) THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            rand(concl th) = `Sg:A->bool` &&
            can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `om:real^3` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        EXPAND_TAC "Sg" THEN REWRITE_TAC[IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `y':real^3 = y` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_INJ THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `rfs_neck_dom eps`; `e:real^3->A`] THEN
          REPEAT CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC;
            FIRST_ASSUM ACCEPT_TAC;
            FIRST_X_ASSUM(ACCEPT_TAC o SYM o check (fun th ->
              concl th = `(e:real^3->A) y = e y'`))];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "high" (MP_TAC o SPEC `v:real^3`) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
          REWRITE_TAC[ASSUME `inv(norm v) % (v:real^3) = om`] THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        concl th = `(e:real^3->A) y = (ez':real^3->A) v`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* clause (2) for the pair, from clause (1) and injectivity *)
  SUBGOAL_THEN
   `DISJOINT (IMAGE (ez':real^3->A) (rfs_neck_dom eps))
             (IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
    DISJOINT (IMAGE (e:real^3->A) (rfs_neck_dom eps))
             (IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                   `eps:real`; `--inv eps`; `--inv(&2 * eps)`; `--inv(&2 * eps)`; `inv eps`]
                  APX_IMAGE_SLABS_DISJOINT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ez':real^3->A`;
                   `eps:real`; `--inv eps`; `inv(&2 * eps)`; `inv(&2 * eps)`; `inv eps`]
                  APX_IMAGE_SLABS_DISJOINT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET
                  IMAGE e (rfs_neck_dom eps) /\
                  IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
                  IMAGE ez' (rfs_neck_dom eps)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `IMAGE (e:real^3->A) (rfs_neck_dom eps) INTER IMAGE (ez':real^3->A) (rfs_neck_dom eps)
      SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
             IMAGE ez' (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* Sigma lies in the positive quarter of e *)
  SUBGOAL_THEN `Sg SUBSET IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Sg" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[APX_SPHERE_LEVEL; SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_INV_MUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the component *)
  SUBGOAL_THEN `Kc SUBSET topspace top DIFF (Sg:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`subtopology top (topspace top DIFF (Sg:A->bool))`; `pm:A`]
                  CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C. connected_in top C /\ C SUBSET topspace top DIFF Sg /\ ~(DISJOINT C Kc)
        ==> C SUBSET (Kc:A->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_CC_ABSORB THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET Kc`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&5 / &8 * inv eps))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
      REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `Kc:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> t = `Vl:real^3->bool`)) (concl th))) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET IMAGE ez' Vh`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
      UNDISCH_TAC `apx_slab (inv(&2 * eps)) (inv eps) SUBSET rfs_neck_dom eps` THEN
      SET_TAC[]; ALL_TAC] THEN
    USE_THEN "mem" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:real^3) IN rfs_neck_dom eps`)]) THEN
    MP_TAC(SPECL [`u:real^3->real`; `eps:real`; `v:real^3`] APX_SECTION_CMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `inv(norm v) % (v:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `&9 / &25 * inv eps`)) (concl th))) THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Kc:A->bool) (IMAGE ez' (apx_slab (inv(&2 * eps)) (inv eps)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
                 IMAGE ez' Vh` THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Kc:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
      can (find_term (fun t -> t = `Vh:real^3->bool`)) (concl th))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Kc INTER IMAGE (ez':real^3->A) (rfs_neck_dom eps) SUBSET
                IMAGE e (rfs_neck_dom eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (ez':real^3->A) Vl SUBSET IMAGE e (rfs_neck_dom eps)` MP_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^3) IN Vl` THEN
        UNDISCH_TAC `Vl SUBSET rfs_neck_dom eps` THEN SET_TAC[]; ALL_TAC] THEN
      USE_THEN "low" (MP_TAC o SPEC `v:real^3`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "mem" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
        (ASSUME `(v:real^3) IN rfs_neck_dom eps`)))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `Kc SUBSET topspace top DIFF (Sg:A->bool)` THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Kc:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
      can (find_term (fun t -> t = `Vh:real^3->bool`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `IMAGE (ez':real^3->A) (rfs_neck_dom eps)`)) THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!S L H N K E C U:A->bool.
        S UNION L UNION H = N ==> DISJOINT K (C UNION H) ==> K SUBSET U DIFF S ==>
        L SUBSET E ==> K INTER N SUBSET E`);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ez':real^3->A`; `Sg:A->bool`; `Kc:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A.18, part 4.  The earlier necks of the chain lie in the                  *)
(* component K below Sigma (downward induction: each is connected, misses    *)
(* Sigma by clause (2), and meets the next one by clause (1)); the assembly  *)
(* of MT Lemma A.18.                                                         *)
(* ------------------------------------------------------------------------- *)

let APX_SLAB_NONEMPTY = prove
 (`!a b. a < b ==> ?y:real^3. y IN apx_slab a b`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `exp(((a + b) / &2) / sqrt(&2)) % (&1 % basis 1:real^3)` THEN
  MP_TAC(SPECL [`(a + b) / &2`; `&1`] APX_SVAL_SCALED_BASIS) THEN
  REWRITE_TAC[REAL_LT_01; LOG_1; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

let APX_CHAIN_BELOW_K = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A) S K.
     &0 < eps /\
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     S SUBSET IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps)) /\
     (!C. connected_in top C /\ C SUBSET topspace top DIFF S /\ ~(DISJOINT C K)
          ==> C SUBSET K) /\
     IMAGE (e b) (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET K
     ==> !i. a <= i /\ i < b ==> IMAGE (e i) (rfs_neck_dom eps) SUBSET K`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "abs") ASSUME_TAC)))) THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))))) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `yp:real^3`) THEN
  MP_TAC(SPECL [`--inv eps`; `--inv(&2 * eps)`] APX_SLAB_NONEMPTY) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `yn:real^3`) THEN
  SUBGOAL_THEN
   `!i. a <= i /\ i <= b
        ==> connected_in top (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)) /\
            IMAGE (e i) (rfs_neck_dom eps) SUBSET topspace top`
  (LABEL_TAC "conn") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A) i) /\
                  smooth_manifold_atlas top atlas` STRIP_ASSUME_TAC THENL
     [USE_THEN "nk" (MP_TAC o SPEC `i:int`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MESON_TAC[rfs_neck];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3];
        REWRITE_TAC[SUBSET_REFL]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. a <= i /\ i + &1 + &n = b
          ==> IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET K`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    USE_THEN "abs" MATCH_MP_TAC THEN
    (USE_THEN "conn" (MP_TAC o SPEC `i:int`) THEN ANTS_TAC THENL
      [ASM_ARITH_TAC; STRIP_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    (USE_THEN "c2" (MP_TAC o SPECL [`i:int`; `b:int`]) THEN ANTS_TAC THENL
      [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT2)]) THEN
    (USE_THEN "c1" (MP_TAC o SPEC `i:int`) THEN ANTS_TAC THENL
      [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT1)]) THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THENL
     [EXISTS_TAC `(e:int->real^3->A) b yn` THEN
      SUBGOAL_THEN `i + &1:int = b` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(e:int->real^3->A) b yn IN IMAGE (e b) (apx_slab (--inv eps) (--inv(&2 * eps)))`
      ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      EXISTS_TAC `(e:int->real^3->A) i yp` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i + &1:int` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `K:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `connected_in`)) (concl th)))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `i + &1 + &(SUC n) = b:int` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
        DISCH_TAC] THEN
      SUBGOAL_THEN `(e:int->real^3->A) i yp IN IMAGE (e i) (apx_slab (inv(&2 * eps)) (inv eps))`
      ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `b - (i + &1):int` INT_OF_NUM_EXISTS))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* MT Lemma A.18 at a scale where the contexts hold. *)

let APX_A18_CORE = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A) z ez.
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\ a <= b /\
     apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e) /\
     rfs_neck (top,atlas) g eps z ez
     ==> ?ez'. (ez' = ez \/ ez' = apx_rev ez) /\
               apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b + &1}
                 (\i. if i = b + &1 then z else x i)
                 (\i. if i = b + &1 then ez' else e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bal" o REWRITE_RULE[IN_ELIM_THM])) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_chain; IN_ELIM_THM] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
     (LABEL_TAC "c2"))))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) b) (e b)` ASSUME_TAC THENL
   [USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z IN IMAGE ((e:int->real^3->A) b) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} (e:int->real^3->A))` THEN
    REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A) b) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A) b`; `(e:int->real^3->A) b`; `z:A`; `ez:real^3->A`]
                APX_A18_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (X_CHOOSE_THEN `S:A->bool`
    (X_CHOOSE_THEN `K:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A) b`; `(e:int->real^3->A) b`; `z:A`]
                APX_FRONTIER_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`;
                 `S:A->bool`; `K:A->bool`] APX_CHAIN_BELOW_K) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "below")] THEN
  EXISTS_TAC `ez':real^3->A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[apx_balanced; apx_chain; IN_ELIM_THM; APX_INT_INTERVAL_SEGMENT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `b:int` THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[INT_ARITH `~(b:int = b + &1)`] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(i:int = b + &1) /\ ~(i + &1:int = b + &1)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "c1" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a':int`; `i:int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(a':int = b + &1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i:int = b + &1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `a':int = b` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "below" (MP_TAC o SPEC `a':int`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "c2" (MP_TAC o SPECL [`a':int`; `b:int`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      SUBGOAL_THEN `IMAGE ((e:int->real^3->A) a') (apx_slab (--inv eps) (--inv(&2 * eps)))
                    SUBSET IMAGE (e a') (rfs_neck_dom eps)` ASSUME_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `K INTER IMAGE (ez':real^3->A) (rfs_neck_dom eps) SUBSET
                   IMAGE ((e:int->real^3->A) b) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `DISJOINT (K:A->bool) (IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) a') (rfs_neck_dom eps) SUBSET K` THEN
      UNDISCH_TAC `DISJOINT (IMAGE ((e:int->real^3->A) b) (rfs_neck_dom eps))
                            (IMAGE (e a') (apx_slab (--inv eps) (--inv(&2 * eps))))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) a') (apx_slab (--inv eps) (--inv(&2 * eps)))
                   SUBSET IMAGE (e a') (rfs_neck_dom eps)` THEN
      SET_TAC[];
      USE_THEN "c2" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[INT_ARITH `~(b:int = b + &1)`] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(i:int = b + &1) /\ ~(i + &1:int = b + &1)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bal" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* MT Lemma A.18 (with A.17), the statement form. *)

let APX_A18 = prove
 (`!u:A->bool. APX_A18_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A18_STATEMENT] THEN
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx")) APX_CH_CTX_HOLDS THEN
  X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "more")) APX_CH_MORE_HOLDS THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r")) APX_CH_N4R_HOLDS THEN
  EXISTS_TAC `min eps1 (min eps2 eps3)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "more" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "n4r" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC APX_A18_CORE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A.19, part 1.  For a finite chain N_a..N_b every point of                 *)
(* the union is deep in some neck, or in the bottom region of N_a, or in the *)
(* top region of N_b; hence the frontier of the union lies in the closures   *)
(* of the negative quarter of N_a and the positive quarter of N_b (the       *)
(* finite form of A.15).                                                      *)
(* ------------------------------------------------------------------------- *)

let APX_FIN_CHAIN_COVER = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A) q.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     q IN apx_chain_union eps {i:int | a <= i /\ i <= b} e
     ==> ?i z. a <= i /\ i <= b /\ z IN rfs_neck_dom eps /\ e i z = q /\
               (abs(apx_sval z) <= &7 / &8 * inv eps - &10 \/
                (i = a /\ apx_sval z < --(&7 / &8 * inv eps - &10)) \/
                (i = b /\ &7 / &8 * inv eps - &10 < apx_sval z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pair")
    (CONJUNCTS_THEN2 MP_TAC MP_TAC))) THEN
  REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (K ALL_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `abs(apx_sval(z:real^3)) <= &7 / &8 * inv eps - &10` THENL
   [MAP_EVERY EXISTS_TAC [`i:int`; `z:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `&0 < apx_sval(z:real^3)` THENL
   [ASM_CASES_TAC `i:int = b` THENL
     [MAP_EVERY EXISTS_TAC [`i:int`; `z:real^3`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i) /\
                  rfs_neck (top,atlas) g eps (x(i + &1)) (e(i + &1))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "c1" (MP_TAC o SPEC `i:int`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "pair" (MP_TAC o SPECL [`(x:int->A) i`; `(e:int->real^3->A) i`;
      `(x:int->A)(i + &1)`; `(e:int->real^3->A)(i + &1)`; `ei:A->real^3`] o
      REWRITE_RULE[apx_ch_pair]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:A) IN IMAGE ((e:int->real^3->A)(i + &1)) (rfs_neck_dom eps)` MP_TAC THENL
     [UNDISCH_TAC `IMAGE ((e:int->real^3->A) i) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
                   IMAGE (e(i + &1)) (apx_slab (--inv eps) (--inv(&2 * eps)))
                   SUBSET IMAGE (e i) (rfs_neck_dom eps) INTER
                          IMAGE (e(i + &1)) (rfs_neck_dom eps)` THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
      ANTS_TAC THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ei:A->real^3)((e:int->real^3->A)(i + &1) v) = z` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`(i:int) + &1`; `v:real^3`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN
    MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_INV_MUL]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:int = a` THENL
   [MAP_EVERY EXISTS_TAC [`i:int`; `z:real^3`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?j:int. a <= j /\ i = j + &1`
  (X_CHOOSE_THEN `j:int` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [EXISTS_TAC `(i:int) - &1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) j) ((e:int->real^3->A) j) /\
                rfs_neck (top,atlas) g eps (x(j + &1)) (e(j + &1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A) j`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "c1" (MP_TAC o SPEC `j:int`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "pair" (MP_TAC o SPECL [`(x:int->A) j`; `(e:int->real^3->A) j`;
    `(x:int->A)(j + &1)`; `(e:int->real^3->A)(j + &1)`; `ei:A->real^3`] o
    REWRITE_RULE[apx_ch_pair]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q:A) IN IMAGE ((e:int->real^3->A) j) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((e:int->real^3->A) j) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
                 IMAGE (e(j + &1)) (apx_slab (--inv eps) (--inv(&2 * eps)))
                 SUBSET IMAGE (e j) (rfs_neck_dom eps) INTER
                        IMAGE (e(j + &1)) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
    ANTS_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `(e:int->real^3->A)(j + &1) z = q` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_abs")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`j:int`; `(ei:A->real^3) q`] THEN
  SUBGOAL_THEN `(ei:A->real^3) q IN rfs_neck_dom eps /\ (e:int->real^3->A) j (ei q) = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:A) IN IMAGE ((e:int->real^3->A) j) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISJ1_TAC THEN
  MP_TAC(SPECL [`eps:real`; `(ei:A->real^3) q`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_INV_MUL]) THEN ASM_REAL_ARITH_TAC);;

let APX_FIN_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= b} x e
     ==> top frontier_of (apx_chain_union eps {i:int | a <= i /\ i <= b} e) SUBSET
         top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                         IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `!i. a <= i /\ i <= b
                    ==> rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union eps {i:int | a <= i /\ i <= b} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `a <= (i:int) /\ i <= b`) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar"))
                            (concl th)))) THEN
      SIMP_TAC[rfs_neck];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = max (mfd_scalar atlas (g:A->real^3^3) p) (&0) + &1` THEN
  SUBGOAL_THEN `&0 < c /\ mfd_scalar atlas (g:A->real^3^3) p < c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `hs = inv(sqrt(&2 * c))` THEN
  SUBGOAL_THEN `&0 < hs` ASSUME_TAC THENL
   [EXPAND_TAC "hs" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = &99 / &100 * hs * (inv eps / &8 + &10)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `O = {q:A | q IN topspace top /\ mfd_scalar atlas (g:A->real^3^3) q IN
                         {t | t < c}} INTER mfd_ball (top,atlas) g p r` THEN
  SUBGOAL_THEN `open_in top (O:A->bool) /\ (p:A) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
      REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS; GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT];
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  (* the union meets O only in the end quarters *)
  SUBGOAL_THEN
   `!q. q IN U /\ q IN O
        ==> q IN IMAGE ((e:int->real^3->A) a) (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                 IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `q:A`]
                  APX_FIN_CHAIN_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
    MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))
    THENL
     [(* deep: p would lie in the neck *)
      MATCH_MP_TAC(TAUT `F ==> p`) THEN UNDISCH_TAC `~((p:A) IN U)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p:A) IN IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)` MP_TAC THENL
       [ALL_TAC;
        EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_TAC THEN EXISTS_TAC `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN `rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(q:A) IN O` THEN EXPAND_TAC "O" THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; mfd_ball] THEN STRIP_TAC THEN
      MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `(x:int->A) i`; `z:real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `q:A`; `p:A`] MFD_JOINABLE_SYM) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "r" THEN
      SUBGOAL_THEN `hs <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)))`
      ASSUME_TAC THENL
       [EXPAND_TAC "hs" THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) /\
                      mfd_scalar atlas g (x i) <= &2 * c` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i)
                                  ((e:int->real^3->A) i)` THEN SIMP_TAC[rfs_neck];
            MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `&2 * mfd_scalar atlas (g:A->real^3^3) q` THEN CONJ_TAC THENL
             [UNDISCH_TAC `(e:int->real^3->A) i z = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
              FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
                is_forall (concl th) && can (find_term (fun t -> t = `&2`)) (concl th) &&
                can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar"))
                    (concl th) &&
                not (can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt"))
                         (concl th)))) THEN
              ASM_REWRITE_TAC[];
              ASM_REAL_ARITH_TAC]];
          ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE]];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv eps / &8 + &10 <= inv eps - abs(apx_sval(z:real^3))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      (* bottom of N_a *)
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
      UNDISCH_TAC `(e:int->real^3->A) a z = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN
      ASM_REAL_ARITH_TAC;
      (* top of N_b *)
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
      UNDISCH_TAC `(e:int->real^3->A) b z = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL; REAL_INV_MUL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_CLOSURE_OF] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:A) IN top closure_of U` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
  DISCH_THEN(MP_TAC o SPEC `t INTER O:A->bool` o CONJUNCT2) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:A` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `O:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A.19, part 2.  A uniform bound on the length of chains                    *)
(* centred in a compact set (from the separation of the centres and a finite *)
(* cover by balls, as in APX_CHAIN_FINITE_CORE).                              *)
(* ------------------------------------------------------------------------- *)

(* A uniform bound: the necks of a chain centred in a compact set are at   *)
(* most as many as the balls of a fixed finite cover.                        *)

let APX_CHAIN_CARD_BOUND = prove
 (`!top atlas (g:A->real^3^3) eps K.
     apx_ch_ctx top atlas g eps /\ compact_in top K
     ==> ?N. !Ix x (e:int->real^3->A).
               apx_chain (top,atlas) g eps Ix x e /\ (!i. i IN Ix ==> x i IN K)
               ==> FINITE Ix /\ CARD Ix <= N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?Rm. &1 <= Rm /\ !p. p IN K ==> mfd_scalar atlas (g:A->real^3^3) p <= Rm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `mfd_scalar atlas (g:A->real^3^3)`;
                   `K:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN
    EXISTS_TAC `max (&1) B` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt Rm) /\ &0 < inv(&8 * eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `r = &99 / &100 * inv(sqrt Rm) * inv(&8 * eps)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a finite cover of K by balls of radius r / 2 *)
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `{mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      EXISTS_TAC `p:A` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CARD(V:(A->bool)->bool)` THEN
  MAP_EVERY X_GEN_TAC [`Ix:int->bool`; `x:int->A`; `e:int->real^3->A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN Ix ==> rfs_neck (top,atlas) g eps ((x:int->A) i) ((e:int->real^3->A) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x (e:int->real^3->A)` THEN
    REWRITE_TAC[apx_chain] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* separation of the centres *)
  SUBGOAL_THEN
   `!i j. i IN Ix /\ j IN Ix /\ mfd_joinable (top,atlas) ((x:int->A) i) (x j) /\
          mfd_dist (top,atlas) (g:A->real^3^3) (x i) (x j) < r ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `r <= &99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i))) *
                       inv(&8 * eps)` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
          is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist"))
                              (concl th)))) THEN
        SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `(x:int->A) i`; `(e:int->real^3->A) i`; `(x:int->A) j`]
                  APX_CENTRE_DEEP_BALL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC APX_CHAIN_NO_DEEP_CENTRE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `eps:real`; `Ix:int->bool`; `x:int->A`;
                          `e:int->real^3->A`; `i:int`; `j:int`; `z:real^3`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN Ix ==> ?B. B IN V /\ (x:int->A) i IN B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:int->A) i IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = \i. @B. B IN V /\ (x:int->A) i IN B` THEN
  SUBGOAL_THEN `!i j. i IN Ix /\ j IN Ix /\ (f:int->A->bool) i = f j ==> i = j`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:int`; `j:int`] THEN EXPAND_TAC "f" THEN BETA_TAC THEN
    STRIP_TAC THEN
    ABBREV_TAC `B0 = @B. B IN V /\ (x:int->A) i IN B` THEN
    SUBGOAL_THEN `B0 IN V /\ (x:int->A) i IN B0 /\ x j IN B0` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(j:int) IN Ix`) o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?p. p IN K /\ B0 = mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `B0 IN (V:(A->bool)->bool)` THEN
      UNDISCH_TAC `V SUBSET {mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:int->A) i IN B0` THEN UNDISCH_TAC `(x:int->A) j IN B0` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) ((x:int->A) i) p`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(x:int->A) i`;
                     `p:A`] MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `r:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:int->A) i) p +
                  mfd_dist (top,atlas) g p (x j)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `(x:int->A) i`; `p:A`] MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:int->A->bool) Ix SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN Ix`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (Ix:int->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:int->A->bool`; `Ix:int->bool`] FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:int->A->bool) Ix)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A.19, part 3.  Reversal and slabs; the later necks of a                   *)
(* chain lie in the component K above the reversed first neck; the balanced *)
(* distance relative to the scale of the new neck (from the fine curvature   *)
(* ratio of overlapping necks).                                              *)
(* ------------------------------------------------------------------------- *)

let APX_INVERSION_INVOL = prove
 (`!y:real^3. inv(norm(inv(norm y pow 2) % y) pow 2) % (inv(norm y pow 2) % y) = y`,
  GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN `inv(norm(inv(norm(y:real^3) pow 2) % y) pow 2) * inv(norm y pow 2) = &1`
   (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  CONV_TAC REAL_FIELD);;

let APX_INVERSION_NONZERO = prove
 (`!y:real^3. ~(y = vec 0) ==> ~(inv(norm y pow 2) % y = vec 0)`,
  SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC);;

let APX_REV_IMAGE_SLAB = prove
 (`!(e:real^3->A) a b.
     IMAGE (apx_rev e) (apx_slab a b) = IMAGE e (apx_slab (--b) (--a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; apx_rev] THEN
  X_GEN_TAC `q:A` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(norm y pow 2) % (y:real^3)` THEN
  ASM_REWRITE_TAC[APX_INVERSION_INVOL; APX_SLAB_SVAL] THEN
  ASM_SIMP_TAC[APX_INVERSION_NONZERO; APX_SVAL_INVERSION] THEN ASM_REAL_ARITH_TAC);;

let APX_REV_IMAGE_DOM = prove
 (`!(e:real^3->A) eps. IMAGE (apx_rev e) (rfs_neck_dom eps) = IMAGE e (rfs_neck_dom eps)`,
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_REV_IMAGE_SLAB; REAL_NEG_NEG]);;

let APX_CHAIN_ABOVE_K = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A) S K.
     &0 < eps /\
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     S SUBSET IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps))) /\
     (!C. connected_in top C /\ C SUBSET topspace top DIFF S /\ ~(DISJOINT C K)
          ==> C SUBSET K) /\
     IMAGE (e a) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET K
     ==> !i. a < i /\ i <= b ==> IMAGE (e i) (rfs_neck_dom eps) SUBSET K`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "abs") ASSUME_TAC)))) THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))))) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `yp:real^3`) THEN
  MP_TAC(SPECL [`--inv eps`; `--inv(&2 * eps)`] APX_SLAB_NONEMPTY) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `yn:real^3`) THEN
  SUBGOAL_THEN
   `!i. a <= i /\ i <= b
        ==> connected_in top (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)) /\
            IMAGE (e i) (rfs_neck_dom eps) SUBSET topspace top`
  (LABEL_TAC "conn") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A) i) /\
                  smooth_manifold_atlas top atlas` STRIP_ASSUME_TAC THENL
     [USE_THEN "nk" (MP_TAC o SPEC `i:int`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MESON_TAC[rfs_neck];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3];
        REWRITE_TAC[SUBSET_REFL]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. i = a + &1 + &n /\ i <= b
          ==> IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET K`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    USE_THEN "abs" MATCH_MP_TAC THEN
    (USE_THEN "conn" (MP_TAC o SPEC `i:int`) THEN ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
       STRIP_TAC]) THEN
    ASM_REWRITE_TAC[] THEN
    (USE_THEN "c2" (MP_TAC o SPECL [`a:int`; `i:int`]) THEN ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
       DISCH_THEN(ASSUME_TAC o CONJUNCT1)]) THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THENL
     [USE_THEN "c1" (MP_TAC o SPEC `a:int`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      EXISTS_TAC `(e:int->real^3->A) a yp` THEN
      SUBGOAL_THEN `a + &1:int = i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(e:int->real^3->A) a yp IN IMAGE (e a) (apx_slab (inv(&2 * eps)) (inv eps))`
      ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      USE_THEN "c1" (MP_TAC o SPEC `i - &1:int`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
        DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i - &1:int` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `K:A->bool`)) (concl th) &&
        not (can (find_term (fun t -> t = `connected_in`)) (concl th)))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
        DISCH_TAC] THEN
      SUBGOAL_THEN `i - &1 + &1:int = i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [INT_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `(e:int->real^3->A) i yn` THEN
      SUBGOAL_THEN `(e:int->real^3->A) i yn IN IMAGE (e i) (apx_slab (--inv eps) (--inv(&2 * eps)))`
      ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `i - (a + &1):int` INT_OF_NUM_EXISTS))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The balanced distance relative to the scale of the new neck at z. *)

let APX_FRONTIER_DIST2 = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) z (ez:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z ez /\
     z IN top closure_of (IMAGE e (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN IMAGE e (rfs_neck_dom eps))
     ==> mfd_joinable (top,atlas) z x /\
         &99 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps
         <= mfd_dist (top,atlas) g z x /\
         mfd_dist (top,atlas) g z x
         <= &101 / &100 * inv(sqrt(mfd_scalar atlas g z)) * inv eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?x0. x0 IN sphere(vec 0,&1) /\ (e:real^3->A) x0 = x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ apx_sval x0 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\ &0 < mfd_scalar atlas g z /\
                &0 < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the fine scale comparison from an overlap point *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`]
                APX_FRONTIER_QUARTER_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `yp:real^3`) THEN
  SUBGOAL_THEN `(yp:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN rfs_neck_dom eps /\ (ez:real^3->A) v = (e:real^3->A) yp`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET
                 IMAGE ez (rfs_neck_dom eps)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `yp:real^3`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g z - &1) <= &1 / &1638400 /\
    abs(mfd_scalar atlas (g:A->real^3^3) z / mfd_scalar atlas g x - &1) <= &1 / &1638400`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[apx_ch_more] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_more")) (concl th))) THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`z:A`; `ez:real^3->A`; `x:A`; `e:real^3->A`; `yp:real^3`] th) THEN
      MP_TAC(SPECL [`x:A`; `e:real^3->A`; `z:A`; `ez:real^3->A`; `v:real^3`] th)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `yp:real^3` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `v:real^3` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) <=
    &201 / &200 * inv(sqrt(mfd_scalar atlas g x)) /\
    inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <=
    &100001 / &100000 * inv(sqrt(mfd_scalar atlas g z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_INV_SQRT_RATIO_GEN THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  (* a point of the top of e near z *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `h / &10`] APX_FRONTIER_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(y:real^3)) < inv eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `x0:real^3`; `y:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
      can (find_term (fun t -> t = `&1 / &200`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "exit")))) THEN
  SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) (x:A) z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(e:real^3->A) y` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `z:A`; `(e:real^3->A) y`] MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z:A`; `x:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) (z:A) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `z:A`; `x:A`] MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the lower bound from the exit length at 1/200 *)
    SUBGOAL_THEN `(&1 - &1 / &200) * h * inv eps <= mfd_dist (top,atlas) (g:A->real^3^3) x z`
    MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(d < b) ==> b <= d`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `z:A`; `(&1 - &1 / &200) * h * inv eps`]
                    APX_DIST_SHORT_CURVE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      USE_THEN "exit" (MP_TAC o SPECL [`gamma:real->A`; `&0`; `&1`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `h' * inv eps <= (&201 / &200 * h) * inv eps /\ &0 <= h * inv eps`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x ((e:real^3->A) y) +
              mfd_dist (top,atlas) g (e y) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `z:A`; `(e:real^3->A) y`] MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `(e:real^3->A) y`; `z:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `h * abs(apx_sval(y:real^3)) <= h * inv eps /\
                h * sqrt(&2) * pi <= h * (&24 / &5) /\ h' * &1024 <= h' * inv eps /\
                h * inv eps <= (&100001 / &100000 * h') * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; APX_SQRT2_PI];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A.19, part 4.  Extension of a balanced chain at its                       *)
(* negative end (the mirror of A.18): the pair lemma for the reversed first  *)
(* neck, the new neck reversed, the later necks in the component above, and  *)
(* the balanced distance relative to the scale of the new neck.              *)
(* ------------------------------------------------------------------------- *)

let APX_A18_NEG_CORE = prove
 (`!top atlas (g:A->real^3^3) eps a b x (e:int->real^3->A) z ez.
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\ a <= b /\
     apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     z IN top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
     ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e) /\
     rfs_neck (top,atlas) g eps z ez
     ==> ?ez'. (ez' = ez \/ ez' = apx_rev ez) /\
               apx_balanced (top,atlas) g eps {i:int | a - &1 <= i /\ i <= b}
                 (\i. if i = a - &1 then z else x i)
                 (\i. if i = a - &1 then ez' else e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bal" o REWRITE_RULE[IN_ELIM_THM])) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_chain; IN_ELIM_THM] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_chain")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
     (LABEL_TAC "c2"))))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) a) (e a) /\
                rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) a) (apx_rev (e a))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) a) (e a)` ASSUME_TAC
    THENL [USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[APX_REV_NECK];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z IN IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} (e:int->real^3->A))` THEN
    REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:int` THEN ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A) a`; `apx_rev((e:int->real^3->A) a)`; `z:A`;
                 `ez:real^3->A`] APX_A18_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG]; ALL_TAC] THEN
  REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (X_CHOOSE_THEN `S:A->bool`
    (X_CHOOSE_THEN `K:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A) a`; `apx_rev((e:int->real^3->A) a)`; `z:A`;
                 `ez:real^3->A`] APX_FRONTIER_DIST2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`;
                 `S:A->bool`; `K:A->bool`] APX_CHAIN_ABOVE_K) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "above")] THEN
  EXISTS_TAC `apx_rev(ez':real^3->A)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term (fun t -> t = `ez':real^3->A`)) (concl th))) THEN
    REWRITE_TAC[APX_REV_REV];
    ALL_TAC] THEN
  REWRITE_TAC[apx_balanced; apx_chain; IN_ELIM_THM; APX_INT_INTERVAL_SEGMENT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `b:int` THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[APX_REV_NECK]; USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = a - &1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[INT_ARITH `a - &1 + &1:int = a`; INT_ARITH `~(a:int = a - &1)`] THEN
      REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE ((e:int->real^3->A) a) (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                     IMAGE (ez':real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps)))
                     SUBSET IMAGE (e a) (rfs_neck_dom eps) INTER IMAGE ez' (rfs_neck_dom eps)` THEN
        SET_TAC[];
        UNDISCH_TAC `IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps) INTER
                     IMAGE (ez':real^3->A) (rfs_neck_dom eps)
                     SUBSET IMAGE (e a) (apx_slab (--inv eps) (inv(&2 * eps))) INTER
                            IMAGE ez' (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
        SET_TAC[]];
      SUBGOAL_THEN `~(i:int = a - &1) /\ ~(i + &1:int = a - &1)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "c1" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a':int`; `i:int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i:int = a - &1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `a':int = a - &1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG] THEN
      ASM_CASES_TAC `i:int = a` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "above" (MP_TAC o SPEC `i:int`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "c2" (MP_TAC o SPECL [`a:int`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
      SUBGOAL_THEN `IMAGE ((e:int->real^3->A) i) (apx_slab (inv(&2 * eps)) (inv eps))
                    SUBSET IMAGE (e i) (rfs_neck_dom eps)` ASSUME_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `K INTER IMAGE (ez':real^3->A) (rfs_neck_dom eps) SUBSET
                   IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `DISJOINT (K:A->bool) (IMAGE (ez':real^3->A) (apx_slab (inv(&2 * eps)) (inv eps)))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET K` THEN
      UNDISCH_TAC `DISJOINT (IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps))
                            (IMAGE (e i) (apx_slab (inv(&2 * eps)) (inv eps)))` THEN
      UNDISCH_TAC `IMAGE ((e:int->real^3->A) i) (apx_slab (inv(&2 * eps)) (inv eps))
                   SUBSET IMAGE (e i) (rfs_neck_dom eps)` THEN
      SET_TAC[];
      USE_THEN "c2" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = a - &1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[INT_ARITH `a - &1 + &1:int = a`; INT_ARITH `~(a:int = a - &1)`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(i:int = a - &1) /\ ~(i + &1:int = a - &1)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bal" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* A.19, part 5.  Integer segments, single-neck chains, the                  *)
(* shift of a chain to start at 0, and the extension step: a balanced chain *)
(* centred in a connected set X that does not cover X extends by one neck  *)
(* centred in X at one of its ends.                                          *)
(* ------------------------------------------------------------------------- *)

let APX_INT_SEG_CARD_TOP = prove
 (`!a b:int. a <= b
             ==> CARD {i:int | a <= i /\ i <= b + &1} = CARD {i:int | a <= i /\ i <= b} + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{i:int | a <= i /\ i <= b + &1} = (b + &1) INSERT {i:int | a <= i /\ i <= b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INT_SEG] THEN
  REWRITE_TAC[IN_ELIM_THM; INT_ARITH `~((b:int) + &1 <= b)`; ADD1]);;

let APX_INT_SEG_CARD_BOT = prove
 (`!a b:int. a <= b
             ==> CARD {i:int | a - &1 <= i /\ i <= b} = CARD {i:int | a <= i /\ i <= b} + 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{i:int | a - &1 <= i /\ i <= b} = (a - &1) INSERT {i:int | a <= i /\ i <= b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INT_SEG] THEN
  REWRITE_TAC[IN_ELIM_THM; INT_ARITH `~((a:int) <= a - &1)`; ADD1]);;

let APX_SINGLE_CHAIN = prove
 (`!top atlas (g:A->real^3^3) eps (x0:A) (e0:real^3->A).
     rfs_neck (top,atlas) g eps x0 e0
     ==> apx_balanced (top,atlas) g eps {i:int | &0 <= i /\ i <= &0} (\i. x0) (\i. e0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[apx_balanced; apx_chain; IN_ELIM_THM; APX_INT_INTERVAL_SEGMENT] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0:int` THEN
    INT_ARITH_TAC;
    INT_ARITH_TAC;
    INT_ARITH_TAC;
    INT_ARITH_TAC]);;

let APX_CHAIN_SHIFT = prove
 (`!top atlas (g:A->real^3^3) eps a n x (e:int->real^3->A).
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= a + &n} x e
     ==> apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n}
                   (\i. x(i + a)) (\i. e(i + a)) /\
         apx_chain_union eps {i:int | &0 <= i /\ i <= &n} (\i. e(i + a)) =
         apx_chain_union eps {i:int | a <= i /\ i <= a + &n} e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[apx_chain; IN_ELIM_THM; APX_INT_INTERVAL_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "nk")
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")))) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0:int` THEN
    INT_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    REWRITE_TAC[INT_ARITH `(i + &1) + a:int = (i + a) + &1`] THEN
    USE_THEN "c1" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a':int`; `i:int`] THEN STRIP_TAC THEN
    USE_THEN "c2" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[apx_chain_union] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i + a:int` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i - a:int` THEN ASM_REWRITE_TAC[INT_SUB_ADD] THEN ASM_ARITH_TAC]]);;

(* The extension step. *)

let APX_A19_STEP = prove
 (`!top atlas (g:A->real^3^3) eps NK X a b x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx_sphere_sep top atlas /\ connected_in top X /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN X ==> ?e. NK x e) /\
     a <= b /\ apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     (!i. a <= i /\ i <= b
          ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
     ~(X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e)
     ==> ?a' b' x' e'.
           a' <= b' /\
           apx_balanced (top,atlas) g eps {i:int | a' <= i /\ i <= b'} x' e' /\
           (!i. a' <= i /\ i <= b'
                ==> x' i IN X /\ (NK (x' i) (e' i) \/ NK (x' i) (apx_rev (e' i)))) /\
           CARD {i:int | a' <= i /\ i <= b'} = CARD {i:int | a <= i /\ i <= b} + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union eps {i:int | a <= i /\ i <= b} (e:int->real^3->A)` THEN
  (* U is open and contains the centre of N_a *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) a) (e a)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. a <= i /\ i <= b
                    ==> IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN t ==> s SUBSET UNIONS t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:int->A) a IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) a) (e a)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:int` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* a point of X on the frontier of U *)
  MP_TAC(ISPECL [`top:A topology`; `X:A->bool`; `U:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(x:int->A) a` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:int` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
        can (find_term (fun t -> t = `NK:A->(real^3->A)->bool`)) (concl th) &&
        can (find_term (fun t -> t = `x:int->A`)) (concl th))) THEN
      ASM_SIMP_TAC[INT_LE_REFL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`]
                APX_FIN_FRONTIER) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_UNION] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((z:A) IN U)` ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e` THEN
        REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[rfs_neck];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN top frontier_of U` THEN
    ASM_SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN; IN_DIFF];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `ez:real^3->A` o C MATCH_MP (ASSUME `(z:A) IN X`) o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
    not (can (find_term (fun t -> t = `x:int->A`)) (concl th)))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z ez` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!ez':real^3->A. (ez' = ez \/ ez' = apx_rev ez)
                                ==> NK (z:A) ez' \/ NK z (apx_rev ez')`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[APX_REV_REV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN top closure_of
                  (IMAGE ((e:int->real^3->A) a) (apx_slab (--inv eps) (--inv(&2 * eps)))) \/
                z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps)))`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                   `ez:real^3->A`] APX_A18_NEG_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`a - &1:int`; `b:int`; `\i:int. if i = a - &1 then (z:A) else x i`;
      `\i:int. if i = a - &1 then (ez':real^3->A) else e i`] THEN
    ASM_SIMP_TAC[APX_INT_SEG_CARD_BOT] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
      can (find_term (fun t -> t = `x:int->A`)) (concl th))) THEN
    ASM_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                   `ez:real^3->A`] APX_A18_CORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`a:int`; `b + &1:int`; `\i:int. if i = b + &1 then (z:A) else x i`;
      `\i:int. if i = b + &1 then (ez':real^3->A) else e i`] THEN
    ASM_SIMP_TAC[APX_INT_SEG_CARD_TOP] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
      can (find_term (fun t -> t = `x:int->A`)) (concl th))) THEN
    ASM_ARITH_TAC]);;

(* MT Prop A.19 at a scale where the contexts hold: a maximal extension     *)
(* argument with the uniform bound on chain lengths.                         *)

let APX_A19_CORE = prove
 (`!top atlas (g:A->real^3^3) eps NK X.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx_sphere_sep top atlas /\
     compact_in top X /\ connected_in top X /\ ~(X = {}) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN X ==> ?e. NK x e)
     ==> ?a b x e.
           a <= b /\
           apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
           (!i. a <= i /\ i <= b
                ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
           X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `X:A->bool`] APX_CHAIN_CARD_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "bd"))] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "nc") THEN
  SUBGOAL_THEN
   `!n. ?a b x (e:int->real^3->A).
          a <= b /\
          apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
          (!i. a <= i /\ i <= b
               ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
          n <= CARD {i:int | a <= i /\ i <= b}`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [UNDISCH_TAC `~(X:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
      FIRST_ASSUM(X_CHOOSE_TAC `e0:real^3->A` o C MATCH_MP (ASSUME `(x0:A) IN X`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
          not (can (find_term (fun t -> t = `CARD`)) (concl th)))) THEN
      MAP_EVERY EXISTS_TAC [`&0:int`; `&0:int`; `\i:int. (x0:A)`;
                            `\i:int. (e0:real^3->A)`] THEN
      REWRITE_TAC[INT_LE_REFL; LE_0] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_SINGLE_CHAIN THEN ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
        (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC)))) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`;
                     `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`] APX_A19_STEP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "nc" MP_TAC THEN REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a':int` (X_CHOOSE_THEN `b':int` (X_CHOOSE_THEN `x':int->A`
        (X_CHOOSE_THEN `e':int->real^3->A` STRIP_ASSUME_TAC)))) THEN
      MAP_EVERY EXISTS_TAC [`a':int`; `b':int`; `x':int->A`; `e':int->real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `SUC N`) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
    (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC)))) THEN
  USE_THEN "bd" (MP_TAC o SPECL [`{i:int | a <= i /\ i <= b}`; `x:int->A`;
                                 `e:int->real^3->A`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced"))
            (concl th))) THEN
      SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* MT Prop A.19 (corrected), the statement form: the chain and its tube   *)
(* (A.13 for the chain shifted to start at 0).                            *)

let APX_A19 = prove
 (`!u:A->bool. APX_A19_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A19_STATEMENT] THEN
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx")) APX_CH_CTX_HOLDS THEN
  X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "more")) APX_CH_MORE_HOLDS THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r")) APX_CH_N4R_HOLDS THEN
  X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a13"))
    (SPEC `u:A->bool` APX_A13_UNCOND) THEN
  EXISTS_TAC `min (min eps1 eps2) (min eps3 eps4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~(X:A->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `e0:real^3->A` o C MATCH_MP (ASSUME `(x0:A) IN X`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `X:A->bool`)) (concl th))) THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps x0 e0` MP_TAC THENL
     [ASM_SIMP_TAC[]; SIMP_TAC[rfs_neck]];
    ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "more" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "n4r" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`] APX_A19_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `x:int->A`
    (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(snd(EQ_IMP_RULE(SPEC `b - a:int` INT_OF_NUM_EXISTS))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  SUBGOAL_THEN `b:int = a + &n` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `n:num`; `x:int->A`; `e:int->real^3->A`]
                APX_CHAIN_SHIFT) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_balanced] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
    SIMP_TAC[];
    STRIP_TAC] THEN
  USE_THEN "a13" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `n:num`; `\i:int. (x:int->A)(i + a)`;
    `\i:int. (e:int->real^3->A)(i + a)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `exp(--inv eps / sqrt(&2))`;
                        `exp((L + inv eps) / sqrt(&2))`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) =
               apx_chain_union eps {i:int | &0 <= i /\ i <= &n} (\i. (e:int->real^3->A)(i + a))` THEN
  ASM_REWRITE_TAC[apx_slab]);;

