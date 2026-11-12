(* ========================================================================= *)
(* pc_apx_far: MT Lemma A.9 in the crude form APX_A9_CRUDE of pc_apx_csreq  *)
(* (difference quotients of d(z,.) along s-lines of a separating neck, for  *)
(* s-differences of at least 16/alpha).  Proof: a curve from z to q meets   *)
(* the level sphere of p (the level sphere separates, being the central     *)
(* sphere of the rescaled neck chart, and z lies below it); after its last  *)
(* visit the curve stays above the level, so its length is at least the     *)
(* s-difference; the sphere has diameter at most about sqrt(2) pi.           *)
(* ========================================================================= *)

needs "src/pc_apx_short.ml";;
needs "src/pc_apx_csreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The sides of a level sphere of a neck.                                    *)
(* ------------------------------------------------------------------------- *)

(* The closure of a component of the complement of S adds only points of S. *)

let APXF_COMPONENT_CLOSURE = prove
 (`!top S (y:A).
     top closure_of (connected_component_of (subtopology top (topspace top DIFF S)) y)
     SUBSET connected_component_of (subtopology top (topspace top DIFF S)) y UNION S`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Q = connected_component_of (subtopology top (topspace top DIFF S)) (y:A)` THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S:A->bool)`; `y:A`]
                CLOSED_IN_CONNECTED_COMPONENT_OF) THEN
  ASM_REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `top closure_of (Q:A->bool) SUBSET C` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `Q:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
  ASM SET_TAC[]);;

(* Levels of the reference points of a neck chart. *)

let APXF_SVAL_REF = prove
 (`apx_sval(&3 / &4 % basis 1:real^3) < &0 /\ -- &1 <= apx_sval(&3 / &4 % basis 1:real^3) /\
   &0 < apx_sval(&4 / &3 % basis 1:real^3) /\ apx_sval(&4 / &3 % basis 1:real^3) <= &1`,
  REWRITE_TAC[apx_sval; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&0 < log(&4 / &3) /\ log(&4 / &3) <= &1 / &3 /\ log(&3 / &4) = --log(&4 / &3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `&1 / &3` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      MP_TAC(SPEC `&4 / &3` LOG_INV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log(&4 / &3) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1 / &3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `s * --l < &0 <=> &0 < s * l`] THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ASM_REWRITE_TAC[REAL_ARITH `-- &1 <= s * --l <=> s * l <= &1`];
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

(* The level sphere of level t of a neck is the central sphere of the        *)
(* rescaled chart e(exp(t / sqrt 2) y). *)

let APXF_SPHERE_SCALE = prove
 (`!(e:real^3->A) c. &0 < c
     ==> IMAGE (\y. e(c % y)) (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^3. (e:real^3->A)(c % y)) = e o (\y. c % y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `inv c % z:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; NORM_MUL;
                 REAL_ABS_INV] THEN
    SUBGOAL_THEN `abs c = c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]]]);;

(* The two sides of a level sphere of a neck, at levels |t| <= 1/(2 eps):   *)
(* the sphere is the central sphere of the rescaled neck chart, which       *)
(* separates by apx_sphere_sep; the in-neck parts below and above the level *)
(* lie on the two sides.                                                     *)

let APXF_LEVEL_SIDES = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) t.
     hausdorff_space top /\ apx_sphere_sep top atlas /\ rfs_neck (top,atlas) g eps x e /\
     eps <= &1 / &1024 /\ abs t <= inv(&2 * eps)
     ==> ?L U. closed_in top (IMAGE e (sphere(vec 0,exp(t / sqrt(&2))))) /\
               L SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               U SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               DISJOINT L U /\ open_in top L /\ open_in top U /\
               top closure_of L SUBSET L UNION IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               top closure_of U SUBSET U UNION IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               IMAGE e (apx_slab (--inv eps) t) SUBSET L /\
               IMAGE e (apx_slab t (inv eps)) SUBSET U /\
               (!K. connected_in top K /\
                    K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
                    ~(K INTER L = {})
                    ==> K SUBSET L) /\
               (!K. connected_in top K /\
                    K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
                    ~(K INTER U = {})
                    ==> K SUBSET U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t <= inv eps / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `abs t <= inv(&2 * eps)` THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * log(&2) /\ sqrt(&2) * log(&2) <= &2 /\
                log(&1 / &2) = --log(&2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log(&2) /\ log(&2) <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
        MP_TAC(SPEC `&1` LOG_LE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
      MP_TAC(SPEC `&2` LOG_INV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = exp(t / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  (* the rescaled chart *)
  SUBGOAL_THEN `mfd_neck_chart top atlas (\y:real^3. (e:real^3->A)(c % y))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN
    SUBGOAL_THEN `(\y:real^3. (e:real^3->A)(c % y)) = e o (\y. c % y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_neck_dom eps`;
      `apx_slab (sqrt(&2) * log(&1 / &2) + t) (sqrt(&2) * log(&2) + t)`;
      `\y:real^3. exp(--t / sqrt(&2)) % y`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN
      SUBGOAL_THEN `annulus (&1 / &2) (&2) =
                    apx_slab (sqrt(&2) * log(&1 / &2)) (sqrt(&2) * log(&2)):real^3->bool`
      SUBST1_TAC THENL
       [MATCH_MP_TAC APX_ANNULUS_AS_SLAB THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `log(&1 / &2) = --log(&2)`; APX_SLAB_SCALE_DIFFEO];
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`abs t <= inv eps / &2`; `&1024 <= inv eps`;
        `sqrt(&2) * log(&2) <= &2`; `&0 <= sqrt(&2) * log(&2)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the sides of the rescaled central sphere *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\y:real^3. (e:real^3->A)(c % y)`] LSP_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\y:real^3. (e:real^3->A)(c % y)`] LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(SPEC `&3 / &4` th) THEN MP_TAC(SPEC `&4 / &3` th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real^3->A`; `c:real`] APXF_SPHERE_SCALE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  (* the level sphere lies in the neck domain; the slabs miss it *)
  SUBGOAL_THEN `sphere(vec 0,c) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `apx_slab (t - &1) (t + &1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; apx_slab; annulus; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "c" THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) t SUBSET rfs_neck_dom eps /\
                apx_slab t (inv eps) SUBSET rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (apx_slab (--inv eps) t) (sphere(vec 0,c)) /\
                DISJOINT (apx_slab t (inv eps)) (sphere(vec 0,c))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; apx_slab; annulus; IN_ELIM_THM;
                IN_SPHERE_0] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lsp_side top (\y:real^3. (e:real^3->A)(c % y)) (&3 / &4)`;
                        `lsp_side top (\y:real^3. (e:real^3->A)(c % y)) (&4 / &3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`e:real^3->A`; `c:real`] APXF_SPHERE_SCALE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[lsp_side; APXF_COMPONENT_CLOSURE];
    MP_TAC(SPECL [`e:real^3->A`; `c:real`] APXF_SPHERE_SCALE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[lsp_side; APXF_COMPONENT_CLOSURE];
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `&3 / &4`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab (--inv eps) t`]
                    MFD_PARAM_IMAGE_SUBSET) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab (--inv eps) t`;
                     `sphere(vec 0:real^3,c)`] APX21_PARAM_IMAGE_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A)(c % &3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `~(&3 / &4 % basis 1:real^3 = vec 0)` ASSUME_TAC THENL
       [SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN EXPAND_TAC "c" THEN
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN
      MP_TAC APXF_SVAL_REF THEN ASM_REAL_ARITH_TAC];
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `&4 / &3`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab t (inv eps)`]
                    MFD_PARAM_IMAGE_SUBSET) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab t (inv eps)`;
                     `sphere(vec 0:real^3,c)`] APX21_PARAM_IMAGE_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A)(c % &4 / &3 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `~(&4 / &3 % basis 1:real^3 = vec 0)` ASSUME_TAC THENL
       [SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN EXPAND_TAC "c" THEN
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN
      MP_TAC APXF_SVAL_REF THEN ASM_REAL_ARITH_TAC]]);;

(* A point z on the negative side of the central sphere, off the middle two *)
(* thirds of the neck, lies on the lower side of every level sphere of      *)
(* level |t| <= 1/(2 eps).                                                   *)

let APXF_LEVEL_SEP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) t z.
     hausdorff_space top /\ apx_sphere_sep top atlas /\ rfs_neck (top,atlas) g eps x e /\
     eps <= &1 / &1024 /\ abs t <= inv(&2 * eps) /\
     apx_neg_side top e z /\
     ~(z IN IMAGE e (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps)))
     ==> ?L U. closed_in top (IMAGE e (sphere(vec 0,exp(t / sqrt(&2))))) /\
               L SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               U SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
               DISJOINT L U /\
               IMAGE e (apx_slab (--inv eps) t) SUBSET L /\
               IMAGE e (apx_slab t (inv eps)) SUBSET U /\
               (!K. connected_in top K /\
                    K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
                    ~(K INTER L = {})
                    ==> K SUBSET L) /\
               (!K. connected_in top K /\
                    K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,exp(t / sqrt(&2)))) /\
                    ~(K INTER U = {})
                    ==> K SUBSET U) /\
               z IN L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t <= inv eps / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `abs t <= inv(&2 * eps)` THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  (* the sides of level t and of the central sphere (level 0) *)
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `eps:real`; `x:A`; `e:real^3->A`; `t:real`] APXF_LEVEL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:A->bool` (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `exp(&0 / sqrt(&2)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `eps:real`; `x:A`; `e:real^3->A`; `&0`] APXF_LEVEL_SIDES) THEN
  ASM_REWRITE_TAC[REAL_ABS_0] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `L0:A->bool` (X_CHOOSE_THEN `U0:A->bool` STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC [`L:A->bool`; `U:A->bool`] THEN ASM_REWRITE_TAC[] THEN
  (* the negative side of the central sphere *)
  SUBGOAL_THEN `mfd_neck_chart top atlas (e:real^3->A)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> b SUBSET c ==> a SUBSET c`) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
                LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&3 / &4` o CONJUNCT2) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN lsp_side top (e:real^3->A) (&3 / &4)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_neg_side top (e:real^3->A) z` THEN
    REWRITE_TAC[apx_neg_side; lsp_side; IN];
    ALL_TAC] THEN
  ABBREV_TAC `Neg = lsp_side top (e:real^3->A) (&3 / &4)` THEN
  SUBGOAL_THEN `~(&3 / &4 % basis 1:real^3 = vec 0)` ASSUME_TAC THENL
   [SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC APXF_SVAL_REF THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Neg:A->bool) SUBSET L0` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `L0:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET L0`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = exp(t / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= t` THENL
   [(* t >= 0: Neg misses the level sphere *)
    SUBGOAL_THEN `DISJOINT (Neg:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,c)))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&1 <= c /\ c < exp(inv eps / sqrt(&2))` STRIP_ASSUME_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `exp(t / sqrt(&2)) = c`)) THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `!y:real^3. norm y = c ==> norm y = &1 \/ y IN apx_slab (&0) (inv eps)`
      ASSUME_TAC THENL
       [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
        REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
        UNDISCH_TAC `c < exp(inv eps / sqrt(&2))` THEN UNDISCH_TAC `&1 <= c` THEN
        REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_SPHERE_0] THEN
      X_GEN_TAC `p:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(Neg:A->bool) SUBSET topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
        UNDISCH_TAC `(p:A) IN Neg` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE; IN_SPHERE_0] THEN ASM_MESON_TAC[];
        SUBGOAL_THEN `(p:A) IN U0` ASSUME_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
            concl th = `IMAGE (e:real^3->A) (apx_slab (&0) (inv eps)) SUBSET U0`)) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          MAP_EVERY UNDISCH_TAC [`DISJOINT (L0:A->bool) U0`; `(Neg:A->bool) SUBSET L0`;
                                 `(p:A) IN Neg`; `(p:A) IN U0`] THEN
          SET_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Neg:A->bool) SUBSET L` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `L:A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(Neg:A->bool) SUBSET topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))`;
          `DISJOINT (Neg:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,c)))`] THEN
        SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (e:real^3->A) (apx_slab (--inv eps) t) SUBSET L`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `(z:A) IN Neg` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* t < 0: Neg lies in L UNION X, X the in-neck slab between t - 1 and 0 *)
  ABBREV_TAC `X = IMAGE (e:real^3->A) (apx_slab (t - &1) (&0))` THEN
  SUBGOAL_THEN `apx_slab (t - &1) (&0) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Neg:A->bool) SUBSET L UNION X` MP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `Neg:A->bool`; `L UNION X:A->bool`] APX22_CLOPEN_SPLIT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN
        MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
      SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp((t - &1) / sqrt(&2)) /\
                    exp((t - &1) / sqrt(&2)) < c /\ c < &1 /\
                    exp(--inv(sqrt(&2) * eps)) < exp((t - &1) / sqrt(&2)) /\
                    &1 < exp(inv(sqrt(&2) * eps))` STRIP_ASSUME_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `exp(t / sqrt(&2)) = c`)) THEN
        SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
          REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `--(inv eps / sqrt(&2)) = --inv eps / sqrt(&2)` SUBST1_TAC THENL
           [REWRITE_TAC[real_div; REAL_MUL_LNEG]; ALL_TAC] THEN
          REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_DIV THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `top closure_of X SUBSET
                    IMAGE (e:real^3->A)
                      (cball(vec 0,&1) DIFF ball(vec 0,exp((t - &1) / sqrt(&2))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
         [EXPAND_TAC "X" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0;
                      IN_BALL_0] THEN
          REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
            REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; rfs_neck_dom; annulus;
                        IN_ELIM_THM] THEN
            ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (e:real^3->A)
                      (cball(vec 0,&1) DIFF ball(vec 0,exp((t - &1) / sqrt(&2))))
                    SUBSET IMAGE e (sphere(vec 0,&1)) UNION X UNION L` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT;
                    IN_UNION] THEN
        X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
        ASM_CASES_TAC `norm(y:real^3) = &1` THENL
         [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
          ALL_TAC] THEN
        ASM_CASES_TAC `norm(y:real^3) = exp((t - &1) / sqrt(&2))` THENL
         [DISJ2_TAC THEN DISJ2_TAC THEN
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
            concl th = `IMAGE (e:real^3->A) (apx_slab (--inv eps) t) SUBSET L`)) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          DISJ2_TAC THEN DISJ1_TAC THEN EXPAND_TAC "X" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
          REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REWRITE_TAC[GSYM real_div] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (e:real^3->A) (sphere(vec 0,c)) SUBSET X` ASSUME_TAC THENL
       [EXPAND_TAC "X" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0; apx_slab; annulus; IN_ELIM_THM] THEN
        REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REWRITE_TAC[GSYM real_div] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_OF_UNION] THEN
      MAP_EVERY UNDISCH_TAC
       [`top closure_of L SUBSET L UNION IMAGE (e:real^3->A) (sphere(vec 0,c))`;
        `IMAGE (e:real^3->A) (sphere(vec 0,c)) SUBSET X`;
        `top closure_of X SUBSET
         IMAGE (e:real^3->A) (cball(vec 0,&1) DIFF ball(vec 0,exp((t - &1) / sqrt(&2))))`;
        `IMAGE (e:real^3->A) (cball(vec 0,&1) DIFF ball(vec 0,exp((t - &1) / sqrt(&2))))
         SUBSET IMAGE e (sphere(vec 0,&1)) UNION X UNION L`;
        `(Neg:A->bool) SUBSET topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1))`] THEN
      SET_TAC[];
      MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN EXPAND_TAC "X" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* z is not in X, so it is in L *)
  SUBGOAL_THEN `~((z:A) IN X)` MP_TAC THENL
   [EXPAND_TAC "X" THEN DISCH_TAC THEN
    UNDISCH_TAC `~((z:A) IN IMAGE (e:real^3->A)
                     (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps)))` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s. (s:A->bool) SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (t - &1) (&0))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(z:A) IN Neg` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Curves from z to the upper part of the neck: first exits,                 *)
(* lifts on general intervals, the crossing of a level sphere and the length *)
(* of the final piece.                                                       *)
(* ------------------------------------------------------------------------- *)

(* The first time a continuous curve on [a,b] leaves an open set (GRGD_FIRST_TIME *)
(* on a general interval).                                                        *)

let APXF_FIRST_TIME = prove
 (`!top (gamma:real->A) B a b.
        continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
        open_in top B /\ a <= b /\ gamma a IN B /\
        (?t. t IN real_interval[a,b] /\ ~(gamma t IN B))
        ==> ?t1. a < t1 /\ t1 <= b /\ ~(gamma t1 IN B) /\
                 !s. a <= s /\ s < t1 ==> gamma s IN B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_closed {s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `{s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)} =
      {s | s IN topspace (subtopology euclideanreal (real_interval[a,b])) /\
           gamma s IN topspace top DIFF B}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      X_GEN_TAC `s:real` THEN
      ASM_CASES_TAC `s IN real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(gamma:real->A) s IN topspace top` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC
       `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                       (gamma:real->A)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~({s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)} = {}) /\
    !x. x IN {s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)}
        ==> a <= x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t1. t1 IN {s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)} /\
         !s. s IN {s | s IN real_interval[a,b] /\ ~(gamma s IN B)} ==> t1 <= s`
  MP_TAC THENL
   [EXISTS_TAC
     `inf {s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CLOSED_CONTAINS_INF THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC
       `{s | s IN real_interval[a,b] /\ ~((gamma:real->A) s IN B)}` INF) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN B)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(gamma:real->A) s IN B` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* APX_NECK_LIFT_SVAL on a general interval [a,b]. *)

let APXF_NECK_LIFT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y gamma a b.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
        y IN rfs_neck_dom eps /\
        mfd_c1_curve (top,atlas) gamma a b /\ gamma a = e y /\
        (!t. a <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps))
        ==> ?v. v IN rfs_neck_dom eps /\ gamma b = e v /\
                sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
                abs(apx_sval v - apx_sval y) <= mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `gamma:real->A`; `a:real`; `b:real`]
                MFD_PARAM_C1_CURVE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(c:real->real^3) a IN rfs_neck_dom eps /\ (gamma:real->A) a = e(c a) /\
    c b IN rfs_neck_dom eps /\ gamma b = e(c b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^3) a = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(c:real->real^3) b` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `c:real->real^3`; `a:real`; `b:real`] APX_NECK_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `c:real->real^3`; `a:real`; `b:real`]
                APX_SVAL_LENGTH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^3^3) gamma a b =
    mfd_length atlas g ((e:real^3->A) o c) a b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                         (c:real->real^3) a b` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* A curve on [a,b] that lies in a closed set before t1 is in it at t1. *)

let APXF_REAL_CLOSED_LEFT = prove
 (`!S a t. real_closed S /\ a < t /\ (!s. a <= s /\ s < t ==> s IN S) ==> t IN S`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(t:real) IN S` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `real_closed (S:real->bool)` THEN
  REWRITE_TAC[real_closed; real_open; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max a (t - e / &2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max a (t - e / &2)`) THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> p) ==> (b ==> ~p) ==> F`) THEN
  ASM_REAL_ARITH_TAC);;

let APXF_CLOSED_LEFT_CURVE = prove
 (`!top (gamma:real->A) C a b t1.
        continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
        closed_in top C /\ a < t1 /\ t1 <= b /\
        (!s. a <= s /\ s < t1 ==> gamma s IN C)
        ==> gamma t1 IN C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 IN {s | s IN real_interval[a,b] /\ (gamma:real->A) s IN C}`
   (fun th -> MP_TAC th THEN SIMP_TAC[IN_ELIM_THM]) THEN
  MATCH_MP_TAC APXF_REAL_CLOSED_LEFT THEN EXISTS_TAC `a:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `{s | s IN real_interval[a,b] /\ (gamma:real->A) s IN C} =
      {s | s IN topspace (subtopology euclideanreal (real_interval[a,b])) /\
           gamma s IN C}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The level of a point of norm exp(t / sqrt 2) is t. *)

let APXF_SVAL_NORM_EXP = prove
 (`!(y:real^3) t. norm y = exp(t / sqrt(&2)) ==> apx_sval y = t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN
  MATCH_MP_TAC(REAL_FIELD `~(s = &0) ==> s * t / s = t`) THEN
  SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH; REAL_LT_IMP_NZ]);;

(* A curve from z (negative side, off the middle two thirds) to a point of  *)
(* the neck above the level t meets the level sphere, and from its last     *)
(* visit on it is at least sqrt(1 - eps) h (s(q) - t) long.                 *)

let APXF_CROSS_LENGTH = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) t z yq (c:real->A) a b.
     hausdorff_space top /\ apx_sphere_sep top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024 /\ abs t <= inv(&2 * eps) /\
     apx_neg_side top e z /\
     ~(z IN IMAGE e (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps))) /\
     yq IN rfs_neck_dom eps /\ t < apx_sval yq /\
     mfd_c1_curve (top,atlas) c a b /\ c a = z /\ c b = e yq
     ==> ?tau v. a <= tau /\ tau <= b /\ norm v = exp(t / sqrt(&2)) /\ c tau = e v /\
                 sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) * (apx_sval yq - t)
                 <= mfd_length atlas g c tau b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ eps < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t <= inv eps / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `abs t <= inv(&2 * eps)` THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `~(yq:real^3 = vec 0) /\ abs(apx_sval yq) < inv eps` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SVAL_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `eps:real`; `x:A`; `e:real^3->A`; `t:real`; `z:A`] APXF_LEVEL_SEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:A->bool` (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,exp(t / sqrt(&2))))` THEN
  SUBGOAL_THEN `a <= b /\
                continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                               (c:real->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (c:real->A) a b` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> (c:real->A) s IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  (* q lies on the upper side *)
  SUBGOAL_THEN `(e:real^3->A) yq IN U` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE (e:real^3->A) (apx_slab t (inv eps)) SUBSET U`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the image of a final piece of the curve is connected *)
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> connected_in top (IMAGE (c:real->A) (real_interval[s,b]))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curve meets S *)
  SUBGOAL_THEN `?s0. a <= s0 /\ s0 <= b /\ (c:real->A) s0 IN S` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
    SUBGOAL_THEN `IMAGE (c:real->A) (real_interval[a,b]) SUBSET L` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `L:A->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
            can (find_term (fun t -> t = `S:A->bool`)) (concl th))) THEN
          MAP_EVERY UNDISCH_TAC [`a <= s:real`; `s <= b:real`] THEN CONV_TAC TAUT];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
        EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      UNDISCH_TAC `DISJOINT (L:A->bool) U` THEN UNDISCH_TAC `(e:real^3->A) yq IN U` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the last time on S *)
  SUBGOAL_THEN `~((c:real->A) b IN S)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `U SUBSET topspace top DIFF S:A->bool` THEN
    UNDISCH_TAC `(e:real^3->A) yq IN U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 < b:real` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `s0 <= b /\ ~(s0 = b) ==> s0 < b`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real->A`; `a:real`; `s0:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real->A`;
                 `s0:real`; `b:real`; `S:A->bool`] APXS_LAST_IN_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?v:real^3. norm v = exp(t / sqrt(&2)) /\ (c:real->A) tau = e v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real->A) tau IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`tau:real`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* after tau the curve is on the upper side *)
  SUBGOAL_THEN `!s. tau < s /\ s <= b ==> (c:real->A) s IN U` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (c:real->A) (real_interval[s,b]) SUBSET U` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `U:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
        EXISTS_TAC `(e:real^3->A) yq` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* in-neck points of U are above the level t *)
  SUBGOAL_THEN `!y. y IN rfs_neck_dom eps /\ (e:real^3->A) y IN U ==> t < apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `apx_sval y < t` THENL
     [SUBGOAL_THEN `(e:real^3->A) y IN L` MP_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (e:real^3->A) (apx_slab (--inv eps) t) SUBSET L`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `DISJOINT (L:A->bool) U` THEN UNDISCH_TAC `(e:real^3->A) y IN U` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `apx_sval y = t` THENL
     [SUBGOAL_THEN `(e:real^3->A) y IN S` MP_TAC THENL
       [EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0] THEN
        UNDISCH_TAC `apx_sval y = t` THEN REWRITE_TAC[apx_sval] THEN DISCH_TAC THEN
        SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
        SUBGOAL_THEN `log(norm(y:real^3)) = t / sqrt(&2)` ASSUME_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
           [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * l) / s = l`];
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[EXP_LOG];
        UNDISCH_TAC `U SUBSET topspace top DIFF S:A->bool` THEN
        UNDISCH_TAC `(e:real^3->A) y IN U` THEN SET_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the first exit from the slab between t - 1 and s(q) after tau *)
  SUBGOAL_THEN `apx_slab (t - &1) (apx_sval yq) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `O = IMAGE (e:real^3->A) (apx_slab (t - &1) (apx_sval yq))` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(v:real^3) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC APXF_SVAL_NORM_EXP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN apx_slab (t - &1) (apx_sval yq)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real->A) b IN O)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `yq:real^3 = y'` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `e:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      UNDISCH_TAC `(y':real^3) IN apx_slab (t - &1) (apx_sval y')` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real->A`; `s0:real`; `tau:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[tau,b]),top)
                               (c:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (c:real->A) tau b` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `c:real->A`; `O:A->bool`; `tau:real`; `b:real`]
                APXF_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
  (* the exit point lies in the closed slab, at the level s(q) *)
  ABBREV_TAC `K = cball(vec 0:real^3,exp(apx_sval yq / sqrt(&2))) DIFF
                  ball(vec 0,exp((t - &1) / sqrt(&2)))` THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; rfs_neck_dom; annulus; IN_ELIM_THM;
                REAL_NOT_LT] THEN
    SUBGOAL_THEN `exp(--inv(sqrt(&2) * eps)) < exp((t - &1) / sqrt(&2)) /\
                  exp(apx_sval yq / sqrt(&2)) < exp(inv(sqrt(&2) * eps))` MP_TAC THENL
     [SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `--(inv eps / sqrt(&2)) = --inv eps / sqrt(&2)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LNEG]; ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:A->bool) SUBSET IMAGE (e:real^3->A) K` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->A) t1 IN IMAGE (e:real^3->A) K` MP_TAC THENL
   [MATCH_MP_TAC APXF_CLOSED_LEFT_CURVE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `tau:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `(O:A->bool) SUBSET IMAGE (e:real^3->A) K` THEN
      MATCH_MP_TAC(SET_RULE `(x:A) IN s ==> s SUBSET t ==> x IN t`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t < apx_sval(y1:real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_sval`)) (concl th) &&
      can (find_term (fun t -> t = `U:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real->A) t1 = (e:real^3->A) y1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(y1:real^3) = apx_sval yq` ASSUME_TAC THENL
   [SUBGOAL_THEN `~((y1:real^3) IN apx_slab (t - &1) (apx_sval yq))` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((c:real->A) t1 IN O)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y1:real^3) IN K` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT; apx_slab; annulus; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `norm(y1:real^3) = exp((t - &1) / sqrt(&2)) \/
                  norm(y1:real^3) = exp(apx_sval yq / sqrt(&2))` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `apx_sval(y1:real^3) = t - &1` ASSUME_TAC THENL
       [MATCH_MP_TAC APXF_SVAL_NORM_EXP THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC APXF_SVAL_NORM_EXP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the lift on [tau, t1] and the length bound *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real->A`; `tau:real`; `t1:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `v:real^3`; `c:real->A`; `tau:real`;
                 `t1:real`] APXF_NECK_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = t1:real` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(c:real->A) s IN O` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN MATCH_MP_TAC(SET_RULE
          `(s:real^3->bool) SUBSET t ==> (x:A) IN IMAGE e s ==> x IN IMAGE e t`) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v':real^3 = y1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real->A`; `t1:real`; `b:real`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
               abs(apx_sval(y1:real^3) - apx_sval(v:real^3)) <=
               mfd_length atlas g (c:real->A) tau t1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval(yq:real^3) - t) = apx_sval yq - t` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The headline |- !u. APX_A9_CRUDE_STATEMENT u.                             *)
(* ------------------------------------------------------------------------- *)

(* MT Lemma A.9, crude form. *)

let APXF_A9_CRUDE = prove
 (`!u:A->bool. APX_A9_CRUDE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A9_CRUDE_STATEMENT] THEN
  X_GEN_TAC `alpha:real` THEN STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &1024) (alpha / &2)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `z:A`; `w:real^3`; `r1:real`;
    `r2:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ eps < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = apx_sval(r1 % w:real^3)` THEN
  ABBREV_TAC `sq = apx_sval(r2 % w:real^3)` THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th1; th2]) THEN ASSUME_TAC th1 THEN ASSUME_TAC th2)) THEN
  SUBGOAL_THEN `(r1 % w:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_SLAB_SUB_DOM THEN REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t <= inv(&2 * eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `(r1 % w:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 <= alpha * (sq - t) /\ &0 < sq - t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `&16 / alpha`))
                                                 (concl th))) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < alpha`];
      FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `&16 / alpha`))
                                                 (concl th))) THEN
      SUBGOAL_THEN `&0 < &16 / alpha` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* constants *)
  SUBGOAL_THEN `&1 - eps <= sqrt(&1 - eps) /\ sqrt(&1 + eps) <= &1 + eps /\
                sqrt(&1 + eps) * (sqrt(&2) * pi) <= &5 /\ &0 <= sqrt(&1 + eps)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC[REAL_POW_2; REAL_ARITH `(&1 - e) * (&1 - e) = &1 - e - e * (&1 - e)`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a - x <= a`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2; REAL_ARITH `(&1 + e) * (&1 + e) = (&1 + e) + e * (&1 + e)`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + &1 / &1024) * &24 / &5` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[APX_SQRT2_PI] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]];
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * (sq - t) <= alpha / &2 * (sq - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - eps) * (sq - t) <= sqrt(&1 - eps) * (sq - t) /\
                sqrt(&1 + eps) * (sq - t) <= (&1 + eps) * (sq - t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* in-neck distances from p and the joinability of z and q *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `r1 % w:real^3`; `r2 % w:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (z:A) ((e:real^3->A)(r2 % w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(e:real^3->A)(r1 % w)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - sq) = sq - t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the lower bound, curve by curve *)
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:A->real^3^3) z ((e:real^3->A)(r1 % w)) -
      sqrt(&1 + eps) * h * (sqrt(&2) * pi) + sqrt(&1 - eps) * h * (sq - t)
      <= mfd_dist (top,atlas) g z (e(r2 % w))`
    MP_TAC THENL
     [MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `gam:real->A` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                    `eps:real`; `x:A`; `e:real^3->A`; `t:real`; `z:A`; `r2 % w:real^3`;
                    `gam:real->A`; `&0`; `&1`] APXF_CROSS_LENGTH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `tau:real` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `gam:real->A`; `&0`; `tau:real`; `&1`] MFD_LENGTH_COMBINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `gam:real->A`; `&0`; `tau:real`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `apx_sval(v:real^3) = t` ASSUME_TAC THENL
       [MATCH_MP_TAC APXF_SVAL_NORM_EXP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
        EXISTS_TAC `apx_slab (--inv eps) (inv eps)` THEN CONJ_TAC THENL
         [REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
            UNDISCH_TAC `abs t <= inv(&2 * eps)` THEN REWRITE_TAC[REAL_INV_MUL] THEN
            ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC APX_SLAB_SUB_DOM THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `x:A`; `e:real^3->A`; `v:real^3`; `r1 % w:real^3`]
                    APX_NECK_DIST_UPPER) THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `gam:real->A`; `&0`; `tau:real`] MFD_C1_CURVE_JOINABLE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `z:A`; `(e:real^3->A) v`; `(e:real^3->A)(r1 % w)`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sqrt(&1 - eps) * h * (sq - t) <= mfd_length atlas (g:A->real^3^3) gam tau (&1)` THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - alpha) * (sq - t) <=
                  sqrt(&1 - eps) * (sq - t) - sqrt(&1 + eps) * (sqrt(&2) * pi)` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(&1 - eps) * (sq - t) <= sqrt(&1 - eps) * (sq - t)`;
        `eps * (sq - t) <= alpha / &2 * (sq - t)`;
        `sqrt(&1 + eps) * (sqrt(&2) * pi) <= &5`; `&16 <= alpha * (sq - t)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`h:real`; `(&1 - alpha) * (sq - t)`;
                  `sqrt(&1 - eps) * (sq - t) - sqrt(&1 + eps) * (sqrt(&2) * pi)`]
                 REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    (* the upper bound *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `z:A`; `(e:real^3->A)(r1 % w)`; `(e:real^3->A)(r2 % w)`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(&1 + eps) * ((sq - t) + sqrt(&2) * pi) <= (&1 + alpha) * (sq - t)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`sqrt(&1 + eps) * (sq - t) <= (&1 + eps) * (sq - t)`;
        `eps * (sq - t) <= alpha / &2 * (sq - t)`;
        `sqrt(&1 + eps) * (sqrt(&2) * pi) <= &5`; `&16 <= alpha * (sq - t)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`h:real`; `sqrt(&1 + eps) * ((sq - t) + sqrt(&2) * pi)`;
                  `(&1 + alpha) * (sq - t)`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A)(r1 % w)) (e(r2 % w)) <=
                 sqrt(&1 + eps) * h * ((sq - t) + sqrt(&2) * pi)` THEN
    REAL_ARITH_TAC]);;

