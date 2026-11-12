(* ========================================================================= *)
(* pc_apx_ncends: proof of APX_A25_NC_ENDS_STATEMENT (pc_apx_ncreq), the     *)
(* relative end structure for MT Lemma 11.30.  W a component of M with R    *)
(* proper on W, a point of W with R <= L, every point of W with R > L an    *)
(* NK-neck centre or a cap core.  One horn per noncompact component X_a of  *)
(* the set of points of W with R >= (5/4) C L: no cap cores in X_a (a       *)
(* capped horn would be all of W, where R > L), two-sided growth of a chain  *)
(* of X_a-centred NK-necks from a frontier point (exactly one side          *)
(* infinite), truncation after the last centre below (3/2) C L, and the     *)
(* chain chart of pc_apx_chcore.  Finitely many such components by packing; *)
(* the rest is compact by properness of R.                                  *)
(* ========================================================================= *)

needs "src/pc_apx_chcore.ml";;
needs "src/pc_apx_ncreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Generic facts.  The scalar curvature on a neck is within a               *)
(* factor 1 +/- 1/100 of its value at the centre (small eps); components of *)
(* a manifold are open, closed and connected, and necks and caps meeting a  *)
(* component lie in it; a set of indices of a chain whose centres lie in a  *)
(* compact set is finite.                                                    *)
(* ------------------------------------------------------------------------- *)

let APXN_NECK_SCALAR_GEN = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y d.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps /\
        abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1) <= d
        ==> (&1 - d) * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= (&1 + d) * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y) /
                   mfd_scalar atlas g x - &1) <= d` THEN
  UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y)`,`a:real`) THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) x`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a / b - &1 = (a - b) / b` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `abs((a - b) / b) <= d` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < b ==> abs b = b`; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let APXN_NECK_RATIO = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps0 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &100`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `&1 / &100`]
                APXN_NECK_SCALAR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REAL_ARITH_TAC]);;

let APXN_COMPONENT_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W.
     smooth_manifold_atlas top atlas /\ W IN connected_components_of top
     ==> open_in top W /\ closed_in top W /\ connected_in top W /\ W SUBSET topspace top /\
         ~(W = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF; CONNECTED_IN_CONNECTED_COMPONENTS_OF;
               CONNECTED_COMPONENTS_OF_SUBSET] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]]);;

let APXN_NECK_IN_COMPONENT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) W.
     rfs_neck (top,atlas) g eps x e /\ W IN connected_components_of top /\ x IN W
     ==> IMAGE e (rfs_neck_dom eps) SUBSET W`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[]]);;

let APXN_CAP_IN_COMPONENT = prove
 (`!top atlas (g:A->real^3^3) C eps U Y W.
     rfs_cap (top,atlas) g C eps U Y /\ W IN connected_components_of top /\
     ~DISJOINT U W
     ==> U SUBSET W`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX21_CAP_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `C:real`; `eps:real`; `Y:A->bool`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[DISJOINT_SYM]]);;
let APXN_CHAIN_FINITE_SUB = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) (S:int->bool) K.
     apx_ch_ctx top atlas g eps /\ apx_chain (top,atlas) g eps Ix x e /\
     S SUBSET Ix /\ compact_in top K /\ (!i. i IN S ==> x i IN K)
     ==> FINITE S`,
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
   `!i j. i IN S /\ j IN S /\ mfd_joinable (top,atlas) ((x:int->A) i) (x j) /\
          mfd_dist (top,atlas) (g:A->real^3^3) (x i) (x j) < r ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:int) IN Ix /\ (j:int) IN Ix` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
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
  SUBGOAL_THEN `!i. i IN S ==> ?B. B IN V /\ (x:int->A) i IN B` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:int->A) i IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\i. @B. B IN V /\ (x:int->A) i IN B) (S:int->bool))` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN S`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:int`; `j:int`] THEN BETA_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B0 = @B. B IN V /\ (x:int->A) i IN B` THEN
  SUBGOAL_THEN `B0 IN V /\ (x:int->A) i IN B0 /\ x j IN B0` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:int) IN S`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(j:int) IN S`) o check (fun th ->
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
(* Shifting and reversing chains of arbitrary index sets.                   *)
(* ------------------------------------------------------------------------- *)

let APXN_CHAIN_SHIFT_GEN = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) a.
     apx_chain (top,atlas) g eps Ix x e
     ==> apx_chain (top,atlas) g eps {i:int | i + a IN Ix} (\i. x(i + a)) (\i. e(i + a)) /\
         apx_chain_union eps {i:int | i + a IN Ix} (\i. e(i + a)) =
         apx_chain_union eps Ix e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain; apx_int_interval; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "iv") (CONJUNCTS_THEN2 (LABEL_TAC "ne")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))))) THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:int`; `j:int`; `k:int`] THEN STRIP_TAC THEN
    USE_THEN "iv" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`i + a:int`; `k + a:int`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    USE_THEN "ne" MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN EXISTS_TAC `i - a:int` THEN
    ASM_REWRITE_TAC[INT_SUB_ADD];
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN BETA_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[INT_ARITH `(i + &1) + a:int = (i + a) + &1`] THEN
    USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((i:int) + &1) + a IN Ix` THEN REWRITE_TAC[INT_ARITH `(i + &1) + a:int = (i + a) + &1`];
    MAP_EVERY X_GEN_TAC [`a':int`; `i:int`] THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "c2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[apx_chain_union] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i + a:int` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i - a:int` THEN ASM_REWRITE_TAC[INT_SUB_ADD]]]);;

let APXN_CHAIN_SHIFT_UP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) a.
     apx_chain (top,atlas) g eps {i:int | a <= i} x e
     ==> apx_chain (top,atlas) g eps {i:int | &0 <= i} (\i. x(i + a)) (\i. e(i + a)) /\
         apx_chain_union eps {i:int | &0 <= i} (\i. e(i + a)) =
         apx_chain_union eps {i:int | a <= i} e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `a:int` o MATCH_MP APXN_CHAIN_SHIFT_GEN) THEN
  SUBGOAL_THEN `{i:int | i + a IN {i | a <= i}} = {i | &0 <= i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; REWRITE_TAC[]]);;

let APXN_CHAIN_REV = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A).
     riemannian_metric atlas g /\ apx_chain (top,atlas) g eps Ix x e
     ==> apx_chain (top,atlas) g eps {i:int | --i IN Ix} (\i. x(--i))
                   (\i. apx_rev(e(--i))) /\
         apx_chain_union eps {i:int | --i IN Ix} (\i. apx_rev(e(--i))) =
         apx_chain_union eps Ix e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain; apx_int_interval; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "iv")
    (CONJUNCTS_THEN2 (LABEL_TAC "ne")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")))))) THEN
  REWRITE_TAC[APX_REV_IMAGE_SLAB; APX_REV_IMAGE_DOM; REAL_NEG_NEG] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:int`; `j:int`; `k:int`] THEN STRIP_TAC THEN
    USE_THEN "iv" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`--k:int`; `--i:int`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    USE_THEN "ne" MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN EXISTS_TAC `--i:int` THEN
    ASM_REWRITE_TAC[INT_NEG_NEG];
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC APX_REV_NECK THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "c1" (MP_TAC o SPEC `--(i + &1):int`) THEN
    REWRITE_TAC[INT_ARITH `--(i + &1) + &1:int = --i`] THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`a':int`; `i:int`] THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "c2" (MP_TAC o SPECL [`--i:int`; `--a':int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SET_TAC[]];
    REWRITE_TAC[apx_chain_union] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; APX_REV_IMAGE_DOM] THEN
    X_GEN_TAC `t:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--i:int` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--i:int` THEN ASM_REWRITE_TAC[INT_NEG_NEG]]]);;
(* A family of necks every point of whose union lies in the deep part of    *)
(* one of them has a closed union (the argument of APX_A15_CORE: a limit    *)
(* point lies in the ball of a deep point, inside its neck).               *)

let APXN_DEEP_CLOSED = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\
     (!i. i IN Ix ==> rfs_neck (top,atlas) g eps (x i) (e i)) /\
     (!q. q IN apx_chain_union eps Ix e
          ==> ?i z. i IN Ix /\ z IN rfs_neck_dom eps /\ e i z = q /\
                    abs(apx_sval z) <= &7 / &8 * inv eps - &10)
     ==> closed_in top (apx_chain_union eps Ix e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "dp"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union eps Ix (e:int->real^3->A)` THEN
  SUBGOAL_THEN `U SUBSET topspace (top:A topology)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[apx_chain_union; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "nk" (MP_TAC o C MATCH_MP (ASSUME `(i:int) IN Ix`)) THEN SIMP_TAC[rfs_neck];
      STRIP_TAC THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
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
  SUBGOAL_THEN `!q:A. q IN U /\ q IN O ==> F` ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    USE_THEN "dp" (MP_TAC o C MATCH_MP (ASSUME `(q:A) IN U`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `~((p:A) IN U)` THEN REWRITE_TAC[] THEN
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
    MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `inv eps / &8 + &10 <= inv eps - abs(apx_sval(z:real^3))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN top closure_of U` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
  DISCH_THEN(MP_TAC o SPEC `O:A->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
(* Frontiers of one-sided infinite chains with an arbitrary first or last   *)
(* index; a bi-infinite chain has a closed union.                           *)

let APXN_UP_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) a.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | a <= i} x e
     ==> top frontier_of (apx_chain_union eps {i:int | a <= i} e) SUBSET
         top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:int->A`; `e:int->real^3->A`; `a:int`] APXN_CHAIN_SHIFT_UP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `\i. (x:int->A)(i + a)`; `\i. (e:int->real^3->A)(i + a)`]
                APX_A15_CORE) THEN
  ASM_REWRITE_TAC[INT_ADD_LID]);;

let APXN_DOWN_FRONTIER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) b.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | i <= b} x e
     ==> top frontier_of (apx_chain_union eps {i:int | i <= b} e) SUBSET
         top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (g:A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `{i:int | i <= b}`; `x:int->A`; `e:int->real^3->A`]
                APXN_CHAIN_REV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{i:int | --i IN {i | i <= b}} = {i | --b <= i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `\i. (x:int->A)(--i)`; `\i. apx_rev((e:int->real^3->A)(--i))`;
                 `--b:int`] APXN_UP_FRONTIER) THEN
  ASM_REWRITE_TAC[INT_NEG_NEG; APX_REV_IMAGE_SLAB; REAL_NEG_NEG]);;

let APXN_BI_COVER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) q.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps (:int) x e /\ q IN apx_chain_union eps (:int) e
     ==> ?i z. i IN (:int) /\ z IN rfs_neck_dom eps /\ e i z = q /\
               abs(apx_sval z) <= &7 / &8 * inv eps - &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `q IN apx_chain_union eps (:int) (e:int->real^3->A)` THEN
  REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_TAC `i0:int`) THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | i0 - &1 <= i} x e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX21_SUBCHAIN THEN EXISTS_TAC `(:int)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[apx_int_interval; IN_ELIM_THM] THEN INT_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `i0:int` THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:int->A`; `e:int->real^3->A`; `i0 - &1:int`]
                APXN_CHAIN_SHIFT_UP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `\i. (x:int->A)(i + (i0 - &1))`;
                 `\i. (e:int->real^3->A)(i + (i0 - &1))`; `q:A`] APX_INF_CHAIN_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `i0:int` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `j:int` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`j + (i0 - &1):int`; `z:real^3`] THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  (* the exceptional case: q low in N_(i0 - 1) but also in N_i0 *)
  UNDISCH_TAC `j:int = &0` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ASSUME `apx_chain (top,atlas) (g:A->real^3^3) eps (:int) x e`) THEN
  REWRITE_TAC[apx_chain; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `i0 - &1:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[INT_SUB_ADD] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[SUBSET; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `q IN IMAGE ((e:int->real^3->A)(i0 - &1)) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:int->real^3->A) (&0 + i0 - &1) z = q` THEN
    REWRITE_TAC[INT_ADD_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(i0 - &1))
                         ((e:int->real^3->A)(i0 - &1))` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps (:int) x e` THEN
    REWRITE_TAC[apx_chain; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A)(i0 - &1)`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(i0 - &1))
                          ((e:int->real^3->A)(i0 - &1))` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z':real^3 = z` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `z' IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `apx_slab (--inv(&2 * eps)) (inv eps)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
      SUBGOAL_THEN `inv(&2 * eps) <= inv eps` MP_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN
        SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_MESON_TAC[apx_ch_ctx]; REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[INT_ADD_LID];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN apx_slab (--inv(&2 * eps)) (inv eps)` THEN
  REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1024 <= inv eps` MP_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN
    SUBGOAL_THEN `&0 < eps /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` MP_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APXN_BI_CLOSED = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_chain (top,atlas) g eps (:int) x e
     ==> closed_in top (apx_chain_union eps (:int) e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APXN_DEEP_CLOSED THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                        `x:int->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps (:int) x e` THEN
    SIMP_TAC[apx_chain];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC APXN_BI_COVER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:int->A`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One step of the two-sided growth of a balanced chain of                  *)
(* X-centred NK-necks (MT A.17-A.19): a chain not covering the connected    *)
(* set X has a point of X on its frontier, at the top or at the bottom      *)
(* quarter, and the chain extends there (APX21_EXT_HOLDS, APX_A18_NEG_CORE). *)
(* ------------------------------------------------------------------------- *)

let APXN_CHAIN_UNION_OPEN = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A).
     smooth_manifold_atlas top atlas /\ apx_chain (top,atlas) g eps Ix x e
     ==> open_in top (apx_chain_union eps Ix e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_chain_union] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A) i`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[rfs_neck];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let APXN_NECK_IN_UNION = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) i.
     apx_chain (top,atlas) g eps Ix x e /\ i IN Ix
     ==> IMAGE (e i) (rfs_neck_dom eps) SUBSET apx_chain_union eps Ix e /\
         x i IN apx_chain_union eps Ix e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET apx_chain_union eps Ix e`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_chain_union] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN t ==> s SUBSET UNIONS t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
  REWRITE_TAC[apx_chain] THEN
  DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET apx_chain_union eps Ix e` THEN
  UNDISCH_TAC `(x:int->A) i IN IMAGE ((e:int->real^3->A) i) (sphere(vec 0,&1))` THEN
  SET_TAC[]);;

let APXN_FIN_EXIT = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) a b x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\
     apx_chain (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     ~(X INTER apx_chain_union eps {i:int | a <= i /\ i <= b} e = {}) /\
     ~(X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e)
     ==> (?z (ez:real^3->A). z IN X /\ NK z ez /\
                 z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
                 ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e)) \/
         (?z (ez:real^3->A). z IN X /\ NK z ez /\
                 z IN top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
                 ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
  ABBREV_TAC `U = apx_chain_union eps {i:int | a <= i /\ i <= b} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `X:A->bool`; `U:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`]
                APX_FIN_FRONTIER) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_UNION] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((z:A) IN U)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of U` THEN ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:A) IN X`) o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `NK:A->(real^3->A)->bool`)) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `ez:real^3->A`) THEN
  SUBGOAL_THEN
   `(z:A) IN top closure_of (IMAGE ((e:int->real^3->A) a) (apx_slab (--inv eps) (--inv(&2 * eps)))) \/
    z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps)))`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`z:A`; `ez:real^3->A`] THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`z:A`; `ez:real^3->A`] THEN ASM_REWRITE_TAC[]]);;

let APXN_EXT_UP = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) a b x (e:int->real^3->A) z ez.
     apx21_ext top atlas g eps /\ (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     a <= b /\ apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     NK z ez /\
     z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
     ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e)
     ==> ?ez'. (NK z ez' \/ NK z (apx_rev ez')) /\
               apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b + &1}
                 (\i. if i = b + &1 then z else x i) (\i. if i = b + &1 then ez' else e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `apx21_ext top atlas (g:A->real^3^3) eps` THEN REWRITE_TAC[apx21_ext] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                             `ez:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `ez':real^3->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
  ASM_REWRITE_TAC[APX_REV_REV]);;

let APXN_EXT_DOWN = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) a b x (e:int->real^3->A) z ez.
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     a <= b /\ apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
     NK z ez /\
     z IN top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
     ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e)
     ==> ?ez'. (NK z ez' \/ NK z (apx_rev ez')) /\
               apx_balanced (top,atlas) g eps {i:int | a - &1 <= i /\ i <= b}
                 (\i. if i = a - &1 then z else x i) (\i. if i = a - &1 then ez' else e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                 `ez:real^3->A`] APX_A18_NEG_CORE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `ez':real^3->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
  ASM_REWRITE_TAC[APX_REV_REV]);;
(* The states of the fair two-sided growth: balanced chains a..b with      *)
(* a <= 0 <= b, b - a = n, centre y0 and neck e0 at index 0, centres in X   *)
(* with NK-necks up to orientation; possible extensions at either end; and  *)
(* the step relation (at even steps the bottom end has priority, at odd     *)
(* steps the top end).                                                       *)

let apxn_good = new_definition
 `apxn_good (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
            (eps:real) (NK:A->(real^3->A)->bool) (X:A->bool) (y0:A) (e0:real^3->A)
            (n:num) (a:int) (b:int) (x:int->A) (e:int->real^3->A) <=>
    a <= &0 /\ &0 <= b /\ b - a = &n /\
    apx_balanced (top,atlas) g eps {i:int | a <= i /\ i <= b} x e /\
    x(&0) = y0 /\ e(&0) = e0 /\
    (!i. a <= i /\ i <= b ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i))))`;;

let apxn_upext = new_definition
 `apxn_upext (top:A topology) (eps:real) (NK:A->(real^3->A)->bool) (X:A->bool)
             (a:int) (b:int) (e:int->real^3->A) <=>
    ?z ez. z IN X /\ NK z ez /\
           z IN top closure_of (IMAGE (e b) (apx_slab (inv(&2 * eps)) (inv eps))) /\
           ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e)`;;

let apxn_downext = new_definition
 `apxn_downext (top:A topology) (eps:real) (NK:A->(real^3->A)->bool) (X:A->bool)
               (a:int) (b:int) (e:int->real^3->A) <=>
    ?z ez. z IN X /\ NK z ez /\
           z IN top closure_of (IMAGE (e a) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
           ~(z IN apx_chain_union eps {i:int | a <= i /\ i <= b} e)`;;

let apxn_step = new_definition
 `apxn_step (top:A topology) (eps:real) (NK:A->(real^3->A)->bool) (X:A->bool) (n:num)
            (a:int) (b:int) (x:int->A) (e:int->real^3->A)
            (a':int) (b':int) (x':int->A) (e':int->real^3->A) <=>
    (!i. a <= i /\ i <= b ==> x' i = x i /\ e' i = e i) /\
    ((a' = a - &1 /\ b' = b /\ (EVEN n \/ ~apxn_upext top eps NK X a b e)) \/
     (a' = a /\ b' = b + &1 /\ (~EVEN n \/ ~apxn_downext top eps NK X a b e)))`;;

let APXN_STEP_UP = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 e0 n a b x (e:int->real^3->A).
     apx21_ext top atlas g eps /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     apxn_good top atlas g eps NK X y0 e0 n a b x e /\ apxn_upext top eps NK X a b e
     ==> ?x' e'. apxn_good top atlas g eps NK X y0 e0 (SUC n) a (b + &1) x' e' /\
                 (!i. a <= i /\ i <= b ==> x' i = x i /\ e' i = e i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apxn_good; apxn_upext] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `ez:real^3->A` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `a:int`; `b:int`;
                 `x:int->A`; `e:int->real^3->A`; `z:A`; `ez:real^3->A`] APXN_EXT_UP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\i. if i = b + &1 then z else (x:int->A) i`;
                        `\i. if i = b + &1 then ez' else (e:int->real^3->A) i`] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  SUBGOAL_THEN `~(&0:int = b + &1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = b + &1` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th))) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i:int = b + &1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

let APXN_STEP_DOWN = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 e0 n a b x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_more top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     apxn_good top atlas g eps NK X y0 e0 n a b x e /\ apxn_downext top eps NK X a b e
     ==> ?x' e'. apxn_good top atlas g eps NK X y0 e0 (SUC n) (a - &1) b x' e' /\
                 (!i. a <= i /\ i <= b ==> x' i = x i /\ e' i = e i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apxn_good; apxn_downext] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `ez:real^3->A` STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `a:int`; `b:int`;
                 `x:int->A`; `e:int->real^3->A`; `z:A`; `ez:real^3->A`] APXN_EXT_DOWN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\i. if i = a - &1 then z else (x:int->A) i`;
                        `\i. if i = a - &1 then ez' else (e:int->real^3->A) i`] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  SUBGOAL_THEN `~(&0:int = a - &1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_CASES_TAC `i:int = a - &1` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `X:A->bool`)) (concl th))) THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i:int = a - &1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;
let APXN_STEP_EXISTS = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 e0 n a b x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\ y0 IN X /\
     apxn_good top atlas g eps NK X y0 e0 n a b x e /\
     ~(X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e)
     ==> ?a' b' x' e'. apxn_good top atlas g eps NK X y0 e0 (SUC n) a' b' x' e' /\
                       apxn_step top eps NK X n a b x e a' b' x' e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e /\
                a <= &0 /\ &0 <= b /\ (x:int->A)(&0) = y0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apxn_good top atlas (g:A->real^3^3) eps NK X y0 e0 n a b x e` THEN
    REWRITE_TAC[apxn_good; apx_balanced] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A) \/
                apxn_downext top eps NK X a b e` ASSUME_TAC THENL
   [REWRITE_TAC[apxn_upext; apxn_downext] THEN MATCH_MP_TAC APXN_FIN_EXIT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y0:A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(x:int->A)(&0) = y0`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `{i:int | a <= i /\ i <= b}`; `x:int->A`; `e:int->real^3->A`;
                   `&0:int`] APXN_NECK_IN_UNION) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A)
     ==> ?x' e'. apxn_good top atlas (g:A->real^3^3) eps NK X y0 e0 (SUC n) a (b + &1) x' e' /\
                 (!i. a <= i /\ i <= b ==> x' i = x i /\ e' i = e i)) /\
    (apxn_downext top eps NK X a b e
     ==> ?x' e'. apxn_good top atlas g eps NK X y0 e0 (SUC n) (a - &1) b x' e' /\
                 (!i. a <= i /\ i <= b ==> x' i = x i /\ e' i = e i))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC APXN_STEP_UP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC APXN_STEP_DOWN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[apxn_step] THEN
  ASM_CASES_TAC `EVEN n` THENL
   [ASM_CASES_TAC `apxn_downext top eps NK (X:A->bool) a b (e:int->real^3->A)` THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `apxn_downext top eps NK (X:A->bool) a b (e:int->real^3->A)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_THEN `e':int->real^3->A`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a - &1:int`; `b:int`; `x':int->A`; `e':int->real^3->A`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_THEN `e':int->real^3->A`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a:int`; `b + &1:int`; `x':int->A`; `e':int->real^3->A`] THEN
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A)` THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `apxn_upext top eps NK (X:A->bool) a b (e:int->real^3->A)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_THEN `e':int->real^3->A`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a:int`; `b + &1:int`; `x':int->A`; `e':int->real^3->A`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `apxn_downext top eps NK (X:A->bool) a b (e:int->real^3->A)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `apxn_downext top eps NK (X:A->bool) a b (e:int->real^3->A)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_THEN `e':int->real^3->A`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a - &1:int`; `b:int`; `x':int->A`; `e':int->real^3->A`] THEN
      ASM_REWRITE_TAC[]]]);;
let APXN_GROW_SEQ = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 (e0:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\ y0 IN X /\ NK y0 e0 /\
     (!n a b x e. apxn_good top atlas g eps NK X y0 e0 n a b x e
                  ==> ~(X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e))
     ==> ?(A:num->int) (B:num->int) (XX:num->int->A) (EE:num->int->real^3->A).
           !n. apxn_good top atlas g eps NK X y0 e0 n (A n) (B n) (XX n) (EE n) /\
               apxn_step top eps NK X n (A n) (B n) (XX n) (EE n)
                         (A(SUC n)) (B(SUC n)) (XX(SUC n)) (EE(SUC n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n (s:int#int#(int->A)#(int->real^3->A)).
       apxn_good top atlas (g:A->real^3^3) eps NK X y0 e0 n
                 (FST s) (FST(SND s)) (FST(SND(SND s))) (SND(SND(SND s)))`;
    `\n (s:int#int#(int->A)#(int->real^3->A)) (s':int#int#(int->A)#(int->real^3->A)).
       apxn_step top eps NK (X:A->bool) n
                 (FST s) (FST(SND s)) (FST(SND(SND s))) (SND(SND(SND s)))
                 (FST s') (FST(SND s')) (FST(SND(SND s'))) (SND(SND(SND s')))`]
   DEPENDENT_CHOICE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `(&0:int),(&0:int),(\i:int. (y0:A)),(\i:int. (e0:real^3->A))` THEN
      REWRITE_TAC[FST; SND; apxn_good] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[INT_LE_REFL; INT_SUB_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_SINGLE_CHAIN THEN ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`n:num`; `s:int#int#(int->A)#(int->real^3->A)`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`;
                     `y0:A`; `e0:real^3->A`; `n:num`;
                     `FST(s:int#int#(int->A)#(int->real^3->A))`;
                     `FST(SND(s:int#int#(int->A)#(int->real^3->A)))`;
                     `FST(SND(SND(s:int#int#(int->A)#(int->real^3->A))))`;
                     `SND(SND(SND(s:int#int#(int->A)#(int->real^3->A))))`]
                    APXN_STEP_EXISTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC
         [`n:num`; `FST(SND(SND(s:int#int#(int->A)#(int->real^3->A))))`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a':int` (X_CHOOSE_THEN `b':int` (X_CHOOSE_THEN `x':int->A`
        (X_CHOOSE_THEN `e':int->real^3->A` STRIP_ASSUME_TAC)))) THEN
      EXISTS_TAC `(a':int),(b':int),(x':int->A),(e':int->real^3->A)` THEN
      ASM_REWRITE_TAC[FST; SND]];
    DISCH_THEN(X_CHOOSE_THEN `f:num->int#int#(int->A)#(int->real^3->A)` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`\n. FST((f:num->int#int#(int->A)#(int->real^3->A)) n)`;
      `\n. FST(SND((f:num->int#int#(int->A)#(int->real^3->A)) n))`;
      `\n. FST(SND(SND((f:num->int#int#(int->A)#(int->real^3->A)) n)))`;
      `\n. SND(SND(SND((f:num->int#int#(int->A)#(int->real^3->A)) n)))`] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[]]);;
(* Limits of nested chains: a sequence of chains on growing intervals that  *)
(* agree on the earlier intervals has a limit chain on the union of the     *)
(* intervals, equal to each of them on its interval.                        *)

let APXN_NESTED_MONO = prove
 (`!(A:num->int) (B:num->int) (XX:num->int->A) (EE:num->int->real^3->A).
     (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
     (!n i. A n <= i /\ i <= B n ==> XX (SUC n) i = XX n i /\ EE (SUC n) i = EE n i)
     ==> !m n. m <= n
               ==> A n <= A m /\ B m <= B n /\
                   !i. A m <= i /\ i <= B m ==> XX n i = XX m i /\ EE n i = EE m i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m n. (A:num->int) n <= A m /\ (B:num->int) m <= B n /\
                      !i. A m <= i /\ i <= B m
                          ==> (XX:num->int->A) n i = XX m i /\
                              (EE:num->int->real^3->A) n i = EE m i`
         TRANSITIVE_STEPWISE_LE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INT_LE_REFL];
      MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `r:num`] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `i:int` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(A:num->int) q <= i /\ i <= (B:num->int) q` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_MESON_TAC[]];
      GEN_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    SIMP_TAC[]]);;

let APXN_NESTED_LIMIT = prove
 (`!top atlas (g:A->real^3^3) eps (A:num->int) (B:num->int) (XX:num->int->A)
    (EE:num->int->real^3->A).
     (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
     (!n i. A n <= i /\ i <= B n ==> XX (SUC n) i = XX n i /\ EE (SUC n) i = EE n i) /\
     (!n. apx_chain (top,atlas) g eps {i:int | A n <= i /\ i <= B n} (XX n) (EE n))
     ==> (!n i. A n <= i /\ i <= B n
                ==> (\i. XX (@n. A n <= i /\ i <= B n) i) i = XX n i /\
                    (\i. EE (@n. A n <= i /\ i <= B n) i) i = EE n i) /\
         apx_chain (top,atlas) g eps {i:int | ?n. A n <= i /\ i <= B n}
                   (\i. XX (@n. A n <= i /\ i <= B n) i)
                   (\i. EE (@n. A n <= i /\ i <= B n) i) /\
         (!q. q IN apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n}
                     (\i. EE (@n. A n <= i /\ i <= B n) i) <=>
              ?n. q IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch"))) THEN
  MP_TAC(ISPECL [`A:num->int`; `B:num->int`; `XX:num->int->A`; `EE:num->int->real^3->A`]
                APXN_NESTED_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!n i. (A:num->int) n <= i /\ i <= (B:num->int) n
                      ==> (XX:num->int->A) (@n. A n <= i /\ i <= B n) i = XX n i /\
                          (EE:num->int->real^3->A) (@n. A n <= i /\ i <= B n) i = EE n i`
  (LABEL_TAC "lim") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    ABBREV_TAC `n0 = @n. (A:num->int) n <= i /\ i <= (B:num->int) n` THEN
    SUBGOAL_THEN `(A:num->int) n0 <= i /\ i <= (B:num->int) n0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "n0" THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ_CASES_TAC(SPECL [`n:num`; `n0:num`] LE_CASES) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. (?n. (A:num->int) n <= i /\ i <= (B:num->int) n) /\
                      (?n. A n <= j /\ j <= B n)
                      ==> ?n. A n <= i /\ i <= B n /\ A n <= j /\ j <= B n`
  (LABEL_TAC "two") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n1:num`) (X_CHOOSE_TAC `n2:num`)) THEN
    EXISTS_TAC `MAX n1 n2` THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`n1:num`; `MAX n1 n2`] th) THEN
                            MP_TAC(SPECL [`n2:num`; `MAX n1 n2`] th)) THEN
    REWRITE_TAC[ARITH_RULE `n1 <= MAX n1 n2 /\ n2 <= MAX n1 n2`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[apx_chain; apx_int_interval; IN_ELIM_THM] THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:int`; `j:int`; `k:int`] THEN STRIP_TAC THEN
      USE_THEN "two" (MP_TAC o SPECL [`i:int`; `k:int`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN EXISTS_TAC `p:num` THEN ASM_ARITH_TAC;
      USE_THEN "ch" (MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[apx_chain; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_TAC `i:int` o CONJUNCT1 o CONJUNCT2) THEN
      EXISTS_TAC `i:int` THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:int` THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
      USE_THEN "ch" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:int` THEN DISCH_TAC THEN
      USE_THEN "two" (MP_TAC o SPECL [`i:int`; `i + &1:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i + &1:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
      USE_THEN "ch" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:int`; `i:int`] THEN DISCH_TAC THEN
      USE_THEN "two" (MP_TAC o SPECL [`a:int`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `a:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
      USE_THEN "ch" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:int`; `i:int`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                 CONJUNCT2) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `q:A` THEN REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN
    BETA_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:int` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `i:int`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `i:int` THEN CONJ_TAC THENL [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      ASM_REWRITE_TAC[]]]);;
(* Monotone integer sequences bounded on the relevant side are eventually  *)
(* constant.                                                                 *)

let APXN_INT_EVCONST_DEC = prove
 (`!(A:num->int) a0.
     (!n. A(SUC n) <= A n) /\ (!n. a0 <= A n) ==> ?N. !n. N <= n ==> A n = A N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (A:num->int) n <= A m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\m n. (A:num->int) n <= A m` TRANSITIVE_STEPWISE_LE)) THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(INST [`\v:int. ?n. v = (A:num->int) n - a0`,`P:int->bool`] INT_WOP) THEN BETA_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `(A:num->int) 0 - a0` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> can (find_term ((=) `a0:int`)) (concl th) &&
        not (can (find_term ((=) `SUC`)) (concl th)))) THEN INT_ARITH_TAC;
      EXISTS_TAC `0` THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:int` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N:num`) (LABEL_TAC "min")))) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "min" (MP_TAC o SPEC `(A:num->int) n - a0`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `a0:int`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `SUC`)) (concl th)))) THEN INT_ARITH_TAC;
      EXISTS_TAC `n:num` THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `n:num`] o check (fun th ->
    can (find_term ((=) `(<=):num->num->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let APXN_INT_EVCONST_INC = prove
 (`!(B:num->int) b0.
     (!n. B n <= B(SUC n)) /\ (!n. B n <= b0) ==> ?N. !n. N <= n ==> B n = B N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. --((B:num->int) n)`; `--b0:int`] APXN_INT_EVCONST_DEC) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_LE_NEG2]; REWRITE_TAC[INT_EQ_NEG2]]);;
(* The facts of the growth sequence used for its limit. *)

let APXN_SEQ_FACTS = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 (e0:real^3->A) (A:num->int) (B:num->int)
    (XX:num->int->A) (EE:num->int->real^3->A).
     (!n. apxn_good top atlas g eps NK X y0 e0 n (A n) (B n) (XX n) (EE n) /\
          apxn_step top eps NK X n (A n) (B n) (XX n) (EE n)
                    (A(SUC n)) (B(SUC n)) (XX(SUC n)) (EE(SUC n)))
     ==> (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
         (!n i. A n <= i /\ i <= B n ==> XX (SUC n) i = XX n i /\ EE (SUC n) i = EE n i) /\
         (!n. apx_chain (top,atlas) g eps {i:int | A n <= i /\ i <= B n} (XX n) (EE n)) /\
         (!n. B n - A n = &n /\ A n <= &0 /\ &0 <= B n /\ XX n (&0) = y0 /\ EE n (&0) = e0) /\
         (!n i. A n <= i /\ i <= B n
                ==> XX n i IN X /\ (NK (XX n i) (EE n i) \/ NK (XX n i) (apx_rev (EE n i)))) /\
         (!n. A(SUC n) = A n /\ EVEN n ==> ~apxn_downext top eps NK X (A n) (B n) (EE n)) /\
         (!n. B(SUC n) = B n /\ ~EVEN n ==> ~apxn_upext top eps NK X (A n) (B n) (EE n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apxn_good; apxn_step; apx_balanced] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THEN ASM_ARITH_TAC) THEN
  TRY(GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY(STRIP_TAC THEN ASM_ARITH_TAC) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The limit of the fair growth in its three cases (half line               *)
(* up, half line down, all integers) and the growth theorem APXN_GROW2.     *)
(* ------------------------------------------------------------------------- *)

let APXN_INT_ARCH = prove
 (`!x:int. ?n. x <= &n`,
  GEN_TAC THEN EXISTS_TAC `num_of_int(abs x)` THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN INT_ARITH_TAC);;

(* Fairness at the bottom: once the bottom index has stabilized, at an even *)
(* step no point of X with an NK-neck lies in the closure of the bottom     *)
(* quarter of the bottom neck outside every chain of the sequence.          *)

let APXN_FAIR_BOTTOM = prove
 (`!top eps NK (X:A->bool) (A:num->int) (B:num->int) (EE:num->int->real^3->A)
    (el:int->real^3->A) N z.
     (!n. N <= n ==> A n = A N) /\
     (!n. A(SUC n) = A n /\ EVEN n ==> ~apxn_downext top eps NK X (A n) (B n) (EE n)) /\
     (!n i. A n <= i /\ i <= B n ==> el i = EE n i) /\
     (!n. A n <= B n) /\
     (!x. x IN X ==> ?e:real^3->A. NK x e) /\
     z IN X /\
     z IN top closure_of (IMAGE (el (A N)) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
     (!n. ~(z IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n)))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 (LABEL_TAC "fa")
    (CONJUNCTS_THEN2 (LABEL_TAC "el") (CONJUNCTS_THEN2 (LABEL_TAC "ab")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "out")))))))) THEN
  SUBGOAL_THEN `(A:num->int)(SUC(2 * N)) = A N /\ A(2 * N) = A N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "st" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(EE:num->int->real^3->A) (2 * N) ((A:num->int) N) = el (A N)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "el" MATCH_MP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `2 * N`) THEN
    UNDISCH_TAC `(A:num->int)(2 * N) = A N` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fa" (MP_TAC o SPEC `2 * N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
  REWRITE_TAC[apxn_downext; TAUT `~p ==> F <=> p`] THEN
  USE_THEN "nk" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN X`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ez:real^3->A`) THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `ez:real^3->A`] THEN
  ASM_REWRITE_TAC[]);;

(* Fairness at the top, symmetrically (odd steps). *)

let APXN_FAIR_TOP = prove
 (`!top eps NK (X:A->bool) (A:num->int) (B:num->int) (EE:num->int->real^3->A)
    (el:int->real^3->A) N z.
     (!n. N <= n ==> B n = B N) /\
     (!n. B(SUC n) = B n /\ ~EVEN n ==> ~apxn_upext top eps NK X (A n) (B n) (EE n)) /\
     (!n i. A n <= i /\ i <= B n ==> el i = EE n i) /\
     (!n. A n <= B n) /\
     (!x. x IN X ==> ?e:real^3->A. NK x e) /\
     z IN X /\
     z IN top closure_of (IMAGE (el (B N)) (apx_slab (inv(&2 * eps)) (inv eps))) /\
     (!n. ~(z IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n)))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 (LABEL_TAC "fa")
    (CONJUNCTS_THEN2 (LABEL_TAC "el") (CONJUNCTS_THEN2 (LABEL_TAC "ab")
    (CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "out")))))))) THEN
  SUBGOAL_THEN `(B:num->int)(SUC(2 * N + 1)) = B N /\ B(2 * N + 1) = B N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "st" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(EE:num->int->real^3->A) (2 * N + 1) ((B:num->int) N) = el (B N)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "el" MATCH_MP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `2 * N + 1`) THEN
    UNDISCH_TAC `(B:num->int)(2 * N + 1) = B N` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "fa" (MP_TAC o SPEC `2 * N + 1`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
  REWRITE_TAC[apxn_upext; TAUT `~p ==> F <=> p`] THEN
  USE_THEN "nk" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN X`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `ez:real^3->A`) THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `ez:real^3->A`] THEN
  ASM_REWRITE_TAC[]);;

(* The three cases of the limit of the fair growth: bottom indices bounded  *)
(* (a half line upwards), top indices bounded (a half line downwards), or   *)
(* neither (all integers); in each case X lies in the union of the limit.   *)

let APXN_A_LE_B = prove
 (`!(A:num->int) (B:num->int). (!n. B n - A n = &n) ==> !n. A n <= B n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  MP_TAC(SPEC `n:num` INT_POS) THEN INT_ARITH_TAC);;

let APXN_NOT_IN_LIMIT = prove
 (`!eps (A:num->int) (B:num->int) (EE:num->int->real^3->A) (el:int->real^3->A) Ix z.
     (!q. q IN apx_chain_union eps Ix el <=>
          ?n. q IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n)) /\
     ~(z IN apx_chain_union eps Ix el)
     ==> !n. ~(z IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  UNDISCH_TAC `~((z:A) IN apx_chain_union eps Ix (el:int->real^3->A))` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

let APXN_COVER_BY_FRONTIER = prove
 (`!top (X:A->bool) U S.
     connected_in top X /\ open_in top U /\ ~(X INTER U = {}) /\
     top frontier_of U SUBSET S /\ (!z. z IN X /\ z IN S ==> z IN U)
     ==> X SUBSET U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `X INTER top frontier_of U = {}:A->bool` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN U` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN top frontier_of U` THEN ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `X:A->bool`; `U:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let APXN_GROW_UP = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) (A:num->int) (B:num->int)
    (EE:num->int->real^3->A) (el:int->real^3->A) (xl:int->A) a0.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\
     (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
     (!n. B n - A n = &n) /\
     (!n. A(SUC n) = A n /\ EVEN n ==> ~apxn_downext top eps NK X (A n) (B n) (EE n)) /\
     (!n i. A n <= i /\ i <= B n ==> el i = EE n i) /\
     apx_chain (top,atlas) g eps {i:int | ?n. A n <= i /\ i <= B n} xl el /\
     (!q. q IN apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el <=>
          ?n. q IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n)) /\
     ~(X INTER apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el = {}) /\
     (!n. a0 <= A n)
     ==> ?a. {i:int | ?n. A n <= i /\ i <= B n} = {i | a <= i} /\
             X SUBSET apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:num->int`; `a0:int`] APXN_INT_EVCONST_DEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "st"))] THEN
  MP_TAC(ISPECL [`A:num->int`; `B:num->int`] APXN_A_LE_B) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (A:num->int) n <= A m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\m n. (A:num->int) n <= A m` TRANSITIVE_STEPWISE_LE)) THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = {i | A N <= i}`
  (LABEL_TAC "ix") THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      DISJ_CASES_TAC(SPECL [`n:num`; `N:num`] LE_CASES) THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `N:num`] o check (fun th ->
          can (find_term ((=) `(<=):num->num->bool`)) (concl th) && is_forall (concl th) &&
          not (can (find_term ((=) `N:num`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(A:num->int) n <= i` THEN INT_ARITH_TAC;
        USE_THEN "st" (MP_TAC o C MATCH_MP (ASSUME `N <= n:num`)) THEN
        UNDISCH_TAC `(A:num->int) n <= i` THEN INT_ARITH_TAC];
      DISCH_TAC THEN X_CHOOSE_TAC `k:num` (SPEC `i - a0:int` APXN_INT_ARCH) THEN
      EXISTS_TAC `MAX N k` THEN
      USE_THEN "st" (MP_TAC o SPEC `MAX N k`) THEN
      REWRITE_TAC[ARITH_RULE `N <= MAX N k`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `MAX N k` o check (fun th ->
        can (find_term ((=) `a0:int`)) (concl th) && is_forall (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `MAX N k` o check (fun th ->
        can (find_term ((=) `(-):int->int->int`)) (concl th) && is_forall (concl th) &&
        not (can (find_term ((=) `a0:int`)) (concl th)))) THEN
      SUBGOAL_THEN `&k:int <= &(MAX N k)` MP_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(i:int) - a0 <= &k` THEN UNDISCH_TAC `(A:num->int) N <= i` THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(A:num->int) N` THEN CONJ_TAC THENL [USE_THEN "ix" ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC APXN_COVER_BY_FRONTIER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`;
    `top closure_of (IMAGE ((el:int->real^3->A) ((A:num->int) N))
                           (apx_slab (--inv eps) (--inv(&2 * eps))))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `xl:int->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_ch_ctx];
    USE_THEN "ix" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC APXN_UP_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `xl:int->A`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ix" (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN MATCH_MP_TAC APXN_FAIR_BOTTOM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `NK:A->(real^3->A)->bool`;
                          `X:A->bool`; `A:num->int`; `B:num->int`;
                          `EE:num->int->real^3->A`; `el:int->real^3->A`; `N:num`; `z:A`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APXN_NOT_IN_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`el:int->real^3->A`;
                          `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n}`] THEN
    ASM_REWRITE_TAC[]]);;

let APXN_GROW_DOWN = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) (A:num->int) (B:num->int)
    (EE:num->int->real^3->A) (el:int->real^3->A) (xl:int->A) b0.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\
     (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
     (!n. B n - A n = &n) /\
     (!n. B(SUC n) = B n /\ ~EVEN n ==> ~apxn_upext top eps NK X (A n) (B n) (EE n)) /\
     (!n i. A n <= i /\ i <= B n ==> el i = EE n i) /\
     apx_chain (top,atlas) g eps {i:int | ?n. A n <= i /\ i <= B n} xl el /\
     (!q. q IN apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el <=>
          ?n. q IN apx_chain_union eps {i:int | A n <= i /\ i <= B n} (EE n)) /\
     ~(X INTER apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el = {}) /\
     (!n. B n <= b0)
     ==> ?b. {i:int | ?n. A n <= i /\ i <= B n} = {i | i <= b} /\
             X SUBSET apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:num->int`; `b0:int`] APXN_INT_EVCONST_INC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "st"))] THEN
  MP_TAC(ISPECL [`A:num->int`; `B:num->int`] APXN_A_LE_B) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (B:num->int) m <= B n` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\m n. (B:num->int) m <= B n` TRANSITIVE_STEPWISE_LE)) THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = {i | i <= B N}`
  (LABEL_TAC "ix") THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      DISJ_CASES_TAC(SPECL [`n:num`; `N:num`] LE_CASES) THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `N:num`] o check (fun th ->
          can (find_term ((=) `(<=):num->num->bool`)) (concl th) && is_forall (concl th) &&
          not (can (find_term ((=) `N:num`)) (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i <= (B:num->int) n` THEN INT_ARITH_TAC;
        USE_THEN "st" (MP_TAC o C MATCH_MP (ASSUME `N <= n:num`)) THEN
        UNDISCH_TAC `i <= (B:num->int) n` THEN INT_ARITH_TAC];
      DISCH_TAC THEN X_CHOOSE_TAC `k:num` (SPEC `b0 - i:int` APXN_INT_ARCH) THEN
      EXISTS_TAC `MAX N k` THEN
      USE_THEN "st" (MP_TAC o SPEC `MAX N k`) THEN
      REWRITE_TAC[ARITH_RULE `N <= MAX N k`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `MAX N k` o check (fun th ->
        can (find_term ((=) `b0:int`)) (concl th) && is_forall (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `MAX N k` o check (fun th ->
        can (find_term ((=) `(-):int->int->int`)) (concl th) && is_forall (concl th) &&
        not (can (find_term ((=) `b0:int`)) (concl th)))) THEN
      SUBGOAL_THEN `&k:int <= &(MAX N k)` MP_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(b0:int) - i <= &k` THEN UNDISCH_TAC `i <= (B:num->int) N` THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(B:num->int) N` THEN CONJ_TAC THENL [USE_THEN "ix" ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC APXN_COVER_BY_FRONTIER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`;
    `top closure_of (IMAGE ((el:int->real^3->A) ((B:num->int) N))
                           (apx_slab (inv(&2 * eps)) (inv eps)))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `xl:int->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_ch_ctx];
    USE_THEN "ix" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC APXN_DOWN_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `xl:int->A`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ix" (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN MATCH_MP_TAC APXN_FAIR_TOP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`; `NK:A->(real^3->A)->bool`;
                          `X:A->bool`; `A:num->int`; `B:num->int`;
                          `EE:num->int->real^3->A`; `el:int->real^3->A`; `N:num`; `z:A`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APXN_NOT_IN_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`el:int->real^3->A`;
                          `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n}`] THEN
    ASM_REWRITE_TAC[]]);;

let APXN_GROW_BI = prove
 (`!top atlas (g:A->real^3^3) eps (X:A->bool) (A:num->int) (B:num->int)
    (el:int->real^3->A) (xl:int->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     connected_in top X /\
     (!n. A(SUC n) <= A n /\ B n <= B(SUC n)) /\
     apx_chain (top,atlas) g eps {i:int | ?n. A n <= i /\ i <= B n} xl el /\
     ~(X INTER apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el = {}) /\
     ~(?a0. !n. a0 <= A n) /\ ~(?b0. !n. B n <= b0)
     ==> {i:int | ?n. A n <= i /\ i <= B n} = (:int) /\
         X SUBSET apx_chain_union eps {i:int | ?n. A n <= i /\ i <= B n} el`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = (:int)`
  (LABEL_TAC "ix") THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `i:int` THEN
    UNDISCH_TAC `~(?a0. !n. a0 <= (A:num->int) n)` THEN
    DISCH_THEN(MP_TAC o SPEC `i + &1:int` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    REWRITE_TAC[NOT_FORALL_THM; INT_NOT_LE] THEN DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
    UNDISCH_TAC `~(?b0. !n. (B:num->int) n <= b0)` THEN
    DISCH_THEN(MP_TAC o SPEC `i - &1:int` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    REWRITE_TAC[NOT_FORALL_THM; INT_NOT_LE] THEN DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
    EXISTS_TAC `MAX n1 n2` THEN
    SUBGOAL_THEN `!m n. m <= n ==> (A:num->int) n <= A m /\ (B:num->int) m <= B n`
    (MP_TAC o SPECL [`n1:num`; `MAX n1 n2`] ) THENL
     [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\m n. (A:num->int) n <= A m /\ (B:num->int) m <= B n`
                                     TRANSITIVE_STEPWISE_LE)) THEN
      ASM_REWRITE_TAC[INT_LE_REFL] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!m n. m <= n ==> (A:num->int) n <= A m /\ (B:num->int) m <= B n`
    (MP_TAC o SPECL [`n2:num`; `MAX n1 n2`] ) THENL
     [MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `\m n. (A:num->int) n <= A m /\ (B:num->int) m <= B n`
                                     TRANSITIVE_STEPWISE_LE)) THEN
      ASM_REWRITE_TAC[INT_LE_REFL] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `n1 <= MAX n1 n2 /\ n2 <= MAX n1 n2`] THEN
    UNDISCH_TAC `(A:num->int) n1 < i + &1` THEN UNDISCH_TAC `i - &1 < (B:num->int) n2` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = (:int)`]) THEN
  MATCH_MP_TAC APXN_COVER_BY_FRONTIER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `{}:A->bool`] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; SUBSET_EMPTY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `xl:int->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_ch_ctx];
    SUBGOAL_THEN `closed_in top (apx_chain_union eps (:int) (el:int->real^3->A)) /\
                  open_in top (apx_chain_union eps (:int) el)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC APXN_BI_CLOSED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `xl:int->A`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `xl:int->A`] THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_ch_ctx]];
      SIMP_TAC[FRONTIER_OF_OPEN_IN; CLOSURE_OF_CLOSED_IN] THEN SET_TAC[]]]);;

(* The fair two-sided growth from the NK-neck e0 at y0 in a connected set X *)
(* of NK-centres that no finite chain of the growth covers: a chain on a     *)
(* half line or on all integers, with neck e0 at index 0, centres in X with *)
(* NK-necks up to orientation, whose union contains X.                       *)

let APXN_GROW2 = prove
 (`!top atlas (g:A->real^3^3) eps NK X y0 (e0:real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     connected_in top X /\ (!x. x IN X ==> ?e:real^3->A. NK x e) /\ y0 IN X /\ NK y0 e0 /\
     (!n a b x e. apxn_good top atlas g eps NK X y0 e0 n a b x e
                  ==> ~(X SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e))
     ==> ?Ix x e. apx_chain (top,atlas) g eps Ix x e /\ &0 IN Ix /\ x(&0) = y0 /\
                  e(&0) = e0 /\
                  (!i. i IN Ix ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                  X SUBSET apx_chain_union eps Ix e /\
                  ((?a. a <= &0 /\ Ix = {i:int | a <= i}) \/
                   (?b. &0 <= b /\ Ix = {i:int | i <= b}) \/ Ix = (:int))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `y0:A`; `e0:real^3->A`]
                APXN_GROW_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:num->int` (X_CHOOSE_THEN `B:num->int`
    (X_CHOOSE_THEN `XX:num->int->A` (X_CHOOSE_THEN `EE:num->int->real^3->A` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `y0:A`; `e0:real^3->A`;
                 `A:num->int`; `B:num->int`; `XX:num->int->A`; `EE:num->int->real^3->A`]
                APXN_SEQ_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `A:num->int`; `B:num->int`; `XX:num->int->A`;
                 `EE:num->int->real^3->A`] APXN_NESTED_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `xl = \i. (XX:num->int->A) (@n. (A:num->int) n <= i /\ i <= (B:num->int) n) i` THEN
  ABBREV_TAC `el = \i. (EE:num->int->real^3->A)
                         (@n. (A:num->int) n <= i /\ i <= (B:num->int) n) i` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "un"))) THEN
  SUBGOAL_THEN `!n i. (A:num->int) n <= i /\ i <= (B:num->int) n
                      ==> (xl:int->A) i = XX n i /\ (el:int->real^3->A) i = EE n i`
  (LABEL_TAC "lim2") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["xl"; "el"] THEN
    USE_THEN "lim" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; BETA_TAC THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->int`; `B:num->int`] APXN_A_LE_B) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(A:num->int) 0 <= &0 /\ &0 <= (B:num->int) 0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(xl:int->A)(&0) = y0 /\ (el:int->real^3->A)(&0) = e0` STRIP_ASSUME_TAC THENL
   [USE_THEN "lim2" (MP_TAC o SPECL [`0`; `&0:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((X:A->bool) INTER apx_chain_union eps {i:int | ?n. (A:num->int) n <= i /\
                                                                   i <= (B:num->int) n}
                                     (el:int->real^3->A) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y0:A` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(xl:int->A)(&0) = y0`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`;
                   `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n}`;
                   `xl:int->A`; `el:int->real^3->A`; `&0:int`] APXN_NECK_IN_UNION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n}`;
                        `xl:int->A`; `el:int->real^3->A`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `?n. (A:num->int) n <= &0 /\ &0 <= (B:num->int) n` (fun th -> REWRITE_TAC[th]) THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (?n. (A:num->int) n <= i /\ i <= (B:num->int) n)
                    ==> (xl:int->A) i IN X /\
                        (NK (xl i) ((el:int->real^3->A) i) \/ NK (xl i) (apx_rev (el i)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `i:int` THEN DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "lim2" (MP_TAC o SPECL [`n:num`; `i:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `X:A->bool`)) (concl th) &&
      can (find_term ((=) `XX:num->int->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?a0. !n. a0 <= (A:num->int) n` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `a0:int`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `A:num->int`;
                   `B:num->int`; `EE:num->int->real^3->A`; `el:int->real^3->A`;
                   `xl:int->A`; `a0:int`] APXN_GROW_UP) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [USE_THEN "lim2" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:int` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC `a:int` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = {i | a <= i}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&0:int`) THEN
    SUBGOAL_THEN `?n. (A:num->int) n <= &0 /\ &0 <= (B:num->int) n` ASSUME_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?b0. !n. (B:num->int) n <= b0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `b0:int`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `A:num->int`;
                   `B:num->int`; `EE:num->int->real^3->A`; `el:int->real^3->A`;
                   `xl:int->A`; `b0:int`] APXN_GROW_DOWN) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [USE_THEN "lim2" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:int` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `b:int` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `{i:int | ?n. (A:num->int) n <= i /\ i <= (B:num->int) n} = {i | i <= b}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&0:int`) THEN
    SUBGOAL_THEN `?n. (A:num->int) n <= &0 /\ &0 <= (B:num->int) n` ASSUME_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `X:A->bool`; `A:num->int`; `B:num->int`; `el:int->real^3->A`;
                 `xl:int->A`] APXN_GROW_BI) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Growth from the end neck of a cap without a length bound                 *)
(* (APX21_GROWTH for noncompact X): either a finite chain with no NK-centre *)
(* of X on the frontier of the cap with the chain, or an infinite chain of  *)
(* X-centred NK-necks from the end neck.                                     *)
(* ------------------------------------------------------------------------- *)

let APXN_CAP_EXT = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) (e0:real^3->A) z0 K U k x e z ez.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx21_ext top atlas g eps /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     apx_balanced (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\
     e(&0) = e0 /\ x(&0) = z0 /\
     (!i. &1 <= i /\ i <= &k ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
     z IN X /\ NK z ez /\
     z IN top frontier_of (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
     ==> ?x' e'. apx_balanced (top,atlas) g eps {i:int | &0 <= i /\ i <= &(SUC k)} x' e' /\
                 e'(&0) = e0 /\ x'(&0) = z0 /\
                 (!i. &1 <= i /\ i <= &(SUC k)
                      ==> x' i IN X /\ (NK (x' i) (e' i) \/ NK (x' i) (apx_rev (e' i)))) /\
                 (!i. &0 <= i /\ i <= &k ==> x' i = x i /\ e' i = e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `e0:real^3->A`; `K:A->bool`; `U:A->bool`; `k:num`; `x:int->A`;
                 `e:int->real^3->A`] APX21_CAPPED_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_balanced]; DISCH_TAC] THEN
  SUBGOAL_THEN `~((z:A) IN apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of
                   (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)` THEN
    SUBGOAL_THEN `open_in top (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k}
                                         (e:int->real^3->A))`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `x:int->A`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[apx_ch_ctx]; ASM_MESON_TAC[apx_balanced]];
      SIMP_TAC[FRONTIER_OF_OPEN_IN; IN_DIFF; IN_UNION; DE_MORGAN_THM]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&0:int`; `&k:int`; `x:int->A`; `e:int->real^3->A`; `z:A`;
                              `ez:real^3->A`] o REWRITE_RULE[apx21_ext] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx21_ext")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_POS] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ez':real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\i:int. if i = &k + &1 then (z:A) else x i`;
                        `\i:int. if i = &k + &1 then (ez':real^3->A) else e i`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `~(&0:int = &k + &1)`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:int` THEN STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term (fun t -> t = `ez':real^3->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[APX_REV_REV];
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `X:A->bool`)) (concl th) &&
        can (find_term (fun t -> t = `&1:int`)) (concl th))) THEN
      ASM_INT_ARITH_TAC];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i:int = &k + &1)` (fun th -> REWRITE_TAC[th]) THEN ASM_INT_ARITH_TAC]);;
let APXN_CAP_GROW = prove
 (`!top atlas (g:A->real^3^3) eps NK (X:A->bool) (e0:real^3->A) z0 K U.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx21_ext top atlas g eps /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     rfs_neck (top,atlas) g eps z0 e0 /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (&0))) SUBSET
       K UNION IMAGE e0 (apx_slab (--inv eps) (&0)) UNION IMAGE e0 (sphere(vec 0,&1)) /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps)))
     ==> (?k x e.
            apx_balanced (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e /\
            e(&0) = e0 /\ x(&0) = z0 /\
            (!i. &1 <= i /\ i <= &k
                 ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
            (!z. z IN X /\
                 z IN top frontier_of
                        (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)
                 ==> ~(?ez. NK z ez))) \/
         (?x e.
            apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
            e(&0) = e0 /\ x(&0) = z0 /\
            (!i. &1 <= i ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k (x:int->A) (e:int->real^3->A).
      apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e /\
      e(&0) = e0 /\ x(&0) = z0 /\
      (!i. &1 <= i /\ i <= &k
           ==> x i IN X /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i))))
      ==> ?z ez. z IN X /\ NK z ez /\
                 z IN top frontier_of
                        (U UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e)`
  (LABEL_TAC "ns") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `x:int->A`; `e:int->real^3->A`] o
                  REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_TAC `ez:real^3->A`))) THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `ez:real^3->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n (s:(int->A)#(int->real^3->A)).
       apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &n}
                    (FST s) (SND s) /\
       SND s (&0) = e0 /\ FST s (&0) = (z0:A) /\
       (!i. &1 <= i /\ i <= &n
            ==> FST s i IN X /\ (NK (FST s i) (SND s i) \/ NK (FST s i) (apx_rev (SND s i))))`;
    `\n (s:(int->A)#(int->real^3->A)) (s':(int->A)#(int->real^3->A)).
       !i. &0 <= i /\ i <= &n ==> FST s' i = FST s i /\ SND s' i = SND s i`]
   DEPENDENT_CHOICE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `(\i:int. (z0:A)),(\i:int. (e0:real^3->A))` THEN REWRITE_TAC[FST; SND] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC APX_SINGLE_CHAIN THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN INT_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`n:num`; `s:(int->A)#(int->real^3->A)`] THEN STRIP_TAC THEN
      USE_THEN "ns" (MP_TAC o SPECL [`n:num`; `FST(s:(int->A)#(int->real^3->A))`;
                                     `SND(s:(int->A)#(int->real^3->A))`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `ez:real^3->A` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`;
                     `e0:real^3->A`; `z0:A`; `K:A->bool`; `U:A->bool`; `n:num`;
                     `FST(s:(int->A)#(int->real^3->A))`; `SND(s:(int->A)#(int->real^3->A))`;
                     `z:A`; `ez:real^3->A`] APXN_CAP_EXT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x':int->A` (X_CHOOSE_THEN `e':int->real^3->A`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `(x':int->A),(e':int->real^3->A)` THEN ASM_REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(int->A)#(int->real^3->A)` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `\n:num. &0:int`; `\n:num. &n:int`;
                 `\n. FST((f:num->(int->A)#(int->real^3->A)) n)`;
                 `\n. SND((f:num->(int->A)#(int->real^3->A)) n)`] APXN_NESTED_LIMIT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INT_LE_REFL; INT_OF_NUM_LE] THEN ARITH_TAC;
      ASM_REWRITE_TAC[];
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_balanced")) (concl th))) THEN
      SIMP_TAC[apx_balanced]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{i:int | ?n. &0 <= i /\ i <= &n} = {i | &0 <= i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `i:int` THEN EQ_TAC THENL
     [MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `num_of_int i` THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`\i. FST((f:num->(int->A)#(int->real^3->A)) (@n. &0 <= i /\ i <= &n)) i`;
    `\i. SND((f:num->(int->A)#(int->real^3->A)) (@n. &0 <= i /\ i <= &n)) i`] THEN
  ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= i /\ &(num_of_int i) = i` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [UNDISCH_TAC `&1 <= (i:int)` THEN INT_ARITH_TAC; SIMP_TAC[INT_OF_NUM_OF_INT]];
      ALL_TAC] THEN
    USE_THEN "lim" (MP_TAC o SPECL [`num_of_int i`; `i:int`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INT_LE_REFL]; DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int i` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `X:A->bool`)) (concl th))) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[INT_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* No cap cores in a noncompact set of high curvature (claim                *)
(* C).  A cap whose core meets X gives a maximal cap and the growth from    *)
(* its end neck: a compact component, X inside a bounded set, or a capped   *)
(* infinite chain which is closed and open, hence the whole component, where *)
(* the curvature exceeds L everywhere.                                       *)
(* ------------------------------------------------------------------------- *)

let APXN_CAPPED_INF_CLOSED = prove
 (`!top atlas (g:A->real^3^3) eps (e0:real^3->A) K U x (e:int->real^3->A).
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     IMAGE e0 (rfs_neck_dom eps) = U DIFF K /\ K SUBSET U /\ open_in top U /\
     top frontier_of U SUBSET
       top closure_of (IMAGE e0 (apx_slab (inv eps - &1) (inv eps))) /\
     top closure_of (K UNION IMAGE e0 (apx_slab (--inv eps) (--inv(&2 * eps)))) SUBSET U /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\ e(&0) = e0
     ==> closed_in top (U UNION apx_chain_union eps {i:int | &0 <= i} e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
  ABBREV_TAC `V = apx_chain_union eps {i:int | &0 <= i} (e:int->real^3->A)` THEN
  SUBGOAL_THEN `open_in top (V:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (rfs_neck_dom eps) SUBSET V` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:int->real^3->A)(&0) = e0`)) THEN
    EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `{i:int | &0 <= i}`; `x:int->A`; `e:int->real^3->A`; `&0:int`]
                  APXN_NECK_IN_UNION) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:int->A`; `e:int->real^3->A`] APX_A15_CORE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `top frontier_of (V:A->bool) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (IMAGE ((e:int->real^3->A)(&0))
                                   (apx_slab (--inv eps) (--inv(&2 * eps))))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (K UNION IMAGE (e0:real^3->A)
                                   (apx_slab (--inv eps) (--inv(&2 * eps))))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)))
                SUBSET top closure_of V` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MONO THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
    SUBGOAL_THEN `&1024 <= inv eps` MP_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN
      SUBGOAL_THEN `&0 < eps /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ; CLOSURE_OF_UNION] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ V SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  UNDISCH_TAC `top frontier_of (U:A->bool) SUBSET
               top closure_of (IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)))` THEN
  UNDISCH_TAC `top frontier_of (V:A->bool) SUBSET U` THEN
  UNDISCH_TAC `top closure_of (IMAGE (e0:real^3->A) (apx_slab (inv eps - &1) (inv eps)))
               SUBSET top closure_of V` THEN
  ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN] THEN SET_TAC[]);;
let APXN_FIN_CHAIN_R_BOUND = prove
 (`!top atlas (g:A->real^3^3) eps k x (e:int->real^3->A).
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
                          ==> mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &k} x e
     ==> ?c. !p. p IN apx_chain_union eps {i:int | &0 <= i /\ i <= &k} e
                 ==> mfd_scalar atlas g p <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\i:int. mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)`;
                 `{i:int | &0 <= i /\ i <= &k}`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[APX21_SEG_CARD] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `&101 / &100 * max a (&0)` THEN
  REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&101 / &100 * mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &k} x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> can (find_term ((=) `a:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]);;
let APXN_SPHERE_IN_SLAB = prove
 (`!t a b. a < t /\ t < b ==> sphere(vec 0:real^3,exp(t / sqrt(&2))) SUBSET apx_slab a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; APX_SLAB_SVAL] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `norm(vec 0:real^3) = exp(t / sqrt(&2))` THEN
    REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `t / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN
  SUBGOAL_THEN `sqrt(&2) * (t / sqrt(&2)) = t` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]);;
let APXN_NO_CAP_CORE = prove
 (`!top atlas (g:A->real^3^3) C eps NK (X:A->bool) W L.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx21_ext top atlas g eps /\
     apx21_tubes top atlas g eps /\
     (!x1 (e2:real^3->A) U1 Y1.
        rfs_neck (top,atlas) g eps x1 e2 /\ rfs_cap (top,atlas) g C eps U1 Y1
        ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     &1 <= C /\ &0 < L /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?q. q IN W /\ mfd_scalar atlas g q <= L) /\
     closed_in top X /\ connected_in top X /\ X SUBSET W /\ ~compact_in top X /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN X ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)) /\
     (!x. x IN X ==> &5 / &4 * C * L <= mfd_scalar atlas g x)
     ==> !x U Y. x IN X /\ rfs_cap (top,atlas) g C eps U Y ==> ~(x IN Y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "nc") (CONJUNCTS_THEN2 (LABEL_TAC "rat")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "prop") (CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nk")
   (CONJUNCTS_THEN2 (LABEL_TAC "can") (LABEL_TAC "lev"))))))))))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`x0:A`; `U:A->bool`; `Y:A->bool`] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                hausdorff_space top /\ &0 < eps /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `W SUBSET topspace (top:A topology) /\ open_in top W /\ connected_in top W`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                  APXN_COMPONENT_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the maximal cap *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `X:A->bool`; `U:A->bool`; `Y:A->bool`]
                APX21_MAXIMAL_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x0:A` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CORE_IN_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` (X_CHOOSE_THEN `Y0:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U0:A->bool`; `Y0:A->bool`] APX21_CAP_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `z0:A` (X_CHOOSE_THEN `K:A->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tf"))))))))))))))))) THEN
  (* a point of X in the closed core, inside U0 *)
  SUBGOAL_THEN `?q':A. q' IN X /\ q' IN U0` (X_CHOOSE_THEN `q':A` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `~DISJOINT (X:A->bool) (top closure_of Y0)` THEN
    UNDISCH_TAC `top closure_of Y0 SUBSET (K:A->bool)` THEN
    UNDISCH_TAC `(K:A->bool) SUBSET U0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U0:A->bool) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_CAP_IN_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `C:real`; `eps:real`; `Y0:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* curvature on U0 *)
  SUBGOAL_THEN `!y:A. y IN U0 ==> L < mfd_scalar atlas (g:A->real^3^3) y` (LABEL_TAC "u0l") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U0:A->bool`; `Y0:A->bool`; `y:A`; `q':A`]
                  APX22_CAP_RATIO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "lev" (MP_TAC o C MATCH_MP (ASSUME `(q':A) IN X`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `C * (&5 / &4 * L) < C * mfd_scalar atlas (g:A->real^3^3) y` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:A) IN U0` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z0 e0` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U0 DIFF K` THEN
    UNDISCH_TAC `(z0:A) IN IMAGE (e0:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN U0 ==> mfd_scalar atlas (g:A->real^3^3) y <= C * mfd_scalar atlas g z0`
  (LABEL_TAC "u0b") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U0:A->bool`; `Y0:A->bool`; `z0:A`; `y:A`]
                  APX22_CAP_RATIO) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the closure fact at level 0 for the growth *)
  USE_THEN "tf" (MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `e0:real^3->A`; `z0:A`;
                 `K:A->bool`; `U0:A->bool`] APXN_CAP_GROW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* a finite chain with no NK-centre of X on the frontier *)
    ABBREV_TAC `V = (U0:A->bool) UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k}
                                          (e:int->real^3->A)` THEN
    SUBGOAL_THEN `open_in top (V:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `x:int->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_balanced];
      ALL_TAC] THEN
    ASM_CASES_TAC `?z:A. z IN X /\ z IN top frontier_of V` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(?ez:real^3->A. NK (z:A) ez)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `NK:A->(real^3->A)->bool`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier_of")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:A) IN top frontier_of V` THEN EXPAND_TAC "V" THEN
        REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "can" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN X`)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `C:real`; `eps:real`; `X:A->bool`; `U0:A->bool`; `Y0:A->bool`;
                     `e0:real^3->A`; `K:A->bool`; `k:num`; `x:int->A`; `e:int->real^3->A`;
                     `U':A->bool`; `Y':A->bool`; `z:A`] APX21_UNION_COMPONENT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[apx_balanced];
        ALL_TAC] THEN
      ABBREV_TAC `V' = (U0 UNION apx_chain_union eps {i:int | &0 <= i /\ i <= &k}
                                   (e:int->real^3->A)) UNION (U':A->bool)` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `V':A->bool = W` SUBST_ALL_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `V':A->bool`; `W:A->bool`]
                      CONNECTED_COMPONENTS_OF_OVERLAP) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q':A` THEN
        CONJ_TAC THENL [EXPAND_TAC "V'" THEN ASM SET_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `~compact_in top (X:A->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
      (* X lies in V, where the curvature is bounded *)
      SUBGOAL_THEN `(X:A->bool) SUBSET V` ASSUME_TAC THENL
       [MATCH_MP_TAC APXN_COVER_BY_FRONTIER THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `top frontier_of (V:A->bool)`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q':A` THEN
          EXPAND_TAC "V" THEN ASM SET_TAC[];
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `k:num`; `x:int->A`; `e:int->real^3->A`]
                    APXN_FIN_CHAIN_R_BOUND) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [USE_THEN "rat" (fun th -> MESON_TAC[th]); ASM_MESON_TAC[apx_balanced]];
        DISCH_THEN(X_CHOOSE_TAC `c1:real`)] THEN
      UNDISCH_TAC `~compact_in top (X:A->bool)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <=
                         max (C * mfd_scalar atlas g z0) c1}` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(p:A) IN V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [USE_THEN "u0b" (MP_TAC o C MATCH_MP (ASSUME `(p:A) IN U0`)) THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
          `(p:A) IN apx_chain_union eps {i:int | &0 <= i /\ i <= &k} (e:int->real^3->A)`) o
          check (fun th -> is_forall (concl th) && can (find_term ((=) `c1:real`)) (concl th))) THEN
        REAL_ARITH_TAC]];
    (* an infinite chain: the capped chain is the component W *)
    ABBREV_TAC `V = (U0:A->bool) UNION apx_chain_union eps {i:int | &0 <= i}
                                          (e:int->real^3->A)` THEN
    USE_THEN "tf" (MP_TAC o SPEC `--inv(&2 * eps)`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      STRIP_TAC] THEN
    SUBGOAL_THEN `closed_in top (V:A->bool) /\ open_in top V` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "V" THEN MATCH_MP_TAC APXN_CAPPED_INF_CLOSED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `e0:real^3->A`; `K:A->bool`; `x:int->A`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(K:A->bool) UNION IMAGE (e0:real^3->A)
                      (apx_slab (--inv eps) (--inv(&2 * eps))) UNION
                    IMAGE e0 (sphere(vec 0,exp(--inv(&2 * eps) / sqrt(&2))))` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET rfs_neck_dom eps /\
                      sphere(vec 0:real^3,exp(--inv(&2 * eps) / sqrt(&2))) SUBSET
                      rfs_neck_dom eps` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
            SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
             [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
            MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `apx_slab (--inv eps) (inv eps)` THEN
            CONJ_TAC THENL
             [MATCH_MP_TAC APXN_SPHERE_IN_SLAB THEN
              SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
               [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
              MATCH_MP_TAC APX_SLAB_SUB_DOM THEN REAL_ARITH_TAC]];
          UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U0 DIFF K` THEN
          UNDISCH_TAC `(K:A->bool) SUBSET U0` THEN SET_TAC[]];
        EXPAND_TAC "V" THEN MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `x:int->A`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`; `V:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~DISJOINT (W:A->bool) V` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q':A` THEN
      EXPAND_TAC "V" THEN ASM SET_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN `(q:A) IN V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_UNION; APXC_IN_CHAIN_UNION; IN_IMAGE] THEN
    STRIP_TAC THENL
     [USE_THEN "u0l" (MP_TAC o C MATCH_MP (ASSUME `(q:A) IN U0`)) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `q:A`)) THEN
    ASM_CASES_TAC `k = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(e:int->real^3->A)(&0) x' IN U0` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps) = U0 DIFF K` THEN
        UNDISCH_TAC `x' IN rfs_neck_dom eps` THEN SET_TAC[];
        DISCH_TAC THEN USE_THEN "u0l" (MP_TAC o C MATCH_MP (ASSUME
          `(e:int->real^3->A)(&0) x' IN U0`)) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:int->A)(&k) IN X /\
                  rfs_neck (top,atlas) (g:A->real^3^3) eps (x(&k)) ((e:int->real^3->A)(&k))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `&k:int` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `X:A->bool`)) (concl th) &&
          can (find_term ((=) `&1:int`)) (concl th))) THEN
        REWRITE_TAC[INT_OF_NUM_LE] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
        UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
        REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        REWRITE_TAC[INT_POS]];
      ALL_TAC] THEN
    USE_THEN "rat" (MP_TAC o SPECL [`(x:int->A)(&k)`; `(e:int->real^3->A)(&k)`; `x':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "lev" (MP_TAC o C MATCH_MP (ASSUME `(x:int->A)(&k) IN X`)) THEN
    SUBGOAL_THEN `L <= C * L` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Components of the high-curvature set.  A component of a                  *)
(* closed set X is closed, connected and maximal; inside a component W with  *)
(* a point of curvature below Lam, every component of the set R >= Lam of W *)
(* contains a point with R = Lam.                                            *)
(* ------------------------------------------------------------------------- *)

let APXN_SUBCOMP_FACTS = prove
 (`!top (X:A->bool) Xb.
     closed_in top X /\ Xb IN connected_components_of (subtopology top X)
     ==> closed_in top Xb /\ connected_in top Xb /\ Xb SUBSET X /\ ~(Xb = {}) /\
         (!Z. connected_in top Z /\ Z SUBSET X /\ ~DISJOINT Z Xb ==> Z SUBSET Xb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN EXISTS_TAC `X:A->bool` THEN
    ASM_SIMP_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
    MP_TAC(ISPECL [`subtopology top (X:A->bool)`; `Xb:A->bool`]
                  CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
    ASM_SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    MP_TAC(ISPECL [`subtopology top (X:A->bool)`; `Xb:A->bool`]
                  CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
    ASM_SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top (X:A->bool)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM_MESON_TAC[DISJOINT_SYM]]);;

let APXN_FRONTIER_LEVEL = prove
 (`!top atlas (g:A->real^3^3) W Lam Xb.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     W IN connected_components_of top /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
     (?q. q IN W /\ mfd_scalar atlas g q < Lam)
     ==> ?y. y IN Xb /\ mfd_scalar atlas g y = Lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `X = {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (mfd_scalar atlas (g:A->real^3^3))`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x} =
                  W INTER {x | x IN topspace top /\ mfd_scalar atlas g x IN {t | t >= Lam}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; real_ge] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_GE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `X:A->bool`; `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!y:A. y IN Xb ==> Lam < mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN X` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Xb:A->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `top:A topology` LOCALLY_CONNECTED_SPACE) THEN
    SUBGOAL_THEN `locally_connected_space (top:A topology)` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
      MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`W INTER {x:A | x IN topspace top /\ mfd_scalar atlas (g:A->real^3^3) x IN {t | t > Lam}}`;
       `y:A`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
        REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT];
        REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN
        SUBGOAL_THEN `(y:A) IN X` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "X" THEN UNDISCH_TAC `(N:A->bool) SUBSET
        W INTER {x | x IN topspace top /\ mfd_scalar atlas (g:A->real^3^3) x IN {t | t > Lam}}` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_gt] THEN MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `W:A->bool`; `Xb:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~DISJOINT (W:A->bool) Xb` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~(Xb:A->bool = {})` THEN UNDISCH_TAC `(Xb:A->bool) SUBSET X` THEN
    EXPAND_TAC "X" THEN SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(q:A) IN X` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;
let APXN_FINSET_CHAIN_R_BOUND = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A).
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
                          ==> mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     apx_chain (top,atlas) g eps Ix x e /\ FINITE Ix
     ==> ?c. !p. p IN apx_chain_union eps Ix e ==> mfd_scalar atlas g p <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\i:int. mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)`;
                 `Ix:int->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `&101 / &100 * max a (&0)` THEN
  REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&101 / &100 * mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> can (find_term ((=) `a:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let APXN_LEVEL_CLOSED = prove
 (`!top atlas (g:A->real^3^3) W Lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ closed_in top W
     ==> closed_in top {x | x IN W /\ Lam <= mfd_scalar atlas g x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (mfd_scalar atlas (g:A->real^3^3))`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x} =
                W INTER {x | x IN topspace top /\ mfd_scalar atlas g x IN {t | t >= Lam}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; real_ge] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] CLOSED_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_GE]);;
(* A noncompact component Xb of R >= Lam in W (all points NK-centres) lies *)
(* in the union of a one-sided infinite chain of Xb-centred NK-necks, one   *)
(* of which is centred at a point with R = Lam.                              *)

let APXN_HORN_CHAIN = prove
 (`!top atlas (g:A->real^3^3) eps NK W L Lam Xb.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     &0 < L /\ &100 / &99 * L < Lam /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?q. q IN W /\ mfd_scalar atlas g q <= L) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
     ~compact_in top Xb /\ (!x. x IN Xb ==> ?e. NK x e)
     ==> ?x e j0. apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
                  (!i. &0 <= i ==> x i IN Xb /\ (NK (x i) (e i) \/ NK (x i) (apx_rev (e i)))) /\
                  Xb SUBSET apx_chain_union eps {i:int | &0 <= i} e /\
                  mfd_scalar atlas g (x(&j0)) = Lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas (g:A->real^3^3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ch_ctx]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `Lam:real`] APXN_LEVEL_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`; `Xb:A->bool`]
                APXN_SUBCOMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `Lam:real`; `Xb:A->bool`] APXN_FRONTIER_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y0:A) IN Xb`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `NK:A->(real^3->A)->bool`)) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `e0:real^3->A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `Xb:A->bool`; `y0:A`; `e0:real^3->A`]
                APXN_GROW2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:int`; `b:int`; `x:int->A`; `e:int->real^3->A`] THEN
    REWRITE_TAC[apxn_good] THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `{i:int | a <= i /\ i <= b}`; `x:int->A`; `e:int->real^3->A`]
                  APXN_FINSET_CHAIN_R_BOUND) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_INT_SEG] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[apx_balanced]];
      DISCH_THEN(X_CHOOSE_TAC `c:real`)] THEN
    UNDISCH_TAC `~compact_in top (Xb:A->bool)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= c}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ix:int->bool` (X_CHOOSE_THEN `x:int->A`
    (X_CHOOSE_THEN `e:int->real^3->A` STRIP_ASSUME_TAC))) THENL
   [(* a half line upwards: shift *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:int->A`; `e:int->real^3->A`; `a:int`] APXN_CHAIN_SHIFT_UP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\i. (x:int->A)(i + a)`; `\i. (e:int->real^3->A)(i + a)`;
                          `num_of_int(--a)`] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:int` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_INT_ARITH_TAC;
      SUBGOAL_THEN `&(num_of_int(--a)) + a = &0:int` SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 <= --a:int` MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[INT_OF_NUM_OF_INT] THEN INT_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    (* a half line downwards: reverse and shift *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `{i:int | i <= b}`; `x:int->A`; `e:int->real^3->A`]
                  APXN_CHAIN_REV) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{i:int | --i IN {i | i <= b}} = {i | --b <= i}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `\i. (x:int->A)(--i)`; `\i. apx_rev((e:int->real^3->A)(--i))`;
                   `--b:int`] APXN_CHAIN_SHIFT_UP) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\i. (x:int->A)(--(i + --b))`;
                          `\i. apx_rev((e:int->real^3->A)(--(i + --b)))`; `num_of_int b`] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `--(i + --b):int` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `Xb:A->bool`)) (concl th) &&
        can (find_term ((=) `NK:A->(real^3->A)->bool`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM; APX_REV_REV] THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[];
      SUBGOAL_THEN `--(&(num_of_int b) + --b) = &0:int` SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 <= b:int` MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[INT_OF_NUM_OF_INT] THEN INT_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    (* all integers: the union would be the whole component *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `closed_in top (apx_chain_union eps (:int) (e:int->real^3->A)) /\
                  open_in top (apx_chain_union eps (:int) e)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC APXN_BI_CLOSED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `x:int->A`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                              `x:int->A`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`; `apx_chain_union eps (:int) (e:int->real^3->A)`]
                  CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~DISJOINT (W:A->bool) (apx_chain_union eps (:int) (e:int->real^3->A))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y0:A` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      DISCH_TAC] THEN
    SUBGOAL_THEN `(q:A) IN apx_chain_union eps (:int) (e:int->real^3->A)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `Xb:A->bool`)) (concl th) &&
      can (find_term ((=) `NK:A->(real^3->A)->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i) ((e:int->real^3->A) i)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps (:int) x e` THEN
      REWRITE_TAC[apx_chain; IN_UNIV] THEN SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(x:int->A) i`; `(e:int->real^3->A) i`; `z:real^3`] o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `&99 / &100`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `Lam <= mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` MP_TAC THENL
     [SUBGOAL_THEN `(x:int->A) i IN {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`
      MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) q <= L` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `q:A`)) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The horn chart of a noncompact component.  Small facts,                  *)
(* the truncation index, and the horn built from the chain chart of the     *)
(* tail of the chain.                                                        *)
(* ------------------------------------------------------------------------- *)

let APXN_EXP_SMALL = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024 ==> exp(--inv eps / sqrt(&2)) < &1 / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= inv eps / sqrt(&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps / sqrt(&2) = --(inv eps / sqrt(&2))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG]; REWRITE_TAC[REAL_EXP_NEG]] THEN
  MP_TAC(SPEC `inv eps / sqrt(&2)` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 < exp(inv eps / sqrt(&2))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < inv(&2) ==> x < &1 / &2`) THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC);;

let APXN_OPEN_OUTER = prove
 (`!r. open {y:real^3 | r < norm y}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | r < norm y} = (:real^3) DIFF cball(vec 0,r)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_CBALL_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]]);;

let APXN_REV_IMAGE_SPHERE = prove
 (`!e:real^3->A. IMAGE (apx_rev e) (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!x:real^3. x IN s ==> (f:real^3->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  REWRITE_TAC[IN_SPHERE_0; apx_rev] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID]);;
let APXN_TRUNC_INDEX = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) W lam j0.
     apx_ch_ctx top atlas g eps /\ apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
     (!i. &0 <= i ==> x i IN W) /\
     compact_in top {x | x IN W /\ mfd_scalar atlas g x <= lam} /\
     mfd_scalar atlas g (x(&j0)) < lam
     ==> ?m0. mfd_scalar atlas g (x(&m0)) < lam /\
              !n. m0 < n ==> lam <= mfd_scalar atlas g (x(&n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `{i:int | &0 <= i}`; `x:int->A`; `e:int->real^3->A`;
                 `{i:int | &0 <= i /\ mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) < lam}`;
                 `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= lam}`]
                APXN_CHAIN_FINITE_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_TAC] THEN
  SUBGOAL_THEN `FINITE {n:num | mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&n)) < lam}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE num_of_int
      {i:int | &0 <= i /\ mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) < lam}` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXISTS_TAC `&n:int` THEN
    ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num. n`;
                 `{n:num | mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&n)) < lam}`]
                UPPER_BOUND_FINITE_SET) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\n:num. mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&n)) < lam` num_MAX) THEN
  BETA_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL [EXISTS_TAC `j0:num` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m0:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term ((=) `m0:num`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let APXN_CHAIN_TAIL = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) m.
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
     ==> apx_chain (top,atlas) g eps {i:int | &0 <= i} (\i. x(i + &m)) (\i. e(i + &m)) /\
         apx_chain_union eps {i:int | &0 <= i} (\i. e(i + &m)) =
         apx_chain_union eps {i:int | &m <= i} e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC APXN_CHAIN_SHIFT_UP THEN
  MATCH_MP_TAC APX21_SUBCHAIN THEN EXISTS_TAC `{i:int | &0 <= i}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apx_int_interval; IN_ELIM_THM] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&m:int` THEN
    REWRITE_TAC[INT_LE_REFL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MP_TAC(SPEC `m:num` INT_POS) THEN INT_ARITH_TAC]);;
let APXN_CONSEC_RATIO = prove
 (`!top atlas (g:A->real^3^3) eps Ix x (e:int->real^3->A) i.
     &0 < eps /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     apx_chain (top,atlas) g eps Ix x e /\ i IN Ix /\ (i + &1) IN Ix
     ==> &99 / &100 * mfd_scalar atlas g (x(i + &1)) <=
         &101 / &100 * mfd_scalar atlas g (x i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rat") MP_TAC)) THEN
  REWRITE_TAC[apx_chain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^3. y IN apx_slab (inv(&2 * eps)) (inv eps)` (X_CHOOSE_TAC `y:real^3`) THENL
   [MATCH_MP_TAC APX_SLAB_NONEMPTY THEN REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t x:real^3. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `apx_slab (inv(&2 * eps)) (inv eps)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_SLAB_SUB_DOM THEN REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A) i y`) THEN
  ANTS_TAC THENL [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i) ((e:int->real^3->A) i) /\
                rfs_neck (top,atlas) g eps (x(i + &1)) (e(i + &1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "rat" (MP_TAC o SPECL [`(x:int->A) i`; `(e:int->real^3->A) i`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "rat" (MP_TAC o SPECL [`(x:int->A)(i + &1)`; `(e:int->real^3->A)(i + &1)`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(e:int->real^3->A) i y = e (i + &1) z` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN REAL_ARITH_TAC);;

let APXN_NECK_IN_SUBCOMP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) W Lam Xb.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     W IN connected_components_of top /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
     rfs_neck (top,atlas) g eps x e /\ x IN Xb /\ Lam <= &99 / &100 * mfd_scalar atlas g x
     ==> IMAGE e (rfs_neck_dom eps) SUBSET Xb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `Lam:real`] APXN_LEVEL_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`; `Xb:A->bool`]
                APXN_SUBCOMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; APX_CONNECTED_ANNULUS3] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck; rfs_neck_dom];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `x:A`; `e:real^3->A`; `W:A->bool`] APXN_NECK_IN_COMPONENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `y:real^3`] o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `&99 / &100`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The horn of a noncompact component (R bounds on compact                  *)
(* sets, properness of the chain chart, the cover of the rest, APXN_HORN).  *)
(* ------------------------------------------------------------------------- *)

(* Small tools for the horn: R bounded above on compact sets, finite sets of *)
(* integers bounded above, the inner slab of the chart, properness of the   *)
(* chain chart, and the cover of the rest.                                   *)

let APXN_SCALAR_UPPER = prove
 (`!top atlas (g:A->real^3^3) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?c. !p. p IN K ==> mfd_scalar atlas g p <= c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `mfd_scalar atlas (g:A->real^3^3)`;
                 `K:A->bool`] IMAGE_COMPACT_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
              FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN EXISTS_TAC `B:real` THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let APXN_FINITE_NONNEG_BOUND = prove
 (`!S:int->bool. FINITE S ==> ?n:num. !i. i IN S /\ &0 <= i ==> i <= &n`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE num_of_int S` num_FINITE) THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `i:int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int i`) THEN REWRITE_TAC[IN_IMAGE] THEN
  ANTS_TAC THENL [EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let APXN_INNER_SLAB = prove
 (`!eps (y:real^3).
     &0 < eps /\ exp(--inv eps / sqrt(&2)) < norm y /\ norm y <= &1
     ==> y IN apx_slab (--inv eps) (inv(&8 * eps)) /\ y IN rfs_neck_dom eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (inv(&8 * eps))` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_DIV THEN
    SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`--inv eps`; `inv(&8 * eps)`; `eps:real`] APX_SLAB_SUB_DOM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

(* Properness of a chain chart: the chart preimage of a compact set is      *)
(* bounded (finitely many necks meet it, their centres having bounded R).    *)

let APXN_CHART_PROPER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) W (E:real^3->A).
     apx_ch_ctx top atlas g eps /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
     (!i. &0 <= i ==> x i IN W) /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
     IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
       apx_chain_union eps {i:int | &0 <= i} e /\
     (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                IMAGE E (apx_slab (--inv eps) rho))
     ==> !K'. compact_in top K'
              ==> bounded {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y /\ E y IN K'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `K':A->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?c. !p. p IN K' ==> mfd_scalar atlas (g:A->real^3^3) p <= c`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_SCALAR_UPPER THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {i:int | &0 <= i /\
                         ~DISJOINT (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)) K'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_CHAIN_FINITE_SUB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `{i:int | &0 <= i}`; `x:int->A`; `e:int->real^3->A`;
      `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= &2 * c}`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~DISJOINT (IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)) K'` THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i)
                           ((e:int->real^3->A) i)` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
      REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * mfd_scalar atlas (g:A->real^3^3) p` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC(REAL_ARITH `a <= c ==> &2 * a <= &2 * c`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o REWRITE_RULE[IN_ELIM_THM] o
                MATCH_MP APXN_FINITE_NONNEG_BOUND) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `rho:real` o SPEC `n:num`) THEN
  REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `exp(rho / sqrt(&2))` THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E:real^3->A) y IN apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e`
  MP_TAC THENL
   [MP_TAC(ASSUME `IMAGE (E:real^3->A) {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                   apx_chain_union eps {i:int | &0 <= i} e`) THEN
    DISCH_THEN(MP_TAC o SPEC `(E:real^3->A) y` o REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
     [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(E:real^3->A) y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^3. z IN apx_slab (--inv eps) rho /\ (E:real^3->A) y = E z`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`apx_chain_union eps {i:int | &0 <= i /\ i <= &n} (e:int->real^3->A) SUBSET
       IMAGE (E:real^3->A) (apx_slab (--inv eps) rho)`;
      `(E:real^3->A) y IN apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN apx_slab (--inv eps) rho` THEN
  REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `y:real^3 = z` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `{y:real^3 | exp(--inv eps / sqrt(&2)) < norm y}`; `E:real^3->A`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ASM_REAL_ARITH_TAC]);;

(* Outside the open outer part of the chart, the chain union is covered by  *)
(* the necks of indices 0 .. m.                                              *)

let APXN_REST_COVER = prove
 (`!eps (e:int->real^3->A) m (E:real^3->A) X.
     &0 < eps /\
     X SUBSET apx_chain_union eps {i:int | &0 <= i} e /\
     (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&m) y) /\
     IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
       apx_chain_union eps {i:int | &m <= i} e
     ==> X SUBSET apx_chain_union eps {i:int | &0 <= i /\ i <= &m} e UNION
                  IMAGE E {y:real^3 | &1 < norm y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?i:int. &0 <= i /\ (p:A) IN IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `X SUBSET apx_chain_union eps {i:int | &0 <= i} (e:int->real^3->A)` THEN
    REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(i:int) <= &m` THENL
   [DISJ1_TAC THEN REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN IMAGE (E:real^3->A) {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y}`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((i:int) <= &m)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `&1 < norm(z:real^3)` THENL
   [DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    DISJ1_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APXN_INNER_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[apx_chain_union; UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `&m:int` THEN
  REWRITE_TAC[INT_POS; INT_LE_REFL; IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN
  ASM_SIMP_TAC[]);;

(* The horn of a noncompact component Xb of R >= (5/4) C L whose points are *)
(* all NK-centres: the chain chart of the tail of its chain after the last  *)
(* centre with R < (3/2) C L.                                                *)

let APXN_HORN = prove
 (`!top atlas (g:A->real^3^3) C eps NK W L Xb.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     (!x (e:int->real^3->A). apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
        ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
                (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                apx_chain_union eps {i:int | &0 <= i} e /\
                (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                           IMAGE E (apx_slab (--inv eps) rho))) /\
     &1 <= C /\ &0 < L /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?q. q IN W /\ mfd_scalar atlas g q <= L) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas g x}) /\
     ~compact_in top Xb /\ (!x. x IN Xb ==> ?e. NK x e)
     ==> ?H:real^3->A.
           mfd_param top atlas {y | &1 / &2 < norm y} H /\
           IMAGE H {y | &1 / &2 < norm y} SUBSET W /\
           (!K'. compact_in top K' ==> bounded {y | &1 <= norm y /\ H y IN K'}) /\
           (!y. &1 <= norm y
                ==> C * L < mfd_scalar atlas g (H y) /\ (?e. NK (H y) e) /\ H y IN Xb) /\
           (!y. norm y = &1 ==> mfd_scalar atlas g (H y) <= &2 * C * L) /\
           (?x e. NK x e /\ IMAGE e (sphere(vec 0,&1)) = IMAGE H (sphere(vec 0,&1))) /\
           (?c. !p. p IN Xb /\ ~(p IN IMAGE H {y | &1 < norm y})
                    ==> mfd_scalar atlas g p <= c) /\
           (?x e. rfs_neck (top,atlas) g eps x e /\ IMAGE e (rfs_neck_dom eps) SUBSET Xb /\
                  mfd_scalar atlas g x <= &2 * C * L)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["ctx"; "pair"; "more"; "n4r"; "ext"; "sep"; "rat"; "chart"; "C1"; "L0"; "WC";
     "prop"; "low"; "nkn"; "xbc"; "ncpt"; "xbnk"] (CONJUNCTS th))) THEN
  USE_THEN "ctx" (MP_TAC o REWRITE_RULE[apx_ch_ctx]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}`;
                 `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  (* the chain of Xb *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `NK:A->(real^3->A)->bool`; `W:A->bool`; `L:real`;
                 `&5 / &4 * C * L`; `Xb:A->bool`] APXN_HORN_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `L <= C * L` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < L` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int->A` (X_CHOOSE_THEN `e:int->real^3->A`
    (X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!i. &0 <= i ==> rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A) i)
                                         ((e:int->real^3->A) i)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. &0 <= i ==> (x:int->A) i IN W` ASSUME_TAC THENL
   [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:int->A) i IN Xb` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\
                                  &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the truncation index *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:int->A`; `e:int->real^3->A`; `W:A->bool`; `&3 / &2 * C * L`;
                 `j0:num`] APXN_TRUNC_INDEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < C * L` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `m0:num` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `m = SUC m0` THEN
  SUBGOAL_THEN `!i. &m <= i ==> &3 / &2 * C * L <= mfd_scalar atlas (g:A->real^3^3)
                                                    ((x:int->A) i)` ASSUME_TAC THENL
   [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k. i:int = &k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
     [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN MP_TAC(SPEC `m:num` INT_POS) THEN
      UNDISCH_TAC `(&m:int) <= i` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(&m:int) <= &k` THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the necks of the tail lie in Xb *)
  SUBGOAL_THEN `!i. &m <= i ==> IMAGE ((e:int->real^3->A) i) (rfs_neck_dom eps) SUBSET Xb`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= i:int` ASSUME_TAC THENL
     [MP_TAC(SPEC `m:num` INT_POS) THEN UNDISCH_TAC `(&m:int) <= i` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC APXN_NECK_IN_SUBCOMP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `(x:int->A) i`; `W:A->bool`; `&5 / &4 * C * L`] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < c /\ &3 / &2 * c <= r ==> &5 / &4 * c <= &99 / &100 * r`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_chain_union eps {i:int | &m <= i} (e:int->real^3->A) SUBSET Xb`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_chain_union; UNIONS_SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* R at the first centre of the tail *)
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) <= &8 / &5 * C * L`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `{i:int | &0 <= i}`; `x:int->A`; `e:int->real^3->A`;
                   `&m0:int`] APXN_CONSEC_RATIO) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; INT_OF_NUM_ADD; INT_POS; GSYM ADD1] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < C * L`;
      `mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m0)) < &3 / &2 * C * L`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the tail chain and its chart *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:int->A`; `e:int->real^3->A`; `m:num`] APXN_CHAIN_TAIL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN USE_THEN "chart" (MP_TAC o C MATCH_MP th)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[INT_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `\i:int. (x:int->A)(i + &m)`; `\i:int. (e:int->real^3->A)(i + &m)`;
                 `W:A->bool`; `E:real^3->A`] APXN_CHART_PROPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC(SPEC `m:num` INT_POS) THEN
    UNDISCH_TAC `&0 <= i:int` THEN INT_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `Xb SUBSET apx_chain_union eps {i:int | &0 <= i /\ i <= &m} (e:int->real^3->A)
                UNION IMAGE (E:real^3->A) {y:real^3 | &1 < norm y}` ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_REST_COVER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?c. !p. p IN apx_chain_union eps {i:int | &0 <= i /\ i <= &m}
                                             (e:int->real^3->A)
                        ==> mfd_scalar atlas (g:A->real^3^3) p <= c` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_FIN_CHAIN_R_BOUND THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `x:int->A`] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "rat" (MP_TAC o C MATCH_MP th)) THEN
      SIMP_TAC[];
      MATCH_MP_TAC APXC_SUBCHAIN_UPTO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_EXP_SMALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. norm y = &1 ==> (E:real^3->A) y = (e:int->real^3->A) (&m) y /\
                                         y IN rfs_neck_dom eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`eps:real`; `y:real^3`] APXN_INNER_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `exp(--inv eps / sqrt(&2)) < &1 / &2` THEN
      REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `E:real^3->A` THEN
  (* the parametrization of the outer part *)
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `{y:real^3 | exp(--inv eps / sqrt(&2)) < norm y}` THEN
    ASM_REWRITE_TAC[APXN_OPEN_OUTER; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    UNDISCH_TAC `exp(--inv eps / sqrt(&2)) < &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* inside W *)
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (E:real^3->A) {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN UNDISCH_TAC `exp(--inv eps / sqrt(&2)) < &1 / &2` THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Xb:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\
                                    &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* properness *)
  CONJ_TAC THENL
   [X_GEN_TAC `K':A->bool` THEN DISCH_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{y:real^3 | exp(--inv eps / sqrt(&2)) < norm y /\ (E:real^3->A) y IN K'}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `exp(--inv eps / sqrt(&2)) < &1 / &2` THEN
    UNDISCH_TAC `&1 <= norm(y:real^3)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the points of the closed outer part *)
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^3->A) y IN Xb` ASSUME_TAC THENL
     [SUBGOAL_THEN `(E:real^3->A) y IN
                    IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y}` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `exp(--inv eps / sqrt(&2)) < &1 / &2` THEN
        UNDISCH_TAC `&1 <= norm(y:real^3)` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `apx_chain_union eps {i:int | &m <= i} (e:int->real^3->A) SUBSET Xb` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) ((E:real^3->A) y)`
      MP_TAC THENL
       [UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\
                                      &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
        UNDISCH_TAC `(E:real^3->A) y IN Xb` THEN SET_TAC[];
        UNDISCH_TAC `&0 < C * L` THEN REAL_ARITH_TAC];
      UNDISCH_TAC `(E:real^3->A) y IN Xb` THEN USE_THEN "xbnk" MATCH_ACCEPT_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the unit sphere *)
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^3->A) y = (e:int->real^3->A) (&m) y /\ y IN rfs_neck_dom eps`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((e:int->real^3->A) (&m) y) <=
                  &101 / &100 * mfd_scalar atlas g ((x:int->A)(&m))` MP_TAC THENL
     [USE_THEN "rat" (MP_TAC o SPECL [`(x:int->A)(&m)`; `(e:int->real^3->A)(&m)`;
                                      `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[INT_POS]; SIMP_TAC[]];
      MAP_EVERY UNDISCH_TAC
       [`mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) <= &8 / &5 * C * L`;
        `&0 < C * L`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the inner sphere is the sphere of an NK-neck *)
  CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (E:real^3->A) (sphere(vec 0,&1)) =
                  IMAGE ((e:int->real^3->A)(&m)) (sphere(vec 0,&1))` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!y:real^3. y IN s ==> (f:real^3->A) y = g y) ==> IMAGE f s = IMAGE g s`) THEN
      REWRITE_TAC[IN_SPHERE_0] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(x:int->A)(&m)` THEN
    SUBGOAL_THEN `(NK:A->(real^3->A)->bool) ((x:int->A)(&m)) ((e:int->real^3->A)(&m)) \/
                  NK (x(&m)) (apx_rev(e(&m)))` MP_TAC THENL
     [ASM_SIMP_TAC[INT_POS]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `(e:int->real^3->A)(&m)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `apx_rev((e:int->real^3->A)(&m))` THEN
      ASM_REWRITE_TAC[APXN_REV_IMAGE_SPHERE]];
    ALL_TAC] THEN
  (* the rest of Xb has bounded R *)
  CONJ_TAC THENL
   [EXISTS_TAC `c:real` THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`Xb SUBSET apx_chain_union eps {i:int | &0 <= i /\ i <= &m} (e:int->real^3->A) UNION
                 IMAGE (E:real^3->A) {y:real^3 | &1 < norm y}`;
      `(p:A) IN Xb`; `~((p:A) IN IMAGE (E:real^3->A) {y:real^3 | &1 < norm y})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the first neck of the tail *)
  EXISTS_TAC `(x:int->A)(&m)` THEN EXISTS_TAC `(e:int->real^3->A)(&m)` THEN
  ASM_SIMP_TAC[INT_POS; INT_LE_REFL] THEN
  MAP_EVERY UNDISCH_TAC
   [`mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) <= &8 / &5 * C * L`; `&0 < C * L`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Packing.  Separated and disjoint-neck families in compact                *)
(* sets are finite; intermediate values of R; necks in high components;   *)
(* only finitely many components of R >= Lam reach R >= 2 C Lam.           *)
(* ------------------------------------------------------------------------- *)

(* Packing: index families of points of a compact set that are separated  *)
(* in the manifold distance are finite; so are families of pairwise        *)
(* disjoint necks with centres in a compact set.                            *)

let APXN_SEPARATED_FINITE = prove
 (`!top atlas (g:A->real^3^3) (S:B->bool) (x:B->A) K r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < r /\
     compact_in top K /\ (!i. i IN S ==> x i IN K) /\
     (!i j. i IN S /\ j IN S /\ mfd_joinable (top,atlas) (x i) (x j) /\
            mfd_dist (top,atlas) g (x i) (x j) < r ==> i = j)
     ==> FINITE S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  SUBGOAL_THEN `!i. i IN S ==> ?Q. Q IN V /\ (x:B->A) i IN Q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:B->A) i IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\i. @Q. Q IN V /\ (x:B->A) i IN Q) (S:B->bool))` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:(A->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `i:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:B) IN S`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:B`; `j:B`] THEN BETA_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B0 = @Q. Q IN V /\ (x:B->A) i IN Q` THEN
  SUBGOAL_THEN `B0 IN V /\ (x:B->A) i IN B0 /\ x j IN B0` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(i:B) IN S`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SELECT_RULE o C MATCH_MP (ASSUME `(j:B) IN S`) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `V:(A->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. p IN K /\ B0 = mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `B0 IN (V:(A->bool)->bool)` THEN
    UNDISCH_TAC `V SUBSET {mfd_ball (top,atlas) (g:A->real^3^3) p (r / &2) | p IN K}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:B->A) i IN B0` THEN UNDISCH_TAC `(x:B->A) j IN B0` THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,(atlas:((A->bool)#(A->real^3))->bool)) ((x:B->A) i) p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(x:B->A) i`;
                   `p:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `r:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:B->A) i) p +
                mfd_dist (top,atlas) g p (x j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `(x:B->A) i`; `p:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]]);;

let APXN_DISJOINT_NECKS_FINITE = prove
 (`!top atlas (g:A->real^3^3) eps (S:B->bool) (x:B->A) (e:B->real^3->A) K.
     apx_ch_ctx top atlas g eps /\
     (!i. i IN S ==> rfs_neck (top,atlas) g eps (x i) (e i)) /\
     (!i j. i IN S /\ j IN S /\ ~(i = j)
            ==> DISJOINT (IMAGE (e i) (rfs_neck_dom eps)) (IMAGE (e j) (rfs_neck_dom eps))) /\
     compact_in top K /\ (!i. i IN S ==> x i IN K)
     ==> FINITE S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `?Rm. &1 <= Rm /\ !p. p IN K ==> mfd_scalar atlas (g:A->real^3^3) p <= Rm`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `K:A->bool`] APXN_SCALAR_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c0:real`) THEN
    EXISTS_TAC `max (&1) c0` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
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
  MATCH_MP_TAC APXN_SEPARATED_FINITE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `x:B->A`; `K:A->bool`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:B`; `j:B`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:B->A) i) ((e:B->real^3->A) i) /\
                rfs_neck (top,atlas) g eps (x j) (e j)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:B->A) i))) *
                     inv(&8 * eps)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:B->A) i)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:B->A) i) ((e:B->real^3->A) i)` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:B->A) i`; `(e:B->real^3->A) i`; `(x:B->A) j`]
                APX_CENTRE_DEEP_BALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:B->A) j IN IMAGE ((e:B->real^3->A) j) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:B->A) j) ((e:B->real^3->A) j)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:B->A) j IN IMAGE ((e:B->real^3->A) j) (rfs_neck_dom eps)` MP_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:B->A) j IN IMAGE ((e:B->real^3->A) j) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:B->A) j IN IMAGE ((e:B->real^3->A) i) (rfs_neck_dom eps)` MP_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:B`; `j:B`] o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]);;

(* Intermediate values of R on a connected set. *)

let APXN_IVT_CONNECTED = prove
 (`!top atlas (g:A->real^3^3) S a b c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_in top S /\
     a IN S /\ b IN S /\ mfd_scalar atlas g a <= c /\ c <= mfd_scalar atlas g b
     ==> ?w. w IN S /\ mfd_scalar atlas g w = c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `top:A topology`; `euclideanreal`;
                 `S:A->bool`] CONNECTED_IN_CONTINUOUS_MAP_IMAGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL; is_realinterval] THEN
  DISCH_THEN(MP_TAC o SPECL [`mfd_scalar atlas (g:A->real^3^3) a`;
                             `mfd_scalar atlas (g:A->real^3^3) b`; `c:real`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* A point w of a component Xb of R >= Lam with R w >= 2 C Lam that is an   *)
(* NK-centre or a cap core point gives a neck inside Xb centred at a point  *)
(* with R <= C R(w) (the neck at w, or the end neck of the cap, whose whole *)
(* domain U lies in Xb by the curvature ratio bound of the cap).             *)

let APXN_LEVEL_NECK = prove
 (`!top atlas (g:A->real^3^3) C eps NK W Lam Xb w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     W IN connected_components_of top /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     &1 <= C /\ &0 < Lam /\ w IN Xb /\ &2 * C * Lam <= mfd_scalar atlas g w /\
     ((?e. NK w e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y))
     ==> ?z e. rfs_neck (top,atlas) g eps z e /\ IMAGE e (rfs_neck_dom eps) SUBSET Xb /\
               mfd_scalar atlas g z <= C * mfd_scalar atlas g w`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 < C * Lam /\ Lam <= C * Lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < C * Lam`; `&2 * C * Lam <= mfd_scalar atlas (g:A->real^3^3) w`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) w <= C * mfd_scalar atlas g w` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * r <= C * r ==> r <= C * r`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`;
                 `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* w is an NK-centre *)
    FIRST_X_ASSUM(X_CHOOSE_TAC `e:real^3->A`) THEN
    MAP_EVERY EXISTS_TAC [`w:A`; `e:real^3->A`] THEN
    SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps w e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_NECK_IN_SUBCOMP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `w:A`; `W:A->bool`; `Lam:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < C * Lam`; `Lam <= C * Lam`;
      `&2 * C * Lam <= mfd_scalar atlas (g:A->real^3^3) w`] THEN
    REAL_ARITH_TAC;
    (* w is a cap core point *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CAP_DATA) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e:real^3->A` (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `e':real^3->A`
       (X_CHOOSE_THEN `z':A` (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC))))))) THEN
    SUBGOAL_THEN `(w:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:A) IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
      UNDISCH_TAC `(w:A) IN Xb` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET W` ASSUME_TAC THENL
     [MATCH_MP_TAC APXN_CAP_IN_COMPONENT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `C:real`; `eps:real`; `Y:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y:A. y IN U ==> Lam <= mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `y:A`; `w:A`]
                    APX22_CAP_RATIO) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `C * (&2 * Lam) < C * mfd_scalar atlas (g:A->real^3^3) y` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&2 * C * Lam <= mfd_scalar atlas (g:A->real^3^3) w`;
          `mfd_scalar atlas (g:A->real^3^3) w < C * mfd_scalar atlas g y`] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN UNDISCH_TAC `&0 < Lam` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET Xb` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `Xb:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC APX21_CAP_CONNECTED THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
          `C:real`; `eps:real`; `Y:A->bool`] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:A) IN U` ASSUME_TAC THENL
     [SUBGOAL_THEN `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` MP_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) = U DIFF K` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `e:real^3->A`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(U:A->bool) SUBSET Xb` THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `w:A`; `z:A`]
                    APX22_CAP_RATIO) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* Only finitely many components of R >= Lam in W reach R >= 2 C Lam: each *)
(* contains a neck centred at R <= 2 C^2 Lam (a point with R = 2 C Lam by   *)
(* intermediate values, then APXN_LEVEL_NECK), and these necks are disjoint. *)

let APXN_HIGH_COMPS_FINITE = prove
 (`!top atlas (g:A->real^3^3) C eps NK W Lam.
     apx_ch_ctx top atlas g eps /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     &1 <= C /\ &0 < Lam /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?q. q IN W /\ mfd_scalar atlas g q < Lam) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN W /\ Lam <= mfd_scalar atlas g x
          ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
     ==> FINITE {Xb | Xb IN connected_components_of
                        (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
                      ?w. w IN Xb /\ &2 * C * Lam <= mfd_scalar atlas g w}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < C * Lam /\ Lam <= C * Lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Xb. Xb IN {Xb | Xb IN connected_components_of
                        (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
                      ?w. w IN Xb /\ &2 * C * Lam <= mfd_scalar atlas (g:A->real^3^3) w}
         ==> ?z e. rfs_neck (top,atlas) g eps z e /\ IMAGE e (rfs_neck_dom eps) SUBSET Xb /\
                   mfd_scalar atlas g z <= C * &2 * C * Lam`
  MP_TAC THENL
   [X_GEN_TAC `Xb:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w0:A` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                  APXN_COMPONENT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`;
                   `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `W:A->bool`; `Lam:real`; `Xb:A->bool`] APXN_FRONTIER_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Xb:A->bool`; `y0:A`; `w0:A`; `&2 * C * Lam`] APXN_IVT_CONNECTED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`&0 < C * Lam`; `Lam <= C * Lam`] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(w:A) IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) w` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
      UNDISCH_TAC `(w:A) IN Xb` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(?e. (NK:A->(real^3->A)->bool) w e) \/
                  (?U Y. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\ w IN Y)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * C * Lam <= mfd_scalar atlas (g:A->real^3^3) w` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rand(concl th) = `&2 * C * Lam`)) THEN
    MATCH_MP_TAC APXN_LEVEL_NECK THEN
    MAP_EVERY EXISTS_TAC [`NK:A->(real^3->A)->bool`; `W:A->bool`; `Lam:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `zf:(A->bool)->A` (X_CHOOSE_THEN `ef:(A->bool)->real^3->A`
    (LABEL_TAC "sk"))) THEN
  MATCH_MP_TAC APXN_DISJOINT_NECKS_FINITE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `zf:(A->bool)->A`; `ef:(A->bool)->real^3->A`;
    `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= C * &2 * C * Lam}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `Xb:A->bool` THEN DISCH_TAC THEN
    USE_THEN "sk" (MP_TAC o SPEC `Xb:A->bool`) THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`X1:A->bool`; `X2:A->bool`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    USE_THEN "sk" (MP_TAC o SPEC `X1:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "sk" (MP_TAC o SPEC `X2:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `DISJOINT (X1:A->bool) X2` MP_TAC THENL
     [MP_TAC(ISPECL [`subtopology top {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`;
                     `X1:A->bool`; `X2:A->bool`] CONNECTED_COMPONENTS_OF_DISJOINT) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE ((ef:(A->bool)->real^3->A) X1) (rfs_neck_dom eps) SUBSET X1`;
        `IMAGE ((ef:(A->bool)->real^3->A) X2) (rfs_neck_dom eps) SUBSET X2`] THEN
      SET_TAC[]];
    X_GEN_TAC `Xb:A->bool` THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    USE_THEN "sk" (MP_TAC o SPEC `Xb:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(zf:(A->bool)->A) Xb IN IMAGE ((ef:(A->bool)->real^3->A) Xb) (rfs_neck_dom eps)`
    MP_TAC THENL
     [SUBGOAL_THEN `(zf:(A->bool)->A) Xb IN IMAGE ((ef:(A->bool)->real^3->A) Xb) (sphere(vec 0,&1))`
      MP_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((zf:(A->bool)->A) Xb)
                              ((ef:(A->bool)->real^3->A) Xb)` THEN SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`;
                   `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                    APXN_COMPONENT_FACTS) THEN
      ASM_SIMP_TAC[];
      STRIP_TAC] THEN
    UNDISCH_TAC `IMAGE ((ef:(A->bool)->real^3->A) Xb) (rfs_neck_dom eps) SUBSET Xb` THEN
    UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly.  Noncompact components of R >= (5/4) C L are                  *)
(* horns (claim C), finitely many; R is bounded off the horns; the end    *)
(* structure of W indexed by the noncompact components.                  *)
(* ------------------------------------------------------------------------- *)

(* Noncompact components of R >= (5/4) C L consist of NK-centres (claim C), *)
(* reach every level of R, and R is bounded off the horns of a family that  *)
(* covers them.                                                              *)

let APXN_NC_ALL_NK = prove
 (`!top atlas (g:A->real^3^3) C eps NK W L Xb.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_n4r top atlas g eps /\ apx21_ext top atlas g eps /\
     apx21_tubes top atlas g eps /\
     (!x1 e2 U1 Y1. rfs_neck (top,atlas) g eps x1 e2 /\ rfs_cap (top,atlas) g C eps U1 Y1
          ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     &1 <= C /\ &0 < L /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?q. q IN W /\ mfd_scalar atlas g q <= L) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN W /\ L < mfd_scalar atlas g x
          ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)) /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas g x}) /\
     ~compact_in top Xb
     ==> !x. x IN Xb ==> ?e. NK x e`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_ch_ctx] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_ctx")) (concl th))) THEN
  SUBGOAL_THEN `&0 < C * L /\ L <= C * L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}`;
                 `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN Xb ==> x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\
                                  &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Xb:A->bool) SUBSET W` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN Xb ==> &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN Xb
                ==> (?e. (NK:A->(real^3->A)->bool) x e) \/
                    (?U Y. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\ x IN Y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th) &&
      can (find_term (fun t -> t = `W:A->bool`)) (concl th))) THEN
    SUBGOAL_THEN `(x:A) IN W /\ &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < C * L`; `L <= C * L`;
      `&5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `NK:A->(real^3->A)->bool`; `Xb:A->bool`; `W:A->bool`;
                 `L:real`] APXN_NO_CAP_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN Xb`) o check (fun th ->
    is_forall (concl th) && is_disj(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
  STRIP_TAC THENL
   [EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `U:A->bool`; `Y:A->bool`] o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th) &&
      can (find_term (fun t -> t = `Xb:A->bool`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "NK")) (concl th)))) THEN
    ASM_REWRITE_TAC[]]);;

let APXN_NC_HIGH = prove
 (`!top atlas (g:A->real^3^3) W Lam Xb lev.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     Xb IN connected_components_of
             (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
     ~compact_in top Xb
     ==> ?w. w IN Xb /\ lev <= mfd_scalar atlas g w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `{x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`;
                 `Xb:A->bool`] APXN_SUBCOMP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APXN_LEVEL_CLOSED THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE]) THEN
  UNDISCH_TAC `~compact_in top (Xb:A->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= lev}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `Xb SUBSET {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}` THEN
    UNDISCH_TAC `(x:A) IN Xb` THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* R is bounded on W off the horns of a family N covering the noncompact   *)
(* components of R >= Lam: finitely many components reach R >= lev; on the *)
(* compact ones R is bounded, on the noncompact ones off their horn.        *)

let APXN_REST_BOUND = prove
 (`!top atlas (g:A->real^3^3) W Lam lev (N:(A->bool)->bool) (HH:(A->bool)->real^3->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ W SUBSET topspace top /\
     FINITE {Xb | Xb IN connected_components_of
                          (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
                  ?w. w IN Xb /\ lev <= mfd_scalar atlas g w} /\
     (!Xb. Xb IN connected_components_of
                   (subtopology top {x | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
           ~compact_in top Xb
           ==> Xb IN N) /\
     (!Xb. Xb IN N
           ==> ?c. !p. p IN Xb /\ ~(p IN IMAGE (HH Xb) {y:real^3 | &1 < norm y})
                       ==> mfd_scalar atlas g p <= c)
     ==> ?c. !p. p IN W /\ (!Xb. Xb IN N ==> ~(p IN IMAGE (HH Xb) {y:real^3 | &1 < norm y}))
                 ==> mfd_scalar atlas g p <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Hc = {Xb | Xb IN connected_components_of
                          (subtopology top {x:A | x IN W /\ Lam <= mfd_scalar atlas g x}) /\
                         ?w. w IN Xb /\ lev <= mfd_scalar atlas (g:A->real^3^3) w}` THEN
  SUBGOAL_THEN
   `!Xb. Xb IN Hc
         ==> ?c. !p. p IN Xb /\
                     (Xb IN N ==> ~(p IN IMAGE ((HH:(A->bool)->real^3->A) Xb)
                                                {y:real^3 | &1 < norm y}))
                     ==> mfd_scalar atlas (g:A->real^3^3) p <= c`
  MP_TAC THENL
   [X_GEN_TAC `Xb:A->bool` THEN EXPAND_TAC "Hc" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `compact_in top (Xb:A->bool)` THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `Xb:A->bool`] APXN_SCALAR_UPPER) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      SUBGOAL_THEN `(Xb:A->bool) IN N` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(Xb:A->bool) IN N`) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `HH:(A->bool)->real^3->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `BB:(A->bool)->real` (LABEL_TAC "bb")) THEN
  MP_TAC(ISPECL [`BB:(A->bool)->real`; `Hc:(A->bool)->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `max (max Lam lev) a` THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `mfd_scalar atlas (g:A->real^3^3) p < Lam` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?Xb. Xb IN connected_components_of
                        (subtopology top {x:A | x IN W /\
                                                Lam <= mfd_scalar atlas (g:A->real^3^3) x}) /\
                     (p:A) IN Xb` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `subtopology top {x:A | x IN W /\ Lam <= mfd_scalar atlas (g:A->real^3^3) x}`
                 UNIONS_CONNECTED_COMPONENTS_OF) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_UNIONS; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
    SUBGOAL_THEN `(p:A) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `Lam <= mfd_scalar atlas (g:A->real^3^3) p` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?w:A. w IN Xb /\ lev <= mfd_scalar atlas (g:A->real^3^3) w` THENL
   [SUBGOAL_THEN `(Xb:A->bool) IN Hc` ASSUME_TAC THENL
     [EXPAND_TAC "Hc" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!b. x <= b /\ b <= a ==> x <= max (max l v) a`) THEN
    EXISTS_TAC `(BB:(A->bool)->real) Xb` THEN CONJ_TAC THENL
     [USE_THEN "bb" (MP_TAC o C MATCH_MP (ASSUME `(Xb:A->bool) IN Hc`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE]) THEN
    DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The end structure of W indexed by the set N of noncompact components of  *)
(* R >= (5/4) C L: one horn per member, compact rest.                       *)

let APXN_ENDS_N = prove
 (`!top atlas (g:A->real^3^3) C eps NK L W.
     apx_ch_ctx top atlas g eps /\ apx_ch_pair top atlas g eps /\
     apx_ch_more top atlas g eps /\ apx_ch_n4r top atlas g eps /\
     apx21_ext top atlas g eps /\ apx21_tubes top atlas g eps /\ apx_sphere_sep top atlas /\
     (!x1 e2 U1 Y1. rfs_neck (top,atlas) g eps x1 e2 /\ rfs_cap (top,atlas) g C eps U1 Y1
          ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))) /\
     (!x (e:real^3->A) y. rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
          ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
              mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x) /\
     (!x (e:int->real^3->A). apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
        ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
                (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                apx_chain_union eps {i:int | &0 <= i} e /\
                (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                           IMAGE E (apx_slab (--inv eps) rho))) /\
     &1 <= C /\ &0 < L /\ W IN connected_components_of top /\
     (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
     (?x. x IN W /\ mfd_scalar atlas g x <= L) /\
     (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
     (!x. x IN W /\ L < mfd_scalar atlas g x
          ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
     ==> ?(N:(A->bool)->bool) (HH:(A->bool)->real^3->A) K.
          FINITE N /\ compact_in top K /\ K SUBSET W /\
          W = K UNION UNIONS {IMAGE (HH b) {y:real^3 | &1 <= norm y} | b IN N} /\
          (!b. b IN N
               ==> mfd_param top atlas {y | &1 / &2 < norm y} (HH b) /\
                   IMAGE (HH b) {y | &1 / &2 < norm y} SUBSET W /\
                   (!K'. compact_in top K' ==> bounded {y | &1 <= norm y /\ HH b y IN K'}) /\
                   (!y. &1 <= norm y
                        ==> C * L < mfd_scalar atlas g (HH b y) /\ ?e. NK (HH b y) e) /\
                   (!y. norm y = &1 ==> mfd_scalar atlas g (HH b y) <= &2 * C * L) /\
                   (?x e. NK x e /\
                          IMAGE e (sphere(vec 0,&1)) = IMAGE (HH b) (sphere(vec 0,&1)))) /\
          (!b b'. b IN N /\ b' IN N /\ ~(b = b')
                  ==> DISJOINT (IMAGE (HH b) {y | &1 <= norm y})
                               (IMAGE (HH b') {y | &1 <= norm y}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["ctx"; "pair"; "more"; "n4r"; "ext"; "tubes"; "sep"; "nocap"; "rat"; "chart"; "C1"; "L0";
     "WC"; "prop"; "low"; "nkn"; "canon"] (CONJUNCTS th))) THEN
  USE_THEN "ctx" (MP_TAC o REWRITE_RULE[apx_ch_ctx]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C * L /\ L <= C * L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 * L <= C * L ==> L <= C * L`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`]
                APXN_COMPONENT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &5 / &4 * C * L` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < C * L` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?q:A. q IN W /\ mfd_scalar atlas (g:A->real^3^3) q < &5 / &4 * C * L`
  ASSUME_TAC THENL
   [USE_THEN "low" (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `q:A` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < C * L`; `L <= C * L`;
                           `mfd_scalar atlas (g:A->real^3^3) q <= L`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN W /\ &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x
                ==> (?e. (NK:A->(real^3->A)->bool) x e) \/
                    (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN USE_THEN "canon" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < C * L`; `L <= C * L`;
                           `&5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `N = {Xb | Xb IN connected_components_of
                            (subtopology top {x:A | x IN W /\
                               &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}) /\
                        ~compact_in top Xb}` THEN
  (* a horn for each member of N *)
  SUBGOAL_THEN
   `!Xb. Xb IN N
         ==> ?H:real^3->A.
               mfd_param top atlas {y | &1 / &2 < norm y} H /\
               IMAGE H {y | &1 / &2 < norm y} SUBSET W /\
               (!K'. compact_in top K' ==> bounded {y | &1 <= norm y /\ H y IN K'}) /\
               (!y. &1 <= norm y
                    ==> C * L < mfd_scalar atlas (g:A->real^3^3) (H y) /\
                        (?e. (NK:A->(real^3->A)->bool) (H y) e) /\ H y IN Xb) /\
               (!y. norm y = &1 ==> mfd_scalar atlas g (H y) <= &2 * C * L) /\
               (?x e. NK x e /\ IMAGE e (sphere(vec 0,&1)) = IMAGE H (sphere(vec 0,&1))) /\
               (?c. !p. p IN Xb /\ ~(p IN IMAGE H {y | &1 < norm y})
                        ==> mfd_scalar atlas g p <= c) /\
               (?x e. rfs_neck (top,atlas) g eps x e /\ IMAGE e (rfs_neck_dom eps) SUBSET Xb /\
                      mfd_scalar atlas g x <= &2 * C * L)`
  MP_TAC THENL
   [X_GEN_TAC `Xb:A->bool` THEN EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `!x:A. x IN Xb ==> ?e. (NK:A->(real^3->A)->bool) x e` ASSUME_TAC THENL
     [MATCH_MP_TAC APXN_NC_ALL_NK THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `C:real`; `eps:real`; `W:A->bool`; `L:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC APXN_HORN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `HH:(A->bool)->real^3->A` (LABEL_TAC "hh")) THEN
  (* only finitely many components reach R >= 2 C Lam, and N is among them *)
  SUBGOAL_THEN
   `FINITE {Xb | Xb IN connected_components_of
                        (subtopology top {x:A | x IN W /\
                           &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}) /\
                 ?w. w IN Xb /\ &2 * C * (&5 / &4 * C * L) <= mfd_scalar atlas g w}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APXN_HIGH_COMPS_FINITE THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `NK:A->(real^3->A)->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (N:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{Xb | Xb IN connected_components_of
                        (subtopology top {x:A | x IN W /\
                           &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}) /\
                 ?w. w IN Xb /\ &2 * C * (&5 / &4 * C * L) <= mfd_scalar atlas g w}` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `Xb:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APXN_NC_HIGH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`; `&5 / &4 * C * L`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* R is bounded on W off the horns *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `&5 / &4 * C * L`; `&2 * C * (&5 / &4 * C * L)`;
                 `N:(A->bool)->bool`; `HH:(A->bool)->real^3->A`] APXN_REST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      X_GEN_TAC `Xb:A->bool` THEN DISCH_TAC THEN
      USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(Xb:A->bool) IN N`)) THEN SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `c:real`)] THEN
  (* the open horn parts are open *)
  SUBGOAL_THEN `!b. b IN N ==> open_in top (IMAGE ((HH:(A->bool)->real^3->A) b)
                                                  {y:real^3 | &1 < norm y})` ASSUME_TAC THENL
   [X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `{y:real^3 | &1 / &2 < norm y}`] THEN
    REWRITE_TAC[APXN_OPEN_OUTER; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(b:A->bool) IN N`)) THEN SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b. b IN N ==> IMAGE ((HH:(A->bool)->real^3->A) b) {y:real^3 | &1 <= norm y}
                               SUBSET W` ASSUME_TAC THENL
   [X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((HH:(A->bool)->real^3->A) b) {y:real^3 | &1 / &2 < norm y}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(b:A->bool) IN N`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N:(A->bool)->bool`; `HH:(A->bool)->real^3->A`;
    `W DIFF UNIONS {IMAGE ((HH:(A->bool)->real^3->A) b) {y:real^3 | &1 < norm y} | b IN N}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the rest is compact *)
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `{x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= c}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; UNIONS_GSPEC; NOT_EXISTS_THM] THEN
      X_GEN_TAC `p:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b:A->bool`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[]];
    (* the rest lies in W *)
    SET_TAC[];
    (* W is the rest and the horns *)
    MATCH_MP_TAC(SET_RULE `(U:A->bool) SUBSET U' /\ U' SUBSET W ==> W = (W DIFF U) UNION U'`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `b:A->bool` STRIP_ASSUME_TAC) THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:A) IN IMAGE ((HH:(A->bool)->real^3->A) b) {y:real^3 | &1 < norm y}` THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[]];
    (* the clauses of each horn *)
    X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN
    USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(b:A->bool) IN N`)) THEN SIMP_TAC[];
    (* the horns are disjoint *)
    MAP_EVERY X_GEN_TAC [`b:A->bool`; `b':A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (b:A->bool) b'` MP_TAC THENL
     [MP_TAC(ISPECL [`subtopology top {x:A | x IN W /\
                        &5 / &4 * C * L <= mfd_scalar atlas (g:A->real^3^3) x}`;
                     `b:A->bool`; `b':A->bool`] CONNECTED_COMPONENTS_OF_DISJOINT) THEN
      MAP_EVERY UNDISCH_TAC [`(b:A->bool) IN N`; `(b':A->bool) IN N`] THEN
      EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(b:A->bool) IN N`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    USE_THEN "hh" (MP_TAC o C MATCH_MP (ASSUME `(b':A->bool) IN N`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Reindexing by numbers and the headline                                   *)
(* |- !u. APX_A25_NC_ENDS_STATEMENT u.                                      *)
(* ------------------------------------------------------------------------- *)

(* Reindexing a finite family of disjoint horns by numbers. *)

let APXN_REINDEX = prove
 (`!(P:(real^3->A)->bool) (N:(A->bool)->bool) (HH:(A->bool)->real^3->A) (s:real^3->bool).
     FINITE N /\ (!b. b IN N ==> P (HH b)) /\
     (!b b'. b IN N /\ b' IN N /\ ~(b = b')
             ==> DISJOINT (IMAGE (HH b) s) (IMAGE (HH b') s))
     ==> ?(J:num->bool) (H:num->real^3->A).
           FINITE J /\ UNIONS {IMAGE (H j) s | j IN J} = UNIONS {IMAGE (HH b) s | b IN N} /\
           (!j. j IN J ==> P (H j)) /\
           (!i j. i IN J /\ j IN J /\ ~(i = j)
                  ==> DISJOINT (IMAGE (H i) s) (IMAGE (H j) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(N:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`1..n`; `\j. (HH:(A->bool)->real^3->A) ((f:num->A->bool) j)`] THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `p:A` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The headline: |- !u. APX_A25_NC_ENDS_STATEMENT u. *)

let APXN_A25_NC_ENDS = prove
 (`!u:A->bool. APX_A25_NC_ENDS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A25_NC_ENDS_STATEMENT] THEN
  X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX_CH_MORE_HOLDS) THEN
  X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  X_CHOOSE_THEN `e4:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX21_EXT_HOLDS) THEN
  X_CHOOSE_THEN `e5:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX21_TUBES_HOLDS) THEN
  X_CHOOSE_THEN `e6:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APXN_NECK_RATIO) THEN
  MP_TAC(REWRITE_RULE[APX_NO_CAP_IN_NECK_STATEMENT]
           (ISPEC `u:A->bool` APX_NO_CAP_IN_NECK_UNCOND)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e7:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP (ISPEC `u:A->bool` APXC_CHART_CORE) (ISPEC `u:A->bool` SMT_PRODUCT2)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e8:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 (min e2 (min e3 (min e4 (min e5 (min e6 (min e7 e8))))))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `NK:A->(real^3->A)->bool`;
    `L:real`; `W:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_CASES_TAC `?x:A. x IN W /\ L < mfd_scalar atlas (g:A->real^3^3) x` THENL
   [ALL_TAC;
    (* no point above L: W is compact and there are no horns *)
    MAP_EVERY EXISTS_TAC [`{}:num->bool`; `\j:num y:real^3. (@x:A. T)`; `W:A->bool`] THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; SUBSET_REFL; SIMPLE_IMAGE; IMAGE_CLAUSES;
                UNIONS_0; UNION_EMPTY] THEN
    SUBGOAL_THEN `W = {x:A | x IN W /\ mfd_scalar atlas (g:A->real^3^3) x <= L}`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV) [th]) THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_REWRITE_TAC[]]] THEN
  (* smoothness, from a neck or a cap at a point above L *)
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0:A` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th) &&
      can (find_term (fun t -> t = `W:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps x0 (e:real^3->A)` MP_TAC THENL
       [ASM_SIMP_TAC[]; SIMP_TAC[rfs_neck]];
      MATCH_MP_TAC APX22_CAP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`;
                            `Y:A->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the contexts at this eps *)
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) eps /\ apx_ch_pair top atlas g eps`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_pair")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_ch_more top atlas (g:A->real^3^3) eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_more")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_ch_n4r top atlas (g:A->real^3^3) eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ch_n4r")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx21_ext top atlas (g:A->real^3^3) eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx21_ext")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx21_tubes top atlas (g:A->real^3^3) eps` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx21_tubes")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x (e:real^3->A) y. rfs_neck (top,atlas) (g:A->real^3^3) eps x e /\ y IN rfs_neck_dom eps
        ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `e6:real`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x1 (e2:real^3->A) U1 Y1. rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e2 /\
                              rfs_cap (top,atlas) g C eps U1 Y1
        ==> ~(top closure_of Y1 SUBSET IMAGE e2 (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `e7:real`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x1:A`; `U1:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x (e:int->real^3->A). apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e
        ==> ?E. mfd_param top atlas {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} E /\
                (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                IMAGE E {y:real^3 | exp(--inv eps / sqrt(&2)) < norm y} =
                apx_chain_union eps {i:int | &0 <= i} e /\
                (!n. ?rho. apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e SUBSET
                           IMAGE E (apx_slab (--inv eps) rho))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`xc:int->A`; `ec:int->real^3->A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `e8:real`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `xc:int->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the end structure indexed by the noncompact components *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `NK:A->(real^3->A)->bool`; `L:real`; `W:A->bool`]
                APXN_ENDS_N) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:(A->bool)->bool` (X_CHOOSE_THEN `HH:(A->bool)->real^3->A`
    (X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs(concl th) = `W:A->bool`)) THEN
  (* reindex the horns by numbers *)
  MP_TAC(ISPECL
   [`\h:real^3->A.
       mfd_param top atlas {y:real^3 | &1 / &2 < norm y} h /\
       IMAGE h {y:real^3 | &1 / &2 < norm y} SUBSET W /\
       (!K'. compact_in top K' ==> bounded {y:real^3 | &1 <= norm y /\ h y IN K'}) /\
       (!y:real^3. &1 <= norm y
                   ==> C * L < mfd_scalar atlas (g:A->real^3^3) (h y) /\
                       ?e. (NK:A->(real^3->A)->bool) (h y) e) /\
       (!y:real^3. norm y = &1 ==> mfd_scalar atlas g (h y) <= &2 * C * L) /\
       (?x e. NK x e /\ IMAGE e (sphere(vec 0,&1)) = IMAGE h (sphere(vec 0,&1)))`;
    `N:(A->bool)->bool`; `HH:(A->bool)->real^3->A`; `{y:real^3 | &1 <= norm y}`]
   APXN_REINDEX) THEN
  ANTS_TAC THENL [BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:num->bool` (X_CHOOSE_THEN `H:num->real^3->A`
    (STRIP_ASSUME_TAC o BETA_RULE))) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`J:num->bool`; `H:num->real^3->A`; `K:A->bool`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs(concl th) = `W:A->bool`)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

