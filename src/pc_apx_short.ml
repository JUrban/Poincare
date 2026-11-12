(* ========================================================================= *)
(* pc_apx_short: MT Appendix A, Sec. 1-2, the shortest-curve lemmas: Lemma  *)
(* A.1 (APX_A1), the constant-speed forms of Lemma A.4, Cor A.6 and Lemma   *)
(* A.7 of pc_p2b_defs (P2B_APX_A4_CS, P2B_APX_A6_CS, P2B_APX_A7_CS), and Cor *)
(* A.8 for constant-speed minimizers (APX_A8_CS of pc_apx_csreq).           *)
(* ========================================================================= *)

needs "src/pc_apx_a21.ml";;
needs "src/pc_smt_leafsep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MT Lemma A.1 (shortening across a separating neck).                      *)
(* ------------------------------------------------------------------------- *)

(* A great-circle path on the unit sphere (apx_mpath with l0 = dl = 0):     *)
(* cylinder length at most sqrt(2) pi, staying on the sphere.               *)

let APXS_SPHERE_PATH = prove
 (`!s y z:real^3.
     open s /\ (!v. norm v = &1 ==> v IN s) /\ norm y = &1 /\ norm z = &1
     ==> ?c. mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c (&0) (&1) /\
             c(&0) = y /\ c(&1) = z /\ (!t. norm(c t) = &1) /\
             mfd_length (open_set_atlas s) (cylinder_flow (&0)) c (&0) (&1)
             <= sqrt(&2) * pi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^3`; `z:real^3`] APX_GREAT_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^3) dot y = &1 /\ (q:real^3) dot q = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_1] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `P = apx_mpath (&0) (&0) th (y:real^3) q` THEN
  ABBREV_TAC `V = \t. (&0) % apx_mpath (&0) (&0) th (y:real^3) q t +
                      th % apx_mpath (&0) (&0) th q (--y) t` THEN
  SUBGOAL_THEN `!t. ((\r. (P:real->real^3)(drop r)) has_vector_derivative V t) (at (lift t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "V"] THEN BETA_TAC THEN
    REWRITE_TAC[APX_MPATH_VD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. norm((P:real->real^3) t) = &1` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "P" THEN
    MP_TAC(ISPECL [`&0`; `&0`; `th:real`; `y:real^3`; `q:real^3`; `t:real`]
                  APX_MPATH_NORM) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_EXP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (P:real->real^3) t IN s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `s:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\r. (V:real->real^3)(drop r)) continuous_on (:real^1) /\
                (\r. (P:real->real^3)(drop r)) continuous_on (:real^1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THENL
     [EXPAND_TAC "V" THEN BETA_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[APX_MPATH_CONT];
      EXPAND_TAC "P" THEN REWRITE_TAC[APX_MPATH_CONT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (P:real->real^3)
                             (&0) (&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_c1_curve; REAL_POS] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `ch:(real^3->bool)#(real^3->real^3)` THEN
      REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
      MATCH_MP_TAC APX_C1_FROM_VD THEN EXISTS_TAC `\r. (V:real->real^3)(drop r)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `drop x` o check (is_forall o concl) o
          check (fun th -> can (find_term (fun t -> t = `V:real->real^3`)) (concl th) &&
                           can (find_term is_abs) (concl th))) THEN
        REWRITE_TAC[LIFT_DROP];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]]];
    ALL_TAC] THEN
  EXISTS_TAC `P:real->real^3` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[apx_mpath; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; COS_0; SIN_0;
                REAL_EXP_0; REAL_MUL_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID];
    EXPAND_TAC "P" THEN
    REWRITE_TAC[apx_mpath; REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_LID;
                REAL_EXP_0; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MFD_LENGTH_OPEN_SET_ATLAS] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,&1])
      (\t. sqrt(vector_derivative (\r. (P:real->real^3)(drop r))
                  (at (lift t) within interval[lift(&0),lift(&1)]) dot
                (cylinder_flow (&0) (P t) **
                 vector_derivative (\r. P(drop r))
                  (at (lift t) within interval[lift(&0),lift(&1)])))) =
    real_integral (real_interval[&0,&1]) (\t. sqrt(&2 * (&0 pow 2 + th pow 2)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN
     `vector_derivative (\r. (P:real->real^3)(drop r))
        (at (lift t) within interval[lift(&0),lift(&1)]) = V t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_LT_01; GRGD_IN_INTERVAL_LIFT;
                   HAS_VECTOR_DERIVATIVE_AT_WITHIN];
      ALL_TAC] THEN
    AP_TERM_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "V"] THEN BETA_TAC THEN
    MATCH_MP_TAC APX_MPATH_SPEED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`&0`; `th:real`] APX_SQRT_PATH_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_RZERO; REAL_ADD_LID]);;

(* The great-circle path in the central sphere of a neck: a curve in M     *)
(* inside e(sphere 1) of length at most sqrt(1 + eps) R(x)^(-1/2) sqrt2 pi. *)

let APXS_NECK_SPHERE_PATH = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) w0 w1.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
     norm w0 = &1 /\ norm w1 = &1
     ==> ?mu. mfd_c1_curve (top,atlas) mu (&0) (&1) /\
              mu(&0) = e w0 /\ mu(&1) = e w1 /\
              (!t. mu t IN IMAGE e (sphere(vec 0,&1))) /\
              mfd_length atlas g mu (&0) (&1) <=
              sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) * sqrt(&2) * pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `w0:real^3`; `w1:real^3`] APXS_SPHERE_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS] THEN REWRITE_TAC[GSYM rfs_neck_dom] THEN
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `c:real->real^3`; `&0`; `&1`]
                APX_NECK_CURVE_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `(e:real^3->A) o (c:real->real^3)` THEN ASM_REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0)) c (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC);;

(* The neck domain contains the closed shell 1/4 <= |y| <= 4. *)

let APXS_DOM_BOUNDS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024
         ==> exp(--inv eps / sqrt(&2)) < &1 / &4 /\ &4 < exp(inv eps / sqrt(&2))`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN SIMP_TAC[]);;

(* The positive side of a neck (apx_pos_side = lsp_side of the neck chart): *)
(* it misses the central sphere and the lower half, and contains every     *)
(* connected set missing the sphere that meets it.                         *)

let APXS_POS_SIDE_FACTS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
     hausdorff_space top /\ apx_sphere_sep top atlas /\ rfs_neck (top,atlas) g eps x e /\
     eps <= &1 / &1024
     ==> closed_in top (IMAGE e (sphere(vec 0,&1))) /\
         apx_pos_side top e SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
         DISJOINT (IMAGE e (apx_slab (--inv eps) (&0))) (apx_pos_side top e) /\
         (!K. connected_in top K /\ K SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
              ~(K INTER apx_pos_side top e = {})
              ==> K SUBSET apx_pos_side top e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (e:real^3->A)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> b SUBSET c ==> a SUBSET c`) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
                LSP_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`]
                LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(SPEC `&3 / &4` th) THEN MP_TAC(SPEC `&4 / &3` th))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_pos_side top (e:real^3->A) = lsp_side top e (&4 / &3)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; apx_pos_side; lsp_side]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the lower half lies in the other side *)
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)) SUBSET lsp_side top e (&3 / &4)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `lsp_side top (e:real^3->A) (&3 / &4)`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3] THEN REWRITE_TAC[GSYM apx_slab] THEN
      MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab (--inv eps) (&0)`]
                      MFD_PARAM_IMAGE_SUBSET) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
          SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
          UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))` THEN
          SET_TAC[]];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab (--inv eps) (&0)`;
                       `sphere(vec 0:real^3,&1)`] APX21_PARAM_IMAGE_DISJOINT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
            SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
             [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
            MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[];
            REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; apx_slab; annulus;
                        IN_ELIM_THM; IN_SPHERE_0] THEN
            REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REAL_ARITH_TAC];
          UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0))` THEN
          SET_TAC[]]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A)(&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(SPEC `eps:real` APXS_DOM_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[apx_slab; annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (lsp_side top (e:real^3->A) (&3 / &4)) (lsp_side top e (&4 / &3))` THEN
  SET_TAC[]);;

(* The last time a curve lies in a closed set (GRGD_FIRST_TIME for the      *)
(* reversed curve).                                                          *)

let APXS_LAST_IN_CLOSED = prove
 (`!top atlas (gamma:real->A) a b S.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma a b /\ a < b /\
     closed_in top S /\ gamma a IN S /\ ~(gamma b IN S)
     ==> ?c. a <= c /\ c < b /\ gamma c IN S /\
             !t. c < t /\ t <= b ==> ~(gamma t IN S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) gamma a b` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  ABBREV_TAC `h = \s:real. b + (a - b) * s` THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool)
                             ((gamma:real->A) o (h:real->real)) (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `\s:real. a - b`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_CONTINUOUS_ON_CONST] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
        `(b - a) * s <= (b - a) * &1 /\ &0 <= (b - a) * s
         ==> a <= b + (a - b) * s /\ b + (a - b) * s <= b`) THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REAL_DIFF_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `(gamma:real->A) o (h:real->real)`; `topspace top DIFF (S:A->bool)`]
                GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool)
                                ((gamma:real->A) o (h:real->real)) (&0) (&1)` THEN
      SIMP_TAC[mfd_c1_curve];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      EXPAND_TAC "h" THEN REWRITE_TAC[o_THM; REAL_MUL_RZERO; REAL_ADD_RID; IN_DIFF] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&1` THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[IN_REAL_INTERVAL; o_THM; IN_DIFF; REAL_MUL_RID;
                  REAL_ARITH `b + (a - b) = a:real`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b + (a - b) * t1` THEN
  SUBGOAL_THEN `a <= b + (a - b) * t1 /\ b + (a - b) * t1 < b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `(b - a) * t1 <= (b - a) * &1 ==> a <= b + (a - b) * t1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < (b - a) * t1 ==> b + (a - b) * t1 < b`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `~(((gamma:real->A) o (h:real->real)) (t1:real) IN topspace top DIFF S)` THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[o_THM; IN_DIFF] THEN
    SUBGOAL_THEN `(gamma:real->A)(b + (a - b) * t1) IN topspace top` ASSUME_TAC
    THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(b - t) / (b - a)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `t1:real`)) (concl th))) THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_SUB_LE; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[o_THM; IN_DIFF] THEN
  SUBGOAL_THEN `b + (a - b) * (b - t) / (b - a) = t` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < b - a` THEN CONV_TAC REAL_FIELD;
    SIMP_TAC[]]);;

(* MT Lemma A.1: shortening across a separating neck.  The last time c the  *)
(* curve is on the central sphere S (APXS_LAST_IN_CLOSED); after c the      *)
(* curve stays on the positive side (it is connected and misses S), so the *)
(* dip into the negative quarter comes before c and gamma[a,c] is at least  *)
(* (9/10) R(x)^(-1/2) / eps long (APX_NECK_DIST); a great-circle path on S  *)
(* from x to gamma c (length <= 2 sqrt(2) pi R(x)^(-1/2)) followed by       *)
(* gamma[c,b] is the shorter curve.                                         *)

let APX_A1 = prove
 (`!u:A->bool. APX_A1_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A1_STATEMENT] THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &10`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  EXISTS_TAC `min e2 (&1 / &1024)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:A`;
                       `gamma:real->A`; `a:real`; `b:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  (* basic facts *)
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                x IN IMAGE e (sphere(vec 0,&1)) /\ &0 < mfd_scalar atlas (g:A->real^3^3) x`
  STRIP_ASSUME_TAC THENL
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
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] APXS_POS_SIDE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "side")))) THEN
  (* the dip point is off S and off the positive side *)
  SUBGOAL_THEN `?v0. v0 IN apx_slab (--inv eps) (--inv(&2 * eps)) /\
                     (gamma:real->A) t0 = e v0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) t0 IN IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET apx_slab (--inv eps) (&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUBSET THEN REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) t0 IN S) /\ ~(apx_pos_side top (e:real^3->A) (gamma t0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `apx_slab (--inv eps) (&0)`;
                     `sphere(vec 0:real^3,&1)`] APX21_PARAM_IMAGE_DISJOINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
          SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; apx_slab; annulus;
                      IN_ELIM_THM; IN_SPHERE_0] THEN
          REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!f:real^3->A s t S v. v IN s /\ s SUBSET t ==>
                     DISJOINT (IMAGE f t) S ==> ~(f v IN S)`) THEN
      EXISTS_TAC `apx_slab (--inv eps) (--inv(&2 * eps))` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (apx_slab (--inv eps) (&0)))
                            (apx_pos_side top e)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!f:real^3->A s t P v. v IN s /\ s SUBSET t ==>
                     DISJOINT (IMAGE f t) P ==> ~(P (f v))`) THEN
      EXISTS_TAC `apx_slab (--inv eps) (--inv(&2 * eps))` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a < b and the points of gamma lie in M *)
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(a = b) ==> a < b`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b` THEN SIMP_TAC[mfd_c1_curve];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((gamma:real->A) t0 IN S)` THEN
    SUBGOAL_THEN `t0 = a:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) a b` THEN SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  (* the last time c on S; afterwards gamma is on the positive side *)
  SUBGOAL_THEN `?c. a <= c /\ c <= b /\ (gamma:real->A) c IN S /\
                    (!t. c < t /\ t <= b ==> apx_pos_side top (e:real^3->A) (gamma t))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(y:A) IN S` THENL
     [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `apx_pos_side top (e:real^3->A) y` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN S \/ apx_pos_side top (e:real^3->A) y` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                   `a:real`; `b:real`; `S:A->bool`] APXS_LAST_IN_CLOSED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (gamma:real->A) (real_interval[t,b]) SUBSET apx_pos_side top e`
    MP_TAC THENL
     [USE_THEN "side" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
        EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
        ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `topspace (top:A topology)`)) (concl th))) THEN
          ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `c:real`)) (concl th))) THEN
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
        EXISTS_TAC `y:A` THEN CONJ_TAC THENL
         [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[]]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[IN] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the dip comes before c *)
  SUBGOAL_THEN `t0 < c:real` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `t0 = c:real` THENL
     [MAP_EVERY UNDISCH_TAC [`(gamma:real->A) c IN S`; `~((gamma:real->A) t0 IN S)`;
                             `t0 = c:real`] THEN
      MESON_TAC[];
      UNDISCH_TAC `~apx_pos_side top (e:real^3->A) ((gamma:real->A) t0)` THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_pos_side")) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the points on S and the two distance bounds (N2) *)
  SUBGOAL_THEN `?w0 w1. norm w0 = &1 /\ norm w1 = &1 /\ x = (e:real^3->A) w0 /\
                        (gamma:real->A) c = e w1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN S` THEN UNDISCH_TAC `(gamma:real->A) c IN S` THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &2 * inv(&2 * eps) = inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET rfs_neck_dom eps /\
                sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w0:real^3) IN rfs_neck_dom eps /\ (w1:real^3) IN rfs_neck_dom eps /\
                (v0:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`norm(w0:real^3) = &1`; `norm(w1:real^3) = &1`;
      `(v0:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))`;
      `apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET rfs_neck_dom eps`;
      `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps`] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(w0:real^3) = &0 /\ apx_sval(w1:real^3) = &0 /\
                --inv eps < apx_sval(v0:real^3) /\ apx_sval v0 < --inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_UNIT] THEN
    UNDISCH_TAC `(v0:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` THEN
    SIMP_TAC[APX_SLAB_SVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &10 * h * inv(&2 * eps) <=
                mfd_dist (top,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x
                         ((gamma:real->A) t0) /\
                &9 / &10 * h * inv(&2 * eps) <= mfd_dist (top,atlas) g (gamma t0) (gamma c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "n2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `v0:real^3`]);
      USE_THEN "n2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `v0:real^3`; `w1:real^3`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= d ==> a <= d`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  (* the length of gamma splits at t0 and c *)
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) t0 c /\
                mfd_c1_curve (top,atlas) gamma c b /\
                mfd_length atlas (g:A->real^3^3) gamma a b =
                mfd_length atlas g gamma a t0 + mfd_length atlas g gamma t0 c +
                mfd_length atlas g gamma c b /\
                mfd_dist (top,atlas) g x (gamma t0) <= mfd_length atlas g gamma a t0 /\
                mfd_dist (top,atlas) g (gamma t0) (gamma c) <= mfd_length atlas g gamma t0 c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `a:real`; `t0:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `t0:real`; `c:real`; `b:real`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `a:real`; `t0:real`] MFD_DIST_LE_LENGTH) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `t0:real`; `c:real`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the sphere path mu from x to gamma c *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `w0:real^3`; `w1:real^3`]
                APXS_NECK_SPHERE_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real->A` (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
    `IMAGE (e:real^3->A) (sphere(vec 0,&1)) = S`; ASSUME
    `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) = h`])) THEN
  (* gamma after c, reparametrized to [0,1] *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `c:real`; `b:real`; `\s:real. c + (b - c) * s`;
                 `\s:real. b - c`; `&0`; `&1`] MFD_LENGTH_REPARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS; REAL_CONTINUOUS_ON_CONST] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC;
      MP_TAC(SPECL [`c:real`; `b:real`] GRGD_AFFINE_FACTS) THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  ABBREV_TAC `dl = (gamma:real->A) o (\s. c + (b - c) * s)` THEN
  SUBGOAL_THEN `(dl:real->A)(&0) = (gamma:real->A) c /\ dl(&1) = y /\
                !t. &0 <= t /\ t <= &1 ==> dl t IN S \/ apx_pos_side top (e:real^3->A) (dl t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
                REAL_ARITH `c + (b - c) = b:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `c + (b - c) * t = c:real` THENL
     [DISJ1_TAC THEN UNDISCH_TAC `c + (b - c) * t = c:real` THEN
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISJ2_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `c:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_pos_side")) (concl th))) THEN
    SUBGOAL_THEN `&0 <= (b - c) * t /\ (b - c) * t <= (b - c) * &1` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(c + (b - c) * t = c:real)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the new curve *)
  EXISTS_TAC `grgd_concat (mu:real->A) (dl:real->A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `mu:real->A`;
                 `dl:real->A`] GRGD_CONCAT_C1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `mu:real->A`; `dl:real->A`] GRGD_CONCAT_LENGTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`mu:real->A`; `dl:real->A`; `S UNION apx_pos_side top (e:real^3->A)`]
                  GRGD_CONCAT_IN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[IN_UNION];
        REWRITE_TAC[IN_UNION] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `dl:real->A`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN]];
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC(TAUT `(q ==> r) ==> (p ==> q) ==> (p ==> r)`) THEN
      REWRITE_TAC[IN_UNION] THEN REWRITE_TAC[IN]];
    ALL_TAC] THEN
  (* the length *)
  SUBGOAL_THEN `sqrt(&1 + eps) * h * sqrt(&2) * pi <= &10 * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 + eps) <= &2 /\ &0 <= sqrt(&2) * pi /\ sqrt(&2) * pi <= &24 / &5`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC PI_POS THEN
        SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN REAL_ARITH_TAC;
        REWRITE_TAC[APX_SQRT2_PI]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * h * &24 / &5` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `&0 < eps ==> &0 <= &1 + eps`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&512 * h <= h * inv(&2 * eps)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

