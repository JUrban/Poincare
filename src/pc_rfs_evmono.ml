(* ========================================================================= *)
(* Unit pc_rfs_evmono: an evolving or strong eps-neck is an eps'-neck for    *)
(* every eps' >= eps, given the metric and the parametrization at the times  *)
(* of its window (in a regular view these come from P2B9_REGULAR_NECK_SLICE).*)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_smt_glue.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Monotonicity in eps of evolving and strong necks.                         *)
(* ------------------------------------------------------------------------- *)

let RFS_EVOLVING_NECK_EPS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps eps' x t len (e:real^3->A).
     rfs_evolving_neck V eps x t len e /\ eps <= eps' /\
     (!s. --len < s /\ s <= &0
          ==> riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t x))
                                (rfs_vmetric V (t + s / rfs_vscalar V t x)) /\
              mfd_param (rfs_vtop V (t + s / rfs_vscalar V t x))
                        (rfs_vatlas V (t + s / rfs_vscalar V t x)) (rfs_neck_dom eps) e)
     ==> rfs_evolving_neck V eps' x t len e`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `eps':real`; `x:A`; `t:real`;
                       `len:real`; `e:real^3->A`] THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  ABBREV_TAC `R = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                             ((G:real->A->real^3^3) t) x` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "cl"))))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl"))) THEN
  SUBGOAL_THEN
   `&0 < eps /\ &0 < R /\
    smooth_manifold_atlas ((TM:real->A topology) t)
                          ((AT:real->((A->bool)#(A->real^3))->bool) t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                   ((G:real->A->real^3^3) t) eps x (e:real^3->A)` THEN
    ASM_REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                  ((G:real->A->real^3^3) t)` ASSUME_TAC THENL
   [USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps' SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* persistence of the smaller image *)
    REWRITE_TAC[rfs_persists] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "per" (MP_TAC o SPEC `u:real` o REWRITE_RULE[rfs_persists]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`(AT:real->((A->bool)#(A->real^3))->bool) u`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]] THEN
    SUBGOAL_THEN `--len < (u - t) * R /\ (u - t) * R <= &0 /\ t + ((u - t) * R) / R = u`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `--len = --(len / R) * R` SUBST1_TAC THENL
         [MATCH_MP_TAC(REAL_FIELD `~(R = &0) ==> --len = --(len / R) * R`) THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `&0 <= (t - u) * R ==> (u - t) * R <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_FIELD `~(R = &0) ==> t + ((u - t) * R) / R = u`) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "sl" (MP_TAC o SPEC `(u - t) * R`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the closeness on the smaller domain with fewer derivatives *)
  USE_THEN "cl" MP_TAC THEN REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps'` THEN
    UNDISCH_TAC `rfs_neck_dom eps' SUBSET rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s)
               (\y. R %% rfs_pullback ((AT:real->((A->bool)#(A->real^3))->bool) (t + s / R))
                         (e:real^3->A) ((G:real->A->real^3^3) (t + s / R)) y) y` THEN
  CONJ_TAC THENL
   [ALL_TAC; USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
  USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `t - len / R < t + s / R /\ t + s / R <= t` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `--len / R < s / R /\ s / R <= &0 / R /\ --len / R = --(len / R) /\ &0 / R = &0
      ==> t - len / R < t + s / R /\ t + s / R <= t`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_DIV2_EQ] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_MUL_LZERO];
    ALL_TAC] THEN
  USE_THEN "per" (MP_TAC o SPEC `t + s / R` o REWRITE_RULE[rfs_persists]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[APX_NECK_DOM_NONZERO] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]];
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `(TM:real->A topology) (t + s / R)` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]]);;

let RFS_STRONG_NECK_EPS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps eps' x t (e:real^3->A).
     rfs_strong_neck V eps x t e /\ eps <= eps' /\
     (!s. --(&1) < s /\ s <= &0
          ==> riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t x))
                                (rfs_vmetric V (t + s / rfs_vscalar V t x)) /\
              mfd_param (rfs_vtop V (t + s / rfs_vscalar V t x))
                        (rfs_vatlas V (t + s / rfs_vscalar V t x)) (rfs_neck_dom eps) e)
     ==> rfs_strong_neck V eps' x t e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_strong_neck] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFS_EVOLVING_NECK_EPS_MONO THEN EXISTS_TAC `eps:real` THEN
  ASM_REWRITE_TAC[]);;

