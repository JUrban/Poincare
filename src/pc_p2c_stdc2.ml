(* ========================================================================= *)
(* Unit pc_p2c_stdc2 (Part 2C; MT Ch 12): MT Thm 12.29, Tm = 1               *)
(* for the maximal standard flow Gs.  If Tm < 1:                             *)
(*  (A) R, hence abs Rm <= R/2 (sec >= 0), is bounded on R^3 x [0,Tm):       *)
(*      far out at a time T0 close to Tm by the cylinder asymptotics         *)
(*      (STDS_ASYM_CLOSE with curvature stability), on [T0,Tm) far out by    *)
(*      Lemma 11.2 (LEMMA_11_2_DB with the derivative bounds of canonical    *)
(*      neighbourhoods, Thm 12.28 and CANON_DERIV), and on the compact rest  *)
(*      by MT's blow-up argument: a kappa-solution limit (Thm 11.8) has     *)
(*      asymptotic volume ratio 0 (AVR_ZERO_FIX), the volumes of rescaled    *)
(*      balls converge (LIM_VOL), Bishop-Gromov and Lemma 3.14 make the      *)
(*      volume of a fixed far-out open set small, against its lower bound.   *)
(*  (B) bounded curvature lets the restart of stdres (STDS_RESTART,         *)
(*      STDS_GLUE) extend Gs past Tm, against maximality.                    *)
(* Deviation from MT: the restart replaces MT's limit metric g(T) and Thm    *)
(* 3.29.                                                                     *)
(* ========================================================================= *)

needs "src/pc_p2c_stdc1.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_p2c_stdnc2.ml";;
needs "src/pc_p2b_rmhalf.ml";;
needs "src/pc_p2b_limbridge.ml";;
needs "src/pc_rf_mequiv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of the unit and the basic curvature facts of              *)
(* Gs: Riemannian slices, abs Rm <= R/2 and Ric >= 0 under sec >= 0.        *)
(* ------------------------------------------------------------------------- *)

let stds_tm_hyps = new_definition
 `stds_tm_hyps (d:real^4->bool) <=>
    stds_gs_hyps /\ PDE_CURVATURE_TIME_STATEMENT d (:3) /\
    P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_PROP_5_14_STATEMENT d (:real^3) /\
    APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\ P2C_STD_NONCOLL_STATEMENT /\
    P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3) /\
    P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
    P2B_AVR_ZERO_FIX_STATEMENT (:real^3) /\ P2C_REQ_BISHOP_GROMOV_STATEMENT (:real^3) /\
    P2_LEMMA_3_14_STATEMENT (:real^3) /\ P2C_LEMMA_11_2_DB_STATEMENT (:real^3) /\
    P2C_CANON_DERIV_STATEMENT (:real^3)`;;

(* With sec >= 0: abs Rm <= R/2, 0 <= Ric <= R g.                            *)

let STDS_GS_SEC_CONSEQ = prove
 (`!g0 A0 t x.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ &0 <= t /\ t < stds_tm g0 /\
     (!u v. ~collinear {vec 0,u,v}
            ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x u v)
     ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <=
         mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x / &2 /\
         &0 <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x /\
         !v. &0 <= mfd_ricci (open_set_atlas (:real^3)) (stds_gs g0 t) x v v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <=
                mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN
    EXISTS_TAC `euclidean:(real^3)topology` THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x
                                    (basis 1) (basis 2))` THEN
      REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; P3S_NONCOLL_BASIS];
      UNDISCH_TAC `mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <=
                   mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x / &2` THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `v:real^3` THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `stds_gs g0 t`; `x:real^3`; `&0`; `v:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_MUL_LZERO; REAL_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* A far-out bound for R on [0,T'], uniform in T' < Tm < 1                  *)
(* (MT 12.29: R(x,T0) <= (1 + eps)/(1 - T0) outside a compact set).  The    *)
(* normalized pullbacks of Gs by stds_nmap are C^2-close to the cylinder    *)
(* flow at basis 1 (STDS_ASYM_CLOSE), whose curvature is bounded by         *)
(* 1/(2(1 - Tm)) on [0,Tm]; curvature stability (LCK_CURVATURE_STABILITY)   *)
(* and the invariance of R under pullback (LSCALAR_PULLBACK) give           *)
(* R(Gs s)(x) <= Cs/(2(1 - Tm)) + 1.                                         *)
(* ------------------------------------------------------------------------- *)

let STDS_PUNCT_FACTS = prove
 (`smooth_manifold_atlas (subtopology euclidean ((:real^3) DELETE vec 0))
                         (open_set_atlas ((:real^3) DELETE vec 0)) /\
   topspace (subtopology euclidean ((:real^3) DELETE vec 0)) = (:real^3) DELETE vec 0 /\
   open ((:real^3) DELETE vec 0) /\
   (!t. t < &1 ==> riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0))
                                     (cylinder_flow t))`,
  SIMP_TAC[OPEN_SET_ATLAS; OPEN_DELETE; OPEN_UNIV; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; RFB_CYL_METRIC_FIELD]);;

(* The cylinder flow on [.,T], T < 1: bounds for the curvature norm and R. *)

let STDS_CYL_UNIF = prove
 (`?C0 Cs. &0 <= C0 /\ &0 <= Cs /\
           !T1 s (y:real^3).
             T1 < &1 /\ s <= T1 /\ ~(y = vec 0)
             ==> lrm_deriv_norm2 0 (cylinder_flow s) y <=
                 (sqrt C0 * inv(&2 * (&1 - T1))) pow 2 /\
                 lscalar (cylinder_flow s) y <= Cs * inv(&2 * (&1 - T1))`,
  X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SC"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_SCALAR_FROM_RMNORM) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RMD"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFA_R1_RMD0) THEN
  MAP_EVERY EXISTS_TAC [`C0:real`; `Cs:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`T1:real`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < &1 /\ &0 < &1 - T1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_rm_norm (open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow s) y <=
                inv(&2 * (&1 - T1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * (&1 - s))` THEN
    ASM_SIMP_TAC[STDS_CYL_RM_NORM] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(&2 * (&1 - T1))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "RMD" (MP_TAC o ISPECL
      [`subtopology euclidean ((:real^3) DELETE vec 0)`;
       `open_set_atlas ((:real^3) DELETE vec 0)`; `cylinder_flow s`; `y:real^3`;
       `inv(&2 * (&1 - T1))`]) THEN
    ASM_SIMP_TAC[STDS_PUNCT_FACTS; IN_DELETE; IN_UNIV] THEN
    ASM_SIMP_TAC[rfa_rmd2; STDS_P_CONV] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2];
    USE_THEN "SC" (MP_TAC o ISPECL
      [`subtopology euclidean ((:real^3) DELETE vec 0)`;
       `open_set_atlas ((:real^3) DELETE vec 0)`; `cylinder_flow s`; `y:real^3`;
       `inv(&2 * (&1 - T1))`]) THEN
    ASM_SIMP_TAC[STDS_PUNCT_FACTS; IN_DELETE; IN_UNIV] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
    REAL_ARITH_TAC]);;

(* The far-out bound.                                                        *)

let STDS_FAR_SCALAR = prove
 (`!g0 A0.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ stds_tm g0 < &1
     ==> ?Kc. !T'. &0 <= T' /\ T' < stds_tm g0
                   ==> ?A1. !x s. A1 < p3_std_dist g0 x /\ &0 <= s /\ s <= T'
                                  ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 s) x
                                      <= Kc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_CHOOSE_THEN `C0:real` (X_CHOOSE_THEN `Cs:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cyl"))))
    STDS_CYL_UNIF THEN
  ABBREV_TAC `Kt = inv(&2 * (&1 - stds_tm g0))` THEN
  MP_TAC(SPECL [`sqrt C0 * Kt`; `&1`]
    (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ST"))) THEN
  EXISTS_TAC `Cs * Kt + &1` THEN X_GEN_TAC `T':real` THEN STRIP_TAC THEN
  UNDISCH_TAC `stds_gs_hyps` THEN REWRITE_TAC[stds_gs_hyps] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`; `stds_gs g0`; `T':real`;
                `{basis 1:real^3}`; `2`; `eta pow 2`] STDS_ASYM_CLOSE) THEN
  ASM_SIMP_TAC[COMPACT_SING; REAL_POW_LT; SING_SUBSET; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ;
               IN_SING] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real` (LABEL_TAC "CL")) THEN
  EXISTS_TAC `max A2 (A0 + sqrt(&2) * (&0 + &1))` THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < stds_tm g0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A0 + sqrt(&2) * (&0 + &1) <= p3_std_dist g0 x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_NMAP_OPEN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--(&0 + &1))`;
                `exp(&0 + &1)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM stds_aW] THEN STRIP_TAC] THEN
  ABBREV_TAC `h = stds_nmap g0 A0 x` THEN
  ABBREV_TAC `U = IMAGE (h:real^3->real^3) (stds_aW 0)` THEN
  SUBGOAL_THEN `metric_field (U:real^3->bool) (stds_gs g0 s)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[stds_gs_hyps] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (stds_aW 0) (mpullback (h:real^3->real^3) (stds_gs g0 s)) /\
                metric_field (stds_aW 0) (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`;
        `(\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o p3_std_nc g0 A0`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      REWRITE_TAC[STDS_AW_SUBSET] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ST" (MP_TAC o SPECL [`stds_aW 0`; `cylinder_flow s`;
                                 `mpullback (h:real^3->real^3) (stds_gs g0 s)`;
                                 `basis 1:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[STDS_AW_BASIS] THEN CONJ_TAC THENL
     [USE_THEN "cyl" (MP_TAC o SPECL [`stds_tm g0`; `s:real`; `basis 1:real^3`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[STDS_BASIS1_NZ] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      EXPAND_TAC "h" THEN USE_THEN "CL" MATCH_MP_TAC THEN
      EXISTS_TAC `basis 1:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `stds_aW 0`; `h:real^3->real^3`;
                 `(\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o
                  p3_std_nc g0 A0`;
                 `stds_gs g0 s`; `basis 1:real^3`] LSCALAR_PULLBACK) THEN
  ASM_REWRITE_TAC[STDS_AW_BASIS] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) (basis 1) = x` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC STDS_NMAP_E1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SCALAR] THEN
  USE_THEN "cyl" (MP_TAC o SPECL [`stds_tm g0`; `s:real`; `basis 1:real^3`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[STDS_BASIS1_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The far-out bound on [T0,Tm).  Thm 12.28 gives canonical                 *)
(* neighbourhoods at all points with R >= r^-2, hence the derivative bounds *)
(* of CANON_DERIV there; Lemma 11.2 (LEMMA_11_2_DB) then keeps R below      *)
(* 2 (Kc + r^-2) on [T0,Tm) at every far-out point once Tm - T0 is below    *)
(* the uniform delta of 11.2 (MT 12.29).                                     *)
(* ------------------------------------------------------------------------- *)

let STDS_CANON_L_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps L x t.
     p2b_canon_L V C eps L x t
     ==> ?U. rfs_canonical_nbhd (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps x U`,
  REWRITE_TAC[FORALL_PAIR_THM; p2b_canon_L; rfs_canonical_nbhd; rfs_evolving_neck;
              rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

(* Thm 12.28 with the derivative bounds of CANON_DERIV.                       *)

let STDS_DERIV_BOUNDS = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> ?eps C. &0 < eps /\ &1 < C /\
           !g0 A0.
             p3_std_initial g0 A0
             ==> ?r. &0 < r /\
                   !x t. &0 <= t /\ t < stds_tm g0 /\
                         inv(r pow 2) <= rfs_vscalar (stds_gv g0) t x
                         ==> r pow 2 < t /\
                             p2b_canon_L (stds_gv g0) C eps (&1 + eps) x t /\
                             sqrt(rfs_scalar_grad2 (rfs_vatlas (stds_gv g0) t)
                                                   (rfs_vmetric (stds_gv g0) t) x) <=
                             max C (&2) * rfs_vscalar (stds_gv g0) t x *
                             sqrt(rfs_vscalar (stds_gv g0) t x) /\
                             abs(rfs_scalar_lap (rfs_vatlas (stds_gv g0) t)
                                                (rfs_vmetric (stds_gv g0) t) x +
                                 &2 * rfs_ric_norm2 (rfs_vatlas (stds_gv g0) t)
                                                    (rfs_vmetric (stds_gv g0) t) x) <=
                             max C (&2) * rfs_vscalar (stds_gv g0) t x pow 2`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_THM_12_28) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1228"))) THEN
  UNDISCH_TAC `P2C_CANON_DERIV_STATEMENT (:real^3)` THEN
  REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CD"))) THEN
  USE_THEN "T1228" (MP_TAC o SPEC `min eps1 eps0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0"))) THEN
  MAP_EVERY EXISTS_TAC [`min eps1 eps0`; `C0:real`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  USE_THEN "C0" (MP_TAC o SPECL [`C0:real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  USE_THEN "r" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM STDS_GV_SCALAR]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP STDS_CANON_L_SLICE) THEN
  DISCH_THEN(X_CHOOSE_TAC `U:real^3->bool`) THEN
  USE_THEN "CD" (MP_TAC o SPECL [`rfs_vtop (stds_gv g0) t`; `rfs_vatlas (stds_gv g0) t`;
                                 `rfs_vmetric (stds_gv g0) t`; `C0:real`;
                                 `min eps1 eps0`; `x:real^3`; `U:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[STDS_GV_PARTS] THEN
    REWRITE_TAC[P2C_EUCLID_FACTS] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[STDS_GV_SCALAR; STDS_GV_PARTS] THEN SIMP_TAC[]);;

(* The far-out bound on [0,Tm).                                              *)

let STDS_FAR_PROP = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0. p3_std_initial g0 A0 /\ stds_tm g0 < &1
                 ==> ?K A1. !x t. A1 < p3_std_dist g0 x /\ &0 <= t /\ t < stds_tm g0
                                  ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x
                                      <= K`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_DERIV_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))))))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_FAR_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kc:real` (LABEL_TAC "FS")) THEN
  ABBREV_TAC `C' = max C (&2)` THEN
  ABBREV_TAC `Kd = max (&0) Kc + inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 < C' /\ &0 < inv(r pow 2) /\ &0 < Kd` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ b /\ (b ==> c) ==> a /\ b /\ c`) THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "C'" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
      EXPAND_TAC "Kd" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dl = inv(&16 * C' * Kd)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = max (&0) (stds_tm g0 - dl / &2)` THEN
  SUBGOAL_THEN `&0 <= T0 /\ T0 < stds_tm g0 /\ stds_tm g0 - T0 <= dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "FS" (MP_TAC o SPEC `T0:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real` (LABEL_TAC "A1")) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `T0:real`] STDS_GS_RBOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  MAP_EVERY EXISTS_TAC [`max K0 (&2 * Kd)`; `A1:real`] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t <= T0` THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= k ==> a <= max k b`) THEN
    USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max k b`) THEN
  SUBGOAL_THEN `T0 < t /\ min T0 t = T0 /\ max T0 t = t` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (stds_gv g0) T0 x <= Kc` ASSUME_TAC THENL
   [REWRITE_TAC[STDS_GV_SCALAR] THEN USE_THEN "A1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 T0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `T0:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * C' * sqrt(max (rfs_vscalar (stds_gv g0) T0 x) (inv(r pow 2))))` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (rfs_vball (stds_gv g0) T0 x rr)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_GV_BALL] THEN REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  UNDISCH_TAC `P2C_LEMMA_11_2_DB_STATEMENT (:real^3)` THEN
  REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`stds_gv g0`; `C':real`; `r:real`; `x:real^3`; `T0:real`;
                             `t:real`; `rr:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`y:real^3`; `s:real`] THEN
      REWRITE_TAC[STDS_GV_TOPSPACE] THEN STRIP_TAC THEN
      USE_THEN "DB" (MP_TAC o SPECL [`y:real^3`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[STDS_GV_TOPSPACE] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl:real` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "Kd" THEN ASM_REAL_ARITH_TAC];
      USE_THEN "per" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      TRY DISCH_TAC THEN ASM_REWRITE_TAC[STDS_GV_PARTS] THEN
      SUBGOAL_THEN `&0 <= t /\ t < stds_tm g0` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MFD_DIFFEO_ID THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[STDS_GV_BALL; MFD_CENTRE_IN_BALL; P2C_EUCLID_FACTS; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[STDS_GV_SCALAR] THEN EXPAND_TAC "Kd" THEN
  UNDISCH_TAC `rfs_vscalar (stds_gv g0) T0 x <= Kc` THEN REWRITE_TAC[STDS_GV_SCALAR] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two fixed objects of MT's volume argument.  A far-out                *)
(* open shell W, A1 + 1 < d(x) < A1 + 2, whose volume stays above c0 > 0 on *)
(* [0,Tm) because abs Rm <= R/2 <= K1/2 there (SNGL_METRIC_EQUIV_LOCAL and *)
(* MFD_HAS_VOLUME_COMPARE_QF); and a bound A2 on the g(t)-distances between *)
(* points of d-distance at most D, for tau <= t < Tm (metric equivalence on *)
(* [0,tau] and Lemma 3.14 after tau).                                        *)
(* ------------------------------------------------------------------------- *)

let STDS_SHELL_OPEN = prove
 (`!g0 A0 a b.
     p3_std_initial g0 A0 /\ &0 <= a /\ &0 <= b
     ==> {y:real^3 | a < p3_std_dist g0 y /\ p3_std_dist g0 y < b} =
         annulus (p3s_rad_rinv g0 a) (p3s_rad_rinv g0 b) /\
         open {y:real^3 | a < p3_std_dist g0 y /\ p3_std_dist g0 y < b} /\
         bounded {y:real^3 | a < p3_std_dist g0 y /\ p3_std_dist g0 y < b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b /\ c) ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; annulus] THEN GEN_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `a:real`; `x:real^3`] P2CN_DIST_COMPARE) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `b:real`; `x:real^3`] P2CN_DIST_COMPARE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^3,p3s_rad_rinv g0 b)` THEN
    REWRITE_TAC[BOUNDED_BALL; SUBSET; annulus; IN_BALL_0; IN_ELIM_THM] THEN
    SIMP_TAC[]]);;

let STDS_SHELL = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 K1 A1.
           p3_std_initial g0 A0 /\ &0 <= A1 /\
           (!x t. A1 < p3_std_dist g0 x /\ &0 <= t /\ t < stds_tm g0
                  ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K1)
           ==> ?W c0. open W /\ ~(W = {}) /\ &0 < c0 /\
                      (!y. y IN W ==> A1 < p3_std_dist g0 y /\ p3_std_dist g0 y <= A1 + &2) /\
                      !t. &0 <= t /\ t < stds_tm g0
                          ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3))
                                                 (stds_gs g0 t) W v /\ c0 <= v`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `K1:real`; `A1:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < stds_tm g0
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t) /\
                        metric_field (:real^3) (stds_gs g0 t)`
  (LABEL_TAC "riem") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC STDS_GS_RIEM THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) g0` ASSUME_TAC THENL
   [USE_THEN "riem" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1 + &1`; `A1 + &2`] STDS_SHELL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1:real`; `A1 + &3`] STDS_SHELL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2)] THEN
  ABBREV_TAC `W = {y:real^3 | A1 + &1 < p3_std_dist g0 y /\ p3_std_dist g0 y < A1 + &2}` THEN
  ABBREV_TAC `Wf = {y:real^3 | A1 < p3_std_dist g0 y /\ p3_std_dist g0 y < A1 + &3}` THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET Wf` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "Wf"] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(W:real^3->bool = {})` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `\n:num. A1 + &3 / &2`] STDS_FAR_SEQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `xs:num->real^3` (MP_TAC o SPEC `0`)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    EXISTS_TAC `(xs:num->real^3) 0` THEN EXPAND_TAC "W" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the rm_norm bound on Wf and the metric equivalence there *)
  SUBGOAL_THEN
   `!t y. &0 <= t /\ t < stds_tm g0 /\ y IN Wf
          ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) y <= max (&0) (K1 / &2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `y:real^3`]
                 STDS_GS_SEC_CONSEQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) y <= K1` MP_TAC THENL
     [USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN Wf` THEN EXPAND_TAC "Wf" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `stds_gs g0`;
                 `&0`; `stds_tm g0`; `Wf:real^3->bool`; `max (&0) (K1 / &2)`]
                SNGL_METRIC_EQUIV_LOCAL) THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; REAL_LE_MAX; REAL_LE_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(LABEL_TAC "EQ") THEN
  SUBGOAL_THEN `&0 <= &2 * (&2 * max (&0) (K1 / &2)) * stds_tm g0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = exp(&2 * (&2 * max (&0) (K1 / &2)) * stds_tm g0)` THEN
  SUBGOAL_THEN `&0 < lam /\ &1 <= lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC(SPEC `&2 * (&2 * max (&0) (K1 / &2)) * stds_tm g0` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* volumes exist *)
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < stds_tm g0
        ==> mfd_has_volume (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) W
              (mfd_volume (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) W)`
  (LABEL_TAC "VOL") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)` ASSUME_TAC THENL
     [USE_THEN "riem" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `stds_gs g0 t`; `closure(W:real^3->bool)`] MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; COMPACT_IN_EUCLIDEAN; COMPACT_CLOSURE] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `stds_gs g0 t`; `W:real^3->bool`; `closure(W:real^3->bool)`; `w:real`]
                  MFD_HAS_VOLUME_SUBSET) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; CLOSURE_SUBSET] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0 W
                  (mfd_volume (euclidean,open_set_atlas (:real^3)) g0 W)` ASSUME_TAC THENL
   [USE_THEN "VOL" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `v0 = mfd_volume (euclidean,open_set_atlas (:real^3)) g0 W` THEN
  SUBGOAL_THEN `&0 < v0` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `g0:real^3->real^3^3`; `W:real^3->bool`]
                         MFD_HAS_VOLUME_OPEN_POS) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `v0 / (lam * sqrt lam)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LT];
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  EXISTS_TAC `mfd_volume (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) W` THEN
  USE_THEN "VOL" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; SQRT_POS_LT] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t) /\
                metric_field (:real^3) (stds_gs g0 t)` STRIP_ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b l m. a <= l * m * b ==> a <= b * (l * m)`) THEN
  MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `g0:real^3->real^3^3`; `stds_gs g0 t`; `W:real^3->bool`]
                       MFD_HAS_VOLUME_COMPARE_QF) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
  USE_THEN "EQ" (MP_TAC o SPECL [`t:real`; `y:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `&0 <= w dot (stds_gs g0 t y ** w) /\
                exp(&2 * (&2 * max (&0) (K1 / &2)) * t) <= lam`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `metric_field (:real^3) (stds_gs g0 t)` THEN
      REWRITE_TAC[metric_field; IN_UNIV] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN
      ASM_CASES_TAC `w:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * (&2 * max (&0) (K1 / &2)) * t) * (w dot (stds_gs g0 t y ** w))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(w:real^3) dot ((g0:real^3->real^3^3) y ** w) =
      exp(&2 * (&2 * max (&0) (K1 / &2)) * t) *
      (exp(--(&2 * (&2 * max (&0) (K1 / &2)) * t)) * (w dot (g0 y ** w)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* g(t)-distances, tau <= t < Tm, between points at d-distance <= D from     *)
(* the tip are bounded: metric equivalence with g0 on [0,tau]                *)
(* (STNC_METRIC_EQUIV, RFAH_DIST_COMPARE), and Lemma 3.14 (Ric >= 0) after   *)
(* tau.                                                                       *)

let STDS_DIST_BOUND = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 tau D.
           p3_std_initial g0 A0 /\ &0 < tau /\ tau < stds_tm g0
           ==> ?A2. !x y t. p3_std_dist g0 x <= D /\ p3_std_dist g0 y <= D /\
                            tau <= t /\ t < stds_tm g0
                            ==> mfd_dist (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t)
                                         x y < A2`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `tau:real`; `D:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`; `stds_gs g0`; `tau:real`]
               STNC_METRIC_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < stds_tm g0
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)`
  (LABEL_TAC "riem") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) g0` ASSUME_TAC THENL
   [USE_THEN "riem" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `sqrt L * (&2 * D) + &1` THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 tau) /\
                riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* (1) at time 0 *)
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) g0 x y <= &2 * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (euclidean,open_set_atlas (:real^3)) g0 x (vec 0) +
                mfd_dist (euclidean,open_set_atlas (:real^3)) g0 (vec 0) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[P2C_EUCLID_FACTS; P2C_RAD_JOINABLE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `x:real^3`; `vec 0:real^3`] MFD_DIST_SYM) THEN
    REWRITE_TAC[P2C_EUCLID_FACTS] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `p3_std_dist g0 x <= D` THEN UNDISCH_TAC `p3_std_dist g0 y <= D` THEN
    REWRITE_TAC[p3_std_dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (2) at time tau *)
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) (stds_gs g0 tau) x y <=
                sqrt L * mfd_dist (euclidean,open_set_atlas (:real^3)) g0 x y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFAH_DIST_COMPARE THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; P2C_RAD_JOINABLE; IN_UNIV] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN
      USE_THEN "L" (MP_TAC o SPECL [`tau:real`; `z:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* (3) from tau to t *)
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t) x y <=
                mfd_dist (euclidean,open_set_atlas (:real^3)) (stds_gs g0 tau) x y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `P2_LEMMA_3_14_STATEMENT (:real^3)` THEN
    REWRITE_TAC[P2_LEMMA_3_14_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `stds_tm g0`] THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; P2C_EUCLID_FACTS; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p3_partial_std g0 (stds_tm g0) (stds_gs g0)` THEN
      SIMP_TAC[p3_partial_std; ricci_flow_from];
      MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`; `z:real^3`]
                   STDS_GS_SEC_CONSEQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt L` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L * mfd_dist (euclidean,open_set_atlas (:real^3)) g0 x y <=
                sqrt L * (&2 * D)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* R is bounded on R^3 x [0,Tm) if Tm < 1 (MT 12.29, Claim                  *)
(* 12.30).  Far out by STDS_FAR_PROP; if R were unbounded, points (x_n,t_n) *)
(* with R -> inf lie at d-distance <= A1, have t_n -> Tm, and satisfy the   *)
(* blow-up hypotheses; the kappa-solution limit has asymptotic volume ratio *)
(* 0, so by LIM_VOL and Bishop-Gromov the balls B(x_n,t_n,A2) have volume   *)
(* < c0/2 for large n, while they contain the shell W of volume >= c0.      *)
(* ------------------------------------------------------------------------- *)

let STDS_VOL_ARITH = prove
 (`!c0 A2 A Q v e vk1 vb.
     &0 < c0 /\ &0 < A2 /\ &0 < A /\ &0 < Q /\
     v < c0 / (&32 * A2 pow 3) * A pow 3 /\ e = c0 / (&32 * A2 pow 3) * A pow 3 /\
     Q * sqrt Q * vk1 <= v + e /\
     vb / A2 pow 3 <= vk1 / (A / &2 * inv(sqrt Q)) pow 3 /\ c0 <= vb
     ==> F`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = sqrt Q` THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 = Q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `eps = c0 / (&32 * A2 pow 3)` THEN
  SUBGOAL_THEN `&0 < A pow 3 /\ &0 < A2 pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `vk1 / (A / &2 * inv s) pow 3 = (&8 * (Q * s * vk1)) / A pow 3`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s pow 2 = Q`)) THEN
    UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&8 * (Q * s * vk1)) / A pow 3 < &16 * eps` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `Q * s * vk1 < &2 * eps * A pow 3` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `vb / A2 pow 3 < &16 * eps` MP_TAC THENL
   [UNDISCH_TAC `vb / A2 pow 3 <= vk1 / (A / &2 * inv s) pow 3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(&8 * (Q * s * vk1)) / A pow 3 < &16 * eps` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `(&16 * eps) * A2 pow 3 = c0 / &2` SUBST1_TAC THENL
   [EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 < A2 pow 3` THEN CONV_TAC REAL_FIELD;
    ASM_REAL_ARITH_TAC]);;

let STDS_RBOUND_ALL = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0. p3_std_initial g0 A0 /\ stds_tm g0 < &1
                 ==> ?K. !x t. &0 <= t /\ t < stds_tm g0
                               ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x
                                   <= K`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  (* the constants of 11.8 and 12.28 *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2C_THM_11_8_VIEW_STATEMENT] o check (fun th ->
    concl th = `P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e118:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T118"))) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_THM_12_28) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1228:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `min e118 e1228`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPECL [`C:real`; `g0:real^3->real^3^3`; `A0:real`]))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T1228"))) THEN
  ABBREV_TAC `eps = min e118 e1228` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= e118` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* basic facts *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cpl") (LABEL_TAC "per"))))))) THEN
  UNDISCH_TAC `P2C_STD_NONCOLL_STATEMENT` THEN REWRITE_TAC[P2C_STD_NONCOLL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`;
                             `stds_gs g0`]) THEN
  ASM_REWRITE_TAC[GSYM stds_gv] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)) THEN
  (* far-out bound, shell, distances *)
  MP_TAC(SPEC `d:real^4->bool` STDS_FAR_PROP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `A1':real` (LABEL_TAC "far0"))) THEN
  ABBREV_TAC `A1 = max (&0) A1'` THEN
  SUBGOAL_THEN `&0 <= A1 /\
                !x t. A1 < p3_std_dist g0 x /\ &0 <= t /\ t < stds_tm g0
                      ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K1`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")) THENL
   [EXPAND_TAC "A1" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "far0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_SHELL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `K1:real`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` (X_CHOOSE_THEN `c0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "Win") (LABEL_TAC "Wvol"))))))) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_DIST_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0 / &2`;
                             `A1 + &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2':real` (LABEL_TAC "dist0")) THEN
  ABBREV_TAC `A2 = max A2' (&1)` THEN
  SUBGOAL_THEN `&0 < A2 /\
                !x y t. p3_std_dist g0 x <= A1 + &2 /\ p3_std_dist g0 y <= A1 + &2 /\
                        stds_tm g0 / &2 <= t /\ t < stds_tm g0
                        ==> mfd_dist (euclidean,open_set_atlas (:real^3)) (stds_gs g0 t)
                                     x y < A2`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist")) THENL
   [EXPAND_TAC "A2" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `a < b ==> a < max b c`) THEN
    USE_THEN "dist0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the contradiction *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `max (&n) (max K1 (inv(r pow 2)))` o
    REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] o
    check (fun th -> is_neg (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num->real^3` (X_CHOOSE_THEN `ts:num->real`
    (LABEL_TAC "seq")) o REWRITE_RULE[SKOLEM_THM]) THEN
  SUBGOAL_THEN `&0 < inv(r pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. p3_std_dist g0 ((xs:num->real^3) n) <= A1` (LABEL_TAC "xX") THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    USE_THEN "far" (MP_TAC o SPECL [`(xs:num->real^3) n`; `(ts:num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= (ts:num->real) n /\ ts n < stds_tm g0 /\
                    &0 < rfs_vscalar (stds_gv g0) (ts n) ((xs:num->real^3) n)`
  (LABEL_TAC "tn") THENL
   [GEN_TAC THEN USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN
    REWRITE_TAC[STDS_GV_SCALAR] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!B. ?N. !n. N <= n
                     ==> B < rfs_vscalar (stds_gv g0) ((ts:num->real) n) ((xs:num->real^3) n)`
  (LABEL_TAC "big") THENL
   [X_GEN_TAC `B:real` THEN MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[STDS_GV_SCALAR] THEN
    SUBGOAL_THEN `B <= &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> stds_tm g0 - e < (ts:num->real) n`
  (LABEL_TAC "tlim") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0 - e`] STDS_GS_RBOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "Kb")) THEN
    MP_TAC(SPEC `Kb:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    USE_THEN "Kb" (MP_TAC o SPECL [`(xs:num->real^3) n`; `(ts:num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `Kb <= &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y s. &0 <= s /\ s <= (ts:num->real) n /\
            &2 * rfs_vscalar (stds_gv g0) (ts n) ((xs:num->real^3) n) <
            rfs_vscalar (stds_gv g0) s y
            ==> p3_canon_at (stds_gv g0) C eps y s`
  (LABEL_TAC "can") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC STDS_CANON_L_IMP THEN EXISTS_TAC `&1 + eps` THEN
    USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv(r pow 2) <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 s) y`
    ASSUME_TAC THENL
     [UNDISCH_TAC `&2 * rfs_vscalar (stds_gv g0) ((ts:num->real) n) ((xs:num->real^3) n) <
                   rfs_vscalar (stds_gv g0) s y` THEN
      REWRITE_TAC[STDS_GV_SCALAR] THEN
      UNDISCH_TAC `max (&n) (max K1 (inv(r pow 2))) <
                   mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 ((ts:num->real) n))
                              ((xs:num->real^3) n)` THEN
      UNDISCH_TAC `&0 < inv(r pow 2)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "T1228" (MP_TAC o SPECL [`y:real^3`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[STDS_GV_SCALAR] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `C:real`; `eps:real`; `kappa:real`;
                `r0:real`; `xs:num->real^3`; `ts:num->real`] STDS_BLOWUP_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* compact closures of the rescaled balls (complete slices) *)
  SUBGOAL_THEN
   `!A. ?N. !n:num. N <= n
            ==> compact_in (rfs_vtop (stds_gv g0) (ts n))
                  (rfs_vtop (stds_gv g0) (ts n) closure_of
                   rfs_vball (stds_gv g0) (ts n) ((xs:num->real^3) n)
                     (A * inv(sqrt(rfs_vscalar (stds_gv g0) (ts n) (xs n)))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "tn" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[STDS_GV_BALL; STDS_GV_PARTS] THEN
    MATCH_MP_TAC RFU_BALL_CLOSURE_COMPACT THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; P2C_EUCLID_FACTS] THEN
    ASM_MESON_TAC[STDS_GS_RIEM; STDS_GS_BASICS];
    ALL_TAC] THEN
  USE_THEN "T118" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `&1`;
                                  `\n:num. stds_gv g0`; `xs:num->real^3`; `ts:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FL") (LABEL_TAC "KS")))))))) THEN
  SUBGOAL_THEN `p3_flow_limit (\n:num. stds_gv g0) ((xs:num->real^3) o (sub:num->num))
                  ((ts:num->real) o sub)
                  (\n. rfs_vscalar (stds_gv g0) (ts (sub n)) (xs (sub n)))
                  (top:(real^3)topology,atlas) g xl (&1)` ASSUME_TAC THENL
   [USE_THEN "FL" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ksep (top:(real^3)topology) atlas` ASSUME_TAC THENL
   [REWRITE_TAC[p2b_ksep] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] P2B_SEP_LIMIT_VIEW);
      MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] P2B_LORIENT_LIMIT_VIEW)] THEN
    REWRITE_TAC[P2B_SEP_LIMIT_VIEW_STATEMENT; P2B_LORIENT_LIMIT_VIEW_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`\n:num. stds_gv g0`; `(xs:num->real^3) o (sub:num->num)`;
      `(ts:num->real) o (sub:num->num)`;
      `\n:num. rfs_vscalar (stds_gv g0) ((ts:num->real) ((sub:num->num) n))
                                       ((xs:num->real^3) (sub n))`;
      `g:real->real^3->real^3^3`; `xl:real^3`; `&1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xl:real^3) IN topspace top /\ hausdorff_space (top:(real^3)topology) /\
                smooth_manifold_atlas top atlas /\
                riemannian_metric atlas ((g:real->real^3->real^3^3) (&0)) /\
                mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top:(real^3)topology,atlas) g` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p3_flow_limit (\n:num. stds_gv g0) ((xs:num->real^3) o (sub:num->num))
                     ((ts:num->real) o sub)
                     (\n. rfs_vscalar (stds_gv g0) (ts (sub n)) (xs (sub n)))
                     (top:(real^3)topology,atlas) g xl (&1)` THEN
      REWRITE_TAC[p3_flow_limit] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
      REWRITE_TAC[rfs_flow_upto] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c0 / (&32 * A2 pow 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  UNDISCH_TAC `P2B_AVR_ZERO_FIX_STATEMENT (:real^3)` THEN
  REWRITE_TAC[P2B_AVR_ZERO_FIX_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:(real^3)topology`;
    `atlas:((real^3->bool)#(real^3->real^3))->bool`; `g:real->real^3->real^3^3`; `xl:real^3`;
    `c0 / (&32 * A2 pow 3)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B11_P3_SLICE o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_flow_limit")) (concl th) &&
    not (is_forall (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Wl:num->real^3->bool` (X_CHOOSE_THEN `phi:num->real^3->real^3`
    (MP_TAC o MATCH_MP P2B11_SLICE_TO_FLOW0))) THEN
  DISCH_THEN(LABEL_TAC "FW") THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] LIM_VOL) THEN REWRITE_TAC[LIM_VOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n:num. stds_gv g0`; `(xs:num->real^3) o (sub:num->num)`;
    `(ts:num->real) o (sub:num->num)`;
    `\n:num. rfs_vscalar (stds_gv g0) ((ts:num->real) ((sub:num->num) n))
                                     ((xs:num->real^3) (sub n))`;
    `{&0}`; `top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
    `\s:real. (g:real->real^3->real^3^3) (&0)`; `xl:real^3`; `Wl:num->real^3->bool`;
    `phi:num->real^3->real^3`; `&0`; `xl:real^3`; `A / &2`; `A:real`;
    `mfd_volume (top,atlas) ((g:real->real^3->real^3^3) (&0))
                (mfd_ball (top,atlas) (g (&0)) xl (A / &2))`;
    `v:real`; `c0 / (&32 * A2 pow 3) * A pow 3`]) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `tau:real` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; STDS_GV_TOPSPACE] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[STDS_GV_PARTS; P2C_EUCLID_FACTS] THEN
        MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `tau:real`] STDS_GS_RIEM) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        GEN_TAC THEN REWRITE_TAC[STDS_GV_PARTS] THEN COND_CASES_TAC THEN
        REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; HAUSDORFF_SPACE_DISCRETE_TOPOLOGY];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
        MP_TAC(ISPECL [`top:(real^3)topology`; `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                       `(g:real->real^3->real^3^3) (&0)`; `xl:real^3`; `A / &2`]
                      MFD_HAS_VOLUME_BALL) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "LV")) THEN
  USE_THEN "tlim" (MP_TAC o SPEC `stds_tm g0 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1"))] THEN
  MP_TAC(SPEC `(A / (&2 * A2)) pow 2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  ABBREV_TAC `k = (k0 + N1 + N2):num` THEN
  SUBGOAL_THEN `k <= (sub:num->num) k` ASSUME_TAC THENL
   [MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Tk = (ts:num->real) ((sub:num->num) k)` THEN
  ABBREV_TAC `X = (xs:num->real^3) ((sub:num->num) k)` THEN
  ABBREV_TAC `Q = mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 Tk) X` THEN
  SUBGOAL_THEN `&0 <= Tk /\ Tk < stds_tm g0 /\ stds_tm g0 / &2 <= Tk /\ &0 < Q /\
                (A / (&2 * A2)) pow 2 <= Q /\ p3_std_dist g0 X <= A1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "X"; "Tk"] THEN
    USE_THEN "tn" (MP_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "seq" (MP_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "xX" (MP_TAC o SPEC `(sub:num->num) k`) THEN
    USE_THEN "N1" (MP_TAC o SPEC `(sub:num->num) k`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `k <= (sub:num->num) k` THEN EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[STDS_GV_SCALAR] THEN
    SUBGOAL_THEN `(A / (&2 * A2)) pow 2 <= &((sub:num->num) k)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `k <= (sub:num->num) k` THEN EXPAND_TAC "k" THEN ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "LV" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[o_THM; REAL_FIELD `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(phi:num->real^3->real^3) k xl = X` SUBST1_TAC THENL
   [UNDISCH_TAC `p2c_flow_limit_with (\n:num. stds_gv g0) ((xs:num->real^3) o (sub:num->num))
                   ((ts:num->real) o sub)
                   (\n. rfs_vscalar (stds_gv g0) (ts (sub n)) (xs (sub n)))
                   {&0} (top:(real^3)topology,atlas) (\s. (g:real->real^3->real^3^3) (&0)) xl
                   Wl phi` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN STRIP_TAC THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[STDS_GV_PARTS; STDS_GV_SCALAR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk1:real` (X_CHOOSE_THEN `vk2:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 Tk) /\
                mfd_complete (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `Tk:real`] STDS_GS_RIEM) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `Tk:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "stds_rotm")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `vb = mfd_volume (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk)
                     (mfd_ball (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk) X A2)` THEN
  SUBGOAL_THEN `mfd_has_volume (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk)
                  (mfd_ball (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk) X A2) vb`
  ASSUME_TAC THENL
   [EXPAND_TAC "vb" THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `stds_gs g0 Tk`; `X:real^3`; `A2:real`] MFD_HAS_VOLUME_BALL) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vb / A2 pow 3 <= vk1 / (A / &2 * inv(sqrt Q)) pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_REQ_BISHOP_GROMOV_STATEMENT (:real^3)` THEN
    REWRITE_TAC[P2C_REQ_BISHOP_GROMOV_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `euclidean:(real^3)topology` THEN EXISTS_TAC `open_set_atlas (:real^3)` THEN
    EXISTS_TAC `stds_gs g0 Tk` THEN EXISTS_TAC `X:real^3` THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; HAUSDORFF_SPACE_EUCLIDEAN; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `A / (&2 * A2) <= sqrt Q` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt Q` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `A / (&2 * A2) <= sqrt Q` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET
                mfd_ball (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk) X A2`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM; P2C_RAD_JOINABLE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "Win" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `p3_std_dist g0 X <= A1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Wvol" (MP_TAC o SPEC `Tk:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vw:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `vw <= vb` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                         `stds_gs g0 Tk`; `W:real^3->bool`;
                         `mfd_ball (euclidean,open_set_atlas (:real^3)) (stds_gs g0 Tk) X A2`]
                        MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  MATCH_MP_TAC STDS_VOL_ARITH THEN
  MAP_EVERY EXISTS_TAC [`c0:real`; `A2:real`; `A:real`; `Q:real`; `v:real`;
                        `c0 / (&32 * A2 pow 3) * A pow 3`; `vk1:real`; `vb:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Thm 12.29, Tm = 1.  Bounded R on [0,Tm) gives abs Rm <=               *)
(* R/2 bounded, uniform restart data (|sec| <= Kh, F(1) >= F1 by the metric *)
(* equivalence on [0,Tm)), and a restart at t1 = max 0 (Tm - delta/2)        *)
(* glued to Gs (STDS_GLUE) is a partial standard flow on [0,t1 + delta),     *)
(* t1 + delta > Tm, against maximality (STDS_GS_BASICS).  With Tm <= 1 and  *)
(* STDS_RBOUND_ALL this gives Tm = 1.                                        *)
(* ------------------------------------------------------------------------- *)

let STDS_GS_UNIF_ALL = prove
 (`!g0 A0 K0.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ &0 <= K0 /\
     (!t x. &0 <= t /\ t < stds_tm g0
            ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K0)
     ==> ?F1. &0 < F1 /\
              !t. &0 <= t /\ t < stds_tm g0 ==> F1 <= stds_mFh (stds_gs g0 t) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < stds_tm g0
                    ==> riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[STDS_RIEM_UNIV_EQ] THEN
    ASM_MESON_TAC[STDS_RT_METRIC_FIELD];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RIC"))) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`;
                 `stds_tm g0`; `stds_gs g0`; `Cr * K0`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "RIC" (MP_TAC o ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                     `stds_gs g0 t`; `x:real^3`; `K0:real`; `v:real^3`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_MUL_ASSOC]] THEN
    REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "EQV")] THEN
  EXISTS_TAC `sqrt(exp(--(&2 * (Cr * K0) * stds_tm g0)) * p3s_rad_b g0 (&1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_MESON_TAC[P3S_ROT_AB];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[stds_mFh; REAL_MUL_LID] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  SUBGOAL_THEN `&0 < p3s_rad_b g0 (&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_ROT_AB]; ALL_TAC] THEN
  USE_THEN "EQV" (MP_TAC o SPECL [`t:real`; `&1 % basis 1:real^3`; `basis 2:real^3`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[GSYM p3s_rad_b] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `(Cr * K0) * t <= (Cr * K0) * stds_tm g0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Bounded scalar curvature on [0,Tm) is impossible: a restart extends Gs.    *)

let STDS_EXTEND_CONTRA = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 K. p3_std_initial g0 A0 /\
                   (!x t. &0 <= t /\ t < stds_tm g0
                          ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K)
                   ==> F`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `K:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RB")) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_RESTART) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rc") (LABEL_TAC "un")))))) THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (stds_tm g0)
                  (stds_gs g0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_partial_std]; ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  ABBREV_TAC `K0 = max (&0) (K / &2)` THEN
  SUBGOAL_THEN `&0 <= K0` ASSUME_TAC THENL [EXPAND_TAC "K0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. &0 <= t /\ t < stds_tm g0
          ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K0`
  (LABEL_TAC "RM") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `x:real^3`]
                 STDS_GS_SEC_CONSEQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    USE_THEN "RB" (MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "K0" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `K0:real`] STDS_GS_UNIF_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F1"))) THEN
  ABBREV_TAC `dl = c / max (&1) (stds_mK K0 F1)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = max (&0) (stds_tm g0 - dl / &2)` THEN
  SUBGOAL_THEN `&0 <= t1 /\ t1 < stds_tm g0 /\ stds_tm g0 < t1 + dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the restart at t1 *)
  USE_THEN "rs" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_gs g0 t1`;
                                 `K0:real`; `F1:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[stds_rgood] THEN
      USE_THEN "rc" (MP_TAC o SPEC `t1:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN STRIP_TAC THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "F1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t1) x` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN
        EXISTS_TAC `euclidean:(real^3)topology` THEN
        ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN
        REWRITE_TAC[STDS_RIEM_UNIV_EQ] THEN MATCH_MP_TAC STDS_RT_METRIC_FIELD THEN
        USE_THEN "rc" (MP_TAC o SPEC `t1:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "RM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?K1. !t x. &0 <= t /\ t <= t1
                           ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 t) x <= K1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `K0:real` THEN REPEAT STRIP_TAC THEN USE_THEN "RM" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t1 = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `p3_partial_std g0 dl (H:real->real^3->real^3^3)` ASSUME_TAC THENL
     [REWRITE_TAC[p3_partial_std] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t2:real` THEN DISCH_TAC THEN
      EXISTS_TAC `C * max (&1) (stds_mK K0 F1)` THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "un" (MP_TAC o SPECL [`dl:real`; `H:real->real^3->real^3^3`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G' = \t. if t < t1 then stds_gs g0 t else (H:real->real^3->real^3^3) (t - t1)` THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (t1 + dl)
                  (G':real->real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G'" THEN MATCH_MP_TAC STDS_GLUE THEN EXISTS_TAC `stds_tm g0` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_partial_std g0 (t1 + dl) (G':real->real^3->real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p3_partial_std] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "G'" THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "G'" THEN BETA_TAC THEN
      COND_CASES_TAC THENL
       [USE_THEN "rc" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t2:real` THEN DISCH_TAC THEN
      EXISTS_TAC `max K1 (C * max (&1) (stds_mK K0 F1))` THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
      EXPAND_TAC "G'" THEN BETA_TAC THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max b c`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "un" (MP_TAC o SPECL [`t1 + dl`; `G':real->real^3->real^3^3`; `&0`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* MT Thm 12.29: the maximal standard flow lives on [0,1).                    *)

let STDS_TM_EQ_1 = prove
 (`!d:real^4->bool.
     stds_tm_hyps d ==> !g0 A0. p3_std_initial g0 A0 ==> stds_tm g0 = &1`,
  GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[stds_tm_hyps]; STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ ~(x < &1) ==> x = &1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_RBOUND_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_EXTEND_CONTRA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `K:real`]) THEN
  ASM_REWRITE_TAC[]);;

