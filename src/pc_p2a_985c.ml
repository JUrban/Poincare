(* ========================================================================= *)
(* pc_p2a_985c: COR_9_94_L piece (b) part (1) at a general base point (MT    *)
(* Remark 9.86) and the upper half of part (2).  A positively curved         *)
(* noncompact kappa-solution has a soul s (CMP_R5_SOUL); a base point p that *)
(* is no strong eps-neck centre lies in the soul ball of P2AS85_SOUL_NECKS,  *)
(* so R(p) <= C R(s) (LEMMA_9_65) and a larger radius about p works.  Upper  *)
(* curvature bound: K <= R(x) / 2 for nonnegative curvature                  *)
(* (P2BX0_RM_NORM_LE_HALF_SCALAR) and R(x) <= C R(p) on the ball             *)
(* (LEMMA_9_65).                                                             *)
(* ========================================================================= *)

needs "src/pc_p2a_s85b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part (1) at a general base point and the upper curvature bound of part    *)
(* (2).                                                                      *)
(* ========================================================================= *)

let P2A985C_NOT_IN_BALL = prove
 (`!top atlas (g:B->real^3^3) s x c D.
     &0 < c /\ D <= c * mfd_dist (top,atlas) g s x
     ==> ~(x IN mfd_ball (top,atlas) g s (D * inv c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN DISJ2_TAC THEN
  ASM_SIMP_TAC[P2AS85_INV_LE]);;

(* MT Prop 9.85 (1) with MT Remark 9.86: any base point that is no strong   *)
(* eps-neck centre; also a soul at rescaled distance < D from p.            *)

let P2A985C_PART1 = prove
 (`!w:B->bool.
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
     P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
     P2B_SOUL_TOPOLOGY_STATEMENT w
     ==> ?eps1. &0 < eps1 /\
           !eps L. &0 < eps /\ eps <= eps1 /\ &1 <= L
             ==> ?D. &1 < D /\
                   !kappa top atlas (g:real->B->real^3^3) p.
                      p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                      ~compact_space top /\
                      (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                               ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
                      p IN topspace top /\
                      ~(?e. rfs_strong_neck (p2b_kview (top,atlas) g) eps p (&0) e)
                      ==> (?s. s IN topspace top /\
                               (!z. z IN topspace top /\ ~(z = s)
                                    ==> p2b_dist_regular (top,atlas) (g(&0)) s z) /\
                               sqrt(mfd_scalar atlas (g(&0)) p) *
                               mfd_dist (top,atlas) (g(&0)) p s < D) /\
                          (!x. x IN topspace top /\
                               ~(x IN mfd_ball (top,atlas) (g(&0)) p
                                        (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))))
                               ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0)
                                                         L e)`,
  GEN_TAC THEN INTRO_TAC "t964 p958 l965 pk ch soul" THEN
  MP_TAC(SPEC `w:B->bool` P2AS85_SOUL_NECKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sn"))) THEN
  USE_THEN "p958" (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0sol")) o
    MATCH_MP P2AS85_KAPPA0) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN INTRO_TAC "ep ep1 L1" THEN
  USE_THEN "sn" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ds:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ds"))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `Ds:real`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (LABEL_TAC "Cr")) THEN
  SUBGOAL_THEN `&0 <= sqrt(abs Cr) /\ &0 <= sqrt(abs Cr) * Ds` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * Ds * (sqrt(abs Cr) + &1) + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < x + &1`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ksol ksep ncpt pos pin nsn" THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\
                riemannian_metric atlas ((g:real->B->real^3^3) (&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_kappa_solution kappa0 (top,atlas) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "k0sol" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[CMP_R5_SOUL_STATEMENT] (SPEC `w:B->bool` CMP_R5_SOUL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `(g:real->B->real^3^3) (&0)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sreg"))) THEN
  SUBGOAL_THEN
   `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s /\
    &0 < mfd_scalar atlas (g(&0)) p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) /\
    &0 < sqrt(mfd_scalar atlas (g(&0)) p)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  (* p lies in the soul ball *)
  SUBGOAL_THEN
   `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) *
    mfd_dist (top,atlas) (g(&0)) s p < Ds`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "nsn" MP_TAC THEN REWRITE_TAC[rfs_strong_neck] THEN
    USE_THEN "Ds" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `s:B`; `p:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A985C_NOT_IN_BALL THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`)] THEN
    EXISTS_TAC `e:real^3->B` THEN
    MATCH_MP_TAC P2BTL_EVNECK_LEN_MONO THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p <= Cr * mfd_scalar atlas (g(&0)) s`
  ASSUME_TAC THENL
   [USE_THEN "Cr" MATCH_MP_TAC THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p s = mfd_dist (top,atlas) (g(&0)) s p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. &0 <= d
        ==> sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p) * d <=
            sqrt(abs Cr) * (sqrt(mfd_scalar atlas (g(&0)) s) * d)`
  (LABEL_TAC "cmp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AS85_SCALE_ARITH THEN
    EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) s p` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `s:B` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cmp" (MP_TAC o SPEC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) s p`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `sqrt(abs Cr) * (sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) *
                      mfd_dist (top,atlas) (g(&0)) s p) <= sqrt(abs Cr) * Ds`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  USE_THEN "Ds" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `s:B`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2A985C_NOT_IN_BALL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:B`; `x:B`;
                 `&2 * Ds * (sqrt(abs Cr) + &1) + &1`] P2AS85_OUT_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p x` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "cmp" (MP_TAC o SPEC `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p x`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) * mfd_dist (top,atlas) (g(&0)) p x <=
    sqrt(mfd_scalar atlas (g(&0)) s) * mfd_dist (top,atlas) (g(&0)) s p +
    sqrt(mfd_scalar atlas (g(&0)) s) * mfd_dist (top,atlas) (g(&0)) s x`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`; `s:B`; `x:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * Ds <=
    sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) * mfd_dist (top,atlas) (g(&0)) p x`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `sqrt(abs Cr) * (sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) s) *
                      mfd_dist (top,atlas) (g(&0)) p x) <= sqrt(abs Cr) * (&2 * Ds)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The upper curvature bound of part (2). *)

let P2A985C_UPPER = prove
 (`!w:B->bool.
     P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w
     ==> !D. &0 < D
             ==> ?D1. &1 < D1 /\
                   !kappa top atlas (g:real->B->real^3^3) p x u v.
                      p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                      ~compact_space top /\ p IN topspace top /\
                      x IN mfd_ball (top,atlas) (g(&0)) p
                             (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
                      ~collinear {vec 0,u,v}
                      ==> mfd_sectional atlas (g(&0)) x u v < D1 * mfd_scalar atlas (g(&0)) p`,
  GEN_TAC THEN INTRO_TAC "p958 l965 pk" THEN X_GEN_TAC `D:real` THEN DISCH_TAC THEN
  USE_THEN "p958" (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0sol")) o
    MATCH_MP P2AS85_KAPPA0) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `D:real`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "C")) THEN
  EXISTS_TAC `abs C + &2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ksol ksep ncpt pin xin ncol" THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\
    (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
             ==> &0 <= mfd_sectional atlas (g(&0)) y u v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_kappa_solution kappa0 (top,atlas) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "k0sol" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p
                          (D * inv(sqrt(mfd_scalar atlas (g(&0)) p)))` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p /\
    &0 < mfd_scalar atlas (g(&0)) x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p) * mfd_dist (top,atlas) (g(&0)) p x < D`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN ASM_SIMP_TAC[GSYM P2AS85_INV_LE] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x <= C * mfd_scalar atlas (g(&0)) p`
  ASSUME_TAC THENL
   [USE_THEN "C" MATCH_MP_TAC THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x u v <=
    mfd_scalar atlas (g(&0)) x / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas ((g:real->B->real^3^3) (&0)) x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C * mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p <=
    abs C * mfd_scalar atlas (g(&0)) p /\
    &0 <= abs C * mfd_scalar atlas (g(&0)) p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

