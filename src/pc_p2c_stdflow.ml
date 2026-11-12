(* ========================================================================= *)
(* Unit pc_p2c_stdflow (Part 2C): MT Ch 12, Sec 12.2-12.3.                   *)
(*   STDS_UNIQUE_ROUTE |- P2C_STD_UNIQUE_ROUTE_STATEMENT: partial standard   *)
(*     flows agree, by the uniqueness of complete bounded-curvature flows   *)
(*     with a bounded-geometry exhaustion (P2C_REQ_UNIQ_COMPLETE) and        *)
(*     P2C_STD_BOUNDED_GEOM.                                                 *)
(*   STDS_PARTIAL_EXISTS_ROUTE |- !d:real^4->bool.                          *)
(*     P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT d: a partial standard flow     *)
(*     exists, as the geometric limit (Prop 5.14) of the flows of compact    *)
(*     doubles of the balls of g0 (PDE_CURVATURE_TIME: existence time and   *)
(*     curvature bound uniform in the radius).  The double lives on the     *)
(*     unit sphere of real^4; its two charts carry the coordinates of g0,    *)
(*     and the transition is the reflection of the cylindrical neck, an     *)
(*     isometry of g0 there.                                                 *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_rf_extend.ml";;
needs "src/pc_rfa_shi.ml";;
needs "src/pc_p3_s13met.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_p2c_fl515.ml";;
needs "src/pc_rf_unique_a14.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The uniqueness route.  Two partial standard flows are compared on [0, min *)
(* te te') by P2C_REQ_UNIQ_COMPLETE on (R^3, euclidean), with the bounded    *)
(* geometry and the exhaustion of P2C_STD_BOUNDED_GEOM.                      *)
(* ------------------------------------------------------------------------- *)

let STDS_PARTIAL_POS = prove
 (`!g0 te (G:real->real^3->real^3^3). p3_partial_std g0 te G ==> &0 < te`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let STDS_UNIQUE_ROUTE = prove
 (`P2C_STD_UNIQUE_ROUTE_STATEMENT`,
  REWRITE_TAC[P2C_STD_UNIQUE_ROUTE_STATEMENT; P2C_STD_UNIQUE_STATEMENT;
              P2C_REQ_UNIQ_COMPLETE_STATEMENT; P2C_STD_BOUNDED_GEOM_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A14") (LABEL_TAC "BG")) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `te':real`;
                       `G:real->real^3->real^3^3`; `G':real->real^3->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < te /\ &0 < te'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[STDS_PARTIAL_POS]; ALL_TAC] THEN
  USE_THEN "BG" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RMD")
    (X_CHOOSE_THEN `phi:real^3->real` (X_CHOOSE_THEN `C:real`
      (CONJUNCTS_THEN2 (LABEL_TAC "SM") (CONJUNCTS_THEN2 (LABEL_TAC "CPT")
        (CONJUNCTS_THEN2 (LABEL_TAC "GL") (LABEL_TAC "VOL"))))))) THEN
  UNDISCH_TAC `p3_partial_std g0 te' (G':real->real^3->real^3^3)` THEN
  UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
  REWRITE_TAC[p3_partial_std] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "I1")
    (CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "K1")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F2") (CONJUNCTS_THEN2 (LABEL_TAC "I2")
    (CONJUNCTS_THEN2 (LABEL_TAC "C2") (LABEL_TAC "K2")))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
  USE_THEN "A14" (MP_TAC o ISPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `min te te'`;
     `G:real->real^3->real^3^3`; `G':real->real^3->real^3^3`; `phi:real^3->real`;
     `C:real`]) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t < te` THEN UNDISCH_TAC `t < te'` THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; HAUSDORFF_SPACE_EUCLIDEAN;
              COMPACT_IN_EUCLIDEAN] THEN
  USE_THEN "I1" SUBST1_TAC THEN USE_THEN "I2" SUBST1_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < min te te' /\ min te te' <= te /\ min te te' <= te'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < te` THEN UNDISCH_TAC `&0 < te'` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `te:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `te':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "C1" MATCH_MP_TAC; USE_THEN "C2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `b1:real` THEN DISCH_TAC THEN
    USE_THEN "K1" (MP_TAC o SPEC `b1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `K1:real`)] THEN
    USE_THEN "K2" (MP_TAC o SPEC `b1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `K2:real`)] THEN
    EXISTS_TAC `max K1 K2` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH
      `!a b c. a <= b \/ a <= c ==> a <= max b c`) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "RMD" ACCEPT_TAC;
    USE_THEN "SM" ACCEPT_TAC;
    USE_THEN "CPT" ACCEPT_TAC;
    USE_THEN "GL" ACCEPT_TAC;
    USE_THEN "VOL" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The reflection of the cylindrical neck.  On the neck                      *)
(* A0 < d(x) < 2R - A0 (d the distance from the tip) the map                *)
(* stds_refl = ncinv o iota o nc, with iota y = c y / |y|^2, keeps the       *)
(* direction of x and sends d(x) to 2R - d(x); it is an involution and an   *)
(* isometry of g0 there, since g0 = nc^* cyl(0) beyond A0 and cyl(0) is     *)
(* invariant under dilations and the inversion.                             *)
(* ------------------------------------------------------------------------- *)

let stds_iota = new_definition
 `stds_iota (c:real) (y:real^3) = (c * inv(norm y pow 2)) % y`;;

let stds_cr = new_definition
 `stds_cr (A0:real) (R:real) = exp(&2 * (A0 + &4 - R) / sqrt(&2))`;;

let stds_refl = new_definition
 `stds_refl (g0:real^3->real^3^3) (A0:real) (R:real) =
    p3s_ncinv g0 A0 o stds_iota (stds_cr A0 R) o p3_std_nc g0 A0`;;

let stds_neck = new_definition
 `stds_neck (g0:real^3->real^3^3) (A0:real) (R:real) =
    {x:real^3 | A0 < p3_std_dist g0 x /\ p3_std_dist g0 x < &2 * R - A0}`;;

let STDS_NECK_NZ = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R ==> ~(x = vec 0) /\ &0 < A0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_A0_POS]; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN UNDISCH_TAC `A0 < p3_std_dist g0 (x:real^3)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `&0 < A0` THEN REAL_ARITH_TAC);;

let STDS_SQRT2_NZ = prove
 (`&0 < sqrt(&2) /\ ~(sqrt(&2) = &0)`,
  MP_TAC(SPEC `&2` SQRT_POS_LT) THEN REAL_ARITH_TAC);;

let STDS_UNIT_NORM = prove
 (`!x:real^3. ~(x = vec 0) ==> norm(inv(norm x) % x) = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0]);;

let STDS_NC_IOTA = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R
     ==> stds_iota (stds_cr A0 R) (p3_std_nc g0 A0 x) =
         exp((A0 + &4 - (&2 * R - p3_std_dist g0 x)) / sqrt(&2)) % (inv(norm x) % x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_NECK_NZ) THEN
  SUBGOAL_THEN
   `(stds_cr A0 R * inv(exp((A0 + &4 - p3_std_dist g0 (x:real^3)) / sqrt(&2)) pow 2)) *
    exp((A0 + &4 - p3_std_dist g0 x) / sqrt(&2)) =
    exp((A0 + &4 - (&2 * R - p3_std_dist g0 x)) / sqrt(&2))` ASSUME_TAC THENL
   [REWRITE_TAC[stds_cr] THEN
    REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_NEG; GSYM REAL_EXP_ADD] THEN
    AP_TERM_TAC THEN MP_TAC STDS_SQRT2_NZ THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[stds_iota] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_NC_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3_std_nc; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

let STDS_REFL_EXPLICIT = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R
     ==> stds_refl g0 A0 R x =
         (p3s_rad_rinv g0 (&2 * R - p3_std_dist g0 x) * inv(norm x)) % x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_NECK_NZ) THEN
  REWRITE_TAC[stds_refl; o_THM] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP STDS_NC_IOTA) THEN
  ABBREV_TAC `e = exp((A0 + &4 - (&2 * R - p3_std_dist g0 (x:real^3))) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &4 - sqrt(&2) * log e = &2 * R - p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[LOG_EXP] THEN MP_TAC STDS_SQRT2_NZ THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(e % inv(norm x) % (x:real^3)) = e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; STDS_UNIT_NORM] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3s_ncinv] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD);;

let STDS_REFL_PROPS = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R
     ==> ~(stds_refl g0 A0 R x = vec 0) /\
         norm(stds_refl g0 A0 R x) = p3s_rad_rinv g0 (&2 * R - p3_std_dist g0 x) /\
         p3_std_dist g0 (stds_refl g0 A0 R x) = &2 * R - p3_std_dist g0 x /\
         inv(norm(stds_refl g0 A0 R x)) % stds_refl g0 A0 R x = inv(norm x) % x /\
         stds_refl g0 A0 R x IN stds_neck g0 A0 R /\
         stds_refl g0 A0 R (stds_refl g0 A0 R x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_NECK_NZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 (x:real^3) /\ p3_std_dist g0 x < &2 * R - A0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN stds_neck g0 A0 R` THEN REWRITE_TAC[stds_neck; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_REFL_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 (&2 * R - p3_std_dist g0 (x:real^3))` THEN
  SUBGOAL_THEN `&0 < r /\ p3s_rad_rho g0 r = &2 * R - p3_std_dist g0 (x:real^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                     `&2 * R - p3_std_dist g0 (x:real^3)`] P3S_RINV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((r * inv(norm x)) % (x:real^3)) = r` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r * inv(norm x)) % (x:real^3) = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 ((r * inv(norm x)) % (x:real^3)) = &2 * R - p3_std_dist g0 x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `(r * inv(norm x)) % (x:real^3)`]
      P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm((r * inv(norm x)) % x)) % ((r * inv(norm x)) % x) =
                inv(norm x) % (x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r * inv(norm x)) % (x:real^3) IN stds_neck g0 A0 R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `stds_refl g0 A0 R ((r * inv(norm x)) % x) = (x:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `(r * inv(norm x)) % (x:real^3)`]
      STDS_REFL_EXPLICIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 * R - (&2 * R - p3_std_dist g0 (x:real^3)) = p3s_rad_rho g0 (norm x)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RINV_UNIQUE) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(norm(x:real^3) * inv r) * r * inv(norm x) = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The neck is an annulus in the coordinates of g0 (d(x) = rho(|x|)).  The   *)
(* comparison below is the first half of P2CN_DIST_COMPARE (pc_p2c_stdgeom), *)
(* whose proof it follows; that unit is not loaded here (its closure is      *)
(* large).                                                                   *)

let STDS_DIST_LT_EQ = prove
 (`!g0 A0 c (x:real^3).
     p3_std_initial g0 A0 /\ &0 <= c
     ==> (p3_std_dist g0 x < c <=> norm x < p3s_rad_rinv g0 c) /\
         (c < p3_std_dist g0 x <=> p3s_rad_rinv g0 c < norm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 c` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `r:real`]
                P3S_RHO_LT_EQ) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`; `norm(x:real^3)`]
                P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN SIMP_TAC[]);;

let STDS_NECK_NORM = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> stds_neck g0 A0 R =
         {x:real^3 | p3s_rad_rinv g0 A0 < norm x /\
                     norm x < p3s_rad_rinv g0 (&2 * R - A0)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; stds_neck; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
  SUBGOAL_THEN `&0 <= A0 /\ &0 <= &2 * R - A0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`; `x:real^3`] STDS_DIST_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&2 * R - A0`; `x:real^3`]
    STDS_DIST_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) THEN
  REWRITE_TAC[]);;

let STDS_NECK_OPEN = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R ==> open(stds_neck g0 A0 R)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STDS_NECK_NORM] THEN
  SUBGOAL_THEN
   `{x:real^3 | p3s_rad_rinv g0 A0 < norm x /\ norm x < p3s_rad_rinv g0 (&2 * R - A0)} =
    ball(vec 0,p3s_rad_rinv g0 (&2 * R - A0)) DIFF cball(vec 0,p3s_rad_rinv g0 A0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL]]);;

(* Smoothness of the reflection.                                             *)

let STDS_IOTA_SMOOTH = prove
 (`!c. smooth_map_on ((:real^3) DELETE vec 0) (stds_iota c)`,
  GEN_TAC THEN
  SUBGOAL_THEN `stds_iota c = (\y:real^3. c % (inv(norm y pow 2) % y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_iota; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  REWRITE_TAC[LRG_CYL_OPEN; STEX_SMOOTH_INVERSION]);;

let STDS_NC_NZ = prove
 (`!g0 A0 (x:real^3). ~(x = vec 0) ==> ~(p3_std_nc g0 A0 x = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  ASM_SIMP_TAC[P3S_NC_NORM; REAL_EXP_NZ]);;

let STDS_IOTA_NC_DOM = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R
     ==> ~(stds_iota (stds_cr A0 R) (p3_std_nc g0 A0 x) = vec 0) /\
         sqrt(&2) * log(norm(stds_iota (stds_cr A0 R) (p3_std_nc g0 A0 x))) < A0 + &4`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDS_NECK_NZ) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP STDS_NC_IOTA) THEN
  UNDISCH_TAC `p3_std_initial g0 A0 /\ (x:real^3) IN stds_neck g0 A0 R` THEN
  REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; STDS_UNIT_NORM; REAL_ABS_EXP; REAL_MUL_RID; LOG_EXP] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_EXP_NZ; DE_MORGAN_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0];
    MP_TAC STDS_SQRT2_NZ THEN
    SUBGOAL_THEN `&0 < &2 * R - p3_std_dist g0 (x:real^3)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_DIV_LMUL] THEN REAL_ARITH_TAC]);;

let STDS_REFL_SMOOTH = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
             ==> smooth_map_on (stds_neck g0 A0 R) (stds_refl g0 A0 R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_refl] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{y:real^3 | ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4}` THEN
  ASM_SIMP_TAC[STDS_NECK_OPEN; P3S_NCINV_DOM_OPEN; P3S_NCINV_SMOOTH] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC STDS_IOTA_NC_DOM THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[STDS_NECK_OPEN; LRG_CYL_OPEN; STDS_IOTA_SMOOTH] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC STDS_NC_NZ THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`]
        STDS_NECK_NZ) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[P3S_NC_SMOOTH] THEN
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`]
        STDS_NECK_NZ) THEN ASM_SIMP_TAC[]]]);;

(* The reflection is an isometry of g0 on the neck.                          *)

let STDS_IOTA_CYL0 = prove
 (`!c (y:real^3). &0 < c /\ ~(y = vec 0)
     ==> mpullback (stds_iota c) (cylinder_flow (&0)) y = cylinder_flow (&0) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stds_iota c = (\x:real^3. c % x) o (\z:real^3. inv(norm z pow 2) % z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; stds_iota; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. inv(norm z pow 2) % z`; `\x:real^3. c % x`;
                 `cylinder_flow (&0)`; `y:real^3`] APX_MPULLBACK_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[RFB_INVERSION_HAS_DERIVATIVE];
      MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (\z:real^3. inv(norm z pow 2) % z) (cylinder_flow (&0)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN BETA_TAC THEN
    MATCH_MP_TAC APX_CYL0_DILATION THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0] THEN
    ARITH_TAC;
    MATCH_MP_TAC APX_INVERSION_CYL0 THEN ASM_REWRITE_TAC[]]);;

let STDS_FAR_CYL = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0 /\ A0 < p3_std_dist g0 x
     ==> g0 x = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) x`,
  REWRITE_TAC[p3_std_initial] THEN MESON_TAC[]);;

let STDS_REFL_ISOM = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ A0 < R /\ x IN stds_neck g0 A0 R
     ==> mpullback (stds_refl g0 A0 R) g0 x = g0 x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_NECK_NZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_REFL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 (x:real^3) /\
                A0 < p3_std_dist g0 (stds_refl g0 A0 R x)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN stds_neck g0 A0 R` THEN
    UNDISCH_TAC `stds_refl g0 A0 R (x:real^3) IN stds_neck g0 A0 R` THEN
    REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(stds_neck g0 A0 R) /\ smooth_map_on (stds_neck g0 A0 R) (stds_refl g0 A0 R)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[STDS_NECK_OPEN; STDS_REFL_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> p3_std_nc g0 A0 differentiable (at z)`
  (LABEL_TAC "DNC") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> stds_iota (stds_cr A0 R) differentiable (at z)`
  (LABEL_TAC "DIO") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; STDS_IOTA_SMOOTH; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (stds_refl g0 A0 R)
                (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN MATCH_MP_TAC STDS_FAR_CYL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`stds_refl g0 A0 R`; `p3_std_nc g0 A0`; `cylinder_flow (&0)`; `x:real^3`]
    APX_MPULLBACK_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `stds_neck g0 A0 R` THEN ASM_REWRITE_TAC[];
      USE_THEN "DNC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (stds_iota (stds_cr A0 R) o p3_std_nc g0 A0) (cylinder_flow (&0)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[stds_refl; o_THM] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                   `stds_iota (stds_cr A0 R) (p3_std_nc g0 A0 w)`] P3S_NCINV_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDS_IOTA_NC_DOM THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3_std_nc g0 A0`; `stds_iota (stds_cr A0 R)`; `cylinder_flow (&0)`;
                 `x:real^3`] APX_MPULLBACK_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "DNC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "DIO" MATCH_MP_TAC THEN MATCH_MP_TAC STDS_NC_NZ THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) x` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN MATCH_MP_TAC STDS_IOTA_CYL0 THEN
    REWRITE_TAC[stds_cr; REAL_EXP_POS_LT] THEN MATCH_MP_TAC STDS_NC_NZ THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_FAR_CYL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The radial reparametrization k of the chart domain                       *)
(* {d < 2R - A0} onto the ball of radius exp(R - A0): k(x) = kap(d x) x/|x|,  *)
(* with kap linear on [0,A0] and kap(s) = exp(s - R) beyond A0, so that     *)
(* k o stds_refl = inversion o k on the neck.  k is a homeomorphism (only   *)
(* continuity is needed: the charts of the double are k^-1 o stereo, and    *)
(* their transition maps are the identity and the reflection).             *)
(* ------------------------------------------------------------------------- *)

let stds_mu = new_definition
 `stds_mu (g0:real^3->real^3^3) (A0:real) (R:real) = exp(A0 - R) / p3s_rad_rinv g0 A0`;;

let stds_kap = new_definition
 `stds_kap (g0:real^3->real^3^3) (A0:real) (R:real) (s:real) =
    stds_mu g0 A0 R * p3s_rad_rinv g0 (min s A0) * exp(max s A0 - A0)`;;

let stds_kapinv = new_definition
 `stds_kapinv (g0:real^3->real^3^3) (A0:real) (R:real) (u:real) =
    p3s_rad_rho g0 (min u (exp(A0 - R)) / stds_mu g0 A0 R) +
    log(max u (exp(A0 - R)) / exp(A0 - R))`;;

let stds_k = new_definition
 `stds_k (g0:real^3->real^3^3) (A0:real) (R:real) (x:real^3) =
    (stds_kap g0 A0 R (p3_std_dist g0 x) * inv(norm x)) % x`;;

let stds_kinv = new_definition
 `stds_kinv (g0:real^3->real^3^3) (A0:real) (R:real) (y:real^3) =
    (p3s_rad_rinv g0 (stds_kapinv g0 A0 R (norm y)) * inv(norm y)) % y`;;

let stds_dom = new_definition
 `stds_dom (g0:real^3->real^3^3) (A0:real) (R:real) =
    {x:real^3 | p3_std_dist g0 x < &2 * R - A0}`;;

(* Facts on rho and its inverse used below.                                  *)

let STDS_RINV_MONO = prove
 (`!g0 A0 s t. p3_std_initial g0 A0 /\ &0 <= s /\ s < t
     ==> p3s_rad_rinv g0 s < p3s_rad_rinv g0 t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`;
                 `p3s_rad_rinv g0 t`] P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let STDS_RINV_0 = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> p3s_rad_rinv g0 (&0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P3S_RHO_0]);;

let STDS_MU_POS = prove
 (`!g0 A0 R. p3_std_initial g0 A0 ==> &0 < stds_mu g0 A0 R`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_mu] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN MATCH_MP_TAC P3S_RINV_POS THEN
  EXISTS_TAC `A0:real` THEN ASM_MESON_TAC[P3S_A0_POS]);;

let STDS_KAP_LOW = prove
 (`!g0 A0 R s. p3_std_initial g0 A0 /\ s <= A0
     ==> stds_kap g0 A0 R s = stds_mu g0 A0 R * p3s_rad_rinv g0 s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_kap] THEN
  SUBGOAL_THEN `min s A0 = s /\ max s A0 = A0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_EXP_0; REAL_MUL_RID]]);;

let STDS_KAP_HIGH = prove
 (`!g0 A0 R s. p3_std_initial g0 A0 /\ A0 <= s ==> stds_kap g0 A0 R s = exp(s - R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_kap; stds_mu] THEN
  SUBGOAL_THEN `min s A0 = A0 /\ max s A0 = s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0 < p3s_rad_rinv g0 A0` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_MESON_TAC[P3S_A0_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(s - R) = exp(A0 - R) * exp(s - A0)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < p3s_rad_rinv g0 A0` THEN CONV_TAC REAL_FIELD);;

let STDS_KAPINV_LOW = prove
 (`!g0 A0 R u. u <= exp(A0 - R)
     ==> stds_kapinv g0 A0 R u = p3s_rad_rho g0 (u / stds_mu g0 A0 R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_kapinv] THEN
  SUBGOAL_THEN `min u (exp(A0 - R)) = u /\ max u (exp(A0 - R)) = exp(A0 - R)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SIMP_TAC[REAL_DIV_REFL; REAL_EXP_NZ; LOG_1; REAL_ADD_RID]);;

let STDS_KAPINV_HIGH = prove
 (`!g0 A0 R u. p3_std_initial g0 A0 /\ exp(A0 - R) <= u
     ==> stds_kapinv g0 A0 R u = R + log u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_kapinv] THEN
  SUBGOAL_THEN `min u (exp(A0 - R)) = exp(A0 - R) /\ max u (exp(A0 - R)) = u`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(A0 - R)` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3s_rad_rinv g0 A0` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_MESON_TAC[P3S_A0_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(A0 - R) / stds_mu g0 A0 R = p3s_rad_rinv g0 A0` SUBST1_TAC THENL
   [REWRITE_TAC[stds_mu] THEN MP_TAC(SPEC `A0 - R` REAL_EXP_POS_LT) THEN
    UNDISCH_TAC `&0 < p3s_rad_rinv g0 A0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`] P3S_RINV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[P3S_A0_POS; REAL_LT_IMP_LE]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_EXP_POS_LT; LOG_EXP] THEN REAL_ARITH_TAC);;

let STDS_KAP_FACTS = prove
 (`!g0 A0 R s. p3_std_initial g0 A0 /\ &0 <= s
     ==> &0 <= stds_kap g0 A0 R s /\ (&0 < s ==> &0 < stds_kap g0 A0 R s) /\
         stds_kapinv g0 A0 R (stds_kap g0 A0 R s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_MU_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s <= A0` THENL
   [ASM_SIMP_TAC[STDS_KAP_LOW] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p3s_rad_rinv g0 s <= p3s_rad_rinv g0 A0` ASSUME_TAC THENL
     [ASM_CASES_TAC `s:real = A0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STDS_RINV_MONO THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `stds_mu g0 A0 R * p3s_rad_rinv g0 s <= exp(A0 - R)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `stds_mu g0 A0 R * p3s_rad_rinv g0 A0` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[stds_mu] THEN
        SUBGOAL_THEN `&0 < p3s_rad_rinv g0 A0` MP_TAC THENL
         [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
          DISCH_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < p3s_rad_rinv g0 A0` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_KAPINV_LOW] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(stds_mu g0 A0 R * p3s_rad_rinv g0 s) / stds_mu g0 A0 R =
                    p3s_rad_rinv g0 s` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < stds_mu g0 A0 R` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN `A0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_KAP_HIGH; REAL_EXP_POS_LE; REAL_EXP_POS_LT] THEN
    SUBGOAL_THEN `exp(A0 - R) <= exp(s - R)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[STDS_KAPINV_HIGH; LOG_EXP] THEN REAL_ARITH_TAC]]);;

let STDS_KAPINV_FACTS = prove
 (`!g0 A0 R u. p3_std_initial g0 A0 /\ &0 <= u
     ==> &0 <= stds_kapinv g0 A0 R u /\ (&0 < u ==> &0 < stds_kapinv g0 A0 R u) /\
         stds_kap g0 A0 R (stds_kapinv g0 A0 R u) = u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_MU_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `u <= exp(A0 - R)` THENL
   [ASM_SIMP_TAC[STDS_KAPINV_LOW] THEN
    SUBGOAL_THEN `&0 <= u / stds_mu g0 A0 R` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `u / stds_mu g0 A0 R <= p3s_rad_rinv g0 A0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN UNDISCH_TAC `u <= exp(A0 - R)` THEN
      REWRITE_TAC[stds_mu] THEN
      SUBGOAL_THEN `&0 < p3s_rad_rinv g0 A0` MP_TAC THENL
       [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    SUBGOAL_THEN `p3s_rad_rho g0 (u / stds_mu g0 A0 R) <= A0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`] P3S_RINV) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC RAND_CONV
        [SYM(ASSUME `p3s_rad_rho g0 (p3s_rad_rinv g0 A0) = A0`)] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `u / stds_mu g0 A0 R`;
                     `p3s_rad_rinv g0 A0`] P3S_RHO_LT_EQ) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_KAP_LOW] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RHO_POS_LE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC P3S_RHO_POS THEN EXISTS_TAC `A0:real` THEN
      ASM_SIMP_TAC[REAL_LT_DIV];
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `u / stds_mu g0 A0 R`]
        P3S_RINV_UNIQUE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < stds_mu g0 A0 R` THEN CONV_TAC REAL_FIELD];
    SUBGOAL_THEN `exp(A0 - R) <= u /\ &0 < u` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `A0 - R` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_KAPINV_HIGH] THEN
    SUBGOAL_THEN `A0 <= R + log u` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`exp(A0 - R)`; `u:real`] LOG_MONO_LE_IMP) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[STDS_KAP_HIGH] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      TRY DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `(R + l) - R = l`] THEN ASM_SIMP_TAC[EXP_LOG]]]);;

(* kap is strictly increasing on [0,inf), and kap(2R - s) kap(s) = 1 on the  *)
(* neck.                                                                     *)

let STDS_KAP_MONO = prove
 (`!g0 A0 R s t. p3_std_initial g0 A0 /\ &0 <= s /\ s < t
     ==> stds_kap g0 A0 R s < stds_kap g0 A0 R t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `s:real`] STDS_KAP_FACTS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `t:real`] STDS_KAP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `stds_kapinv g0 A0 R (stds_kap g0 A0 R t) <=
                stds_kapinv g0 A0 R (stds_kap g0 A0 R s)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[stds_kapinv] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                   `min (stds_kap g0 A0 R t) (exp(A0 - R)) / stds_mu g0 A0 R`;
                   `min (stds_kap g0 A0 R s) (exp(A0 - R)) / stds_mu g0 A0 R`]
                  P3S_RHO_LT_EQ) THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_MU_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_MIN;
                 REAL_EXP_POS_LE] THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    SIMP_TAC[REAL_LT_DIV; REAL_EXP_POS_LT; REAL_LT_MAX] THEN
    SIMP_TAC[REAL_LE_DIV2_EQ; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

let STDS_KAP_REFL = prove
 (`!g0 A0 R s. p3_std_initial g0 A0 /\ A0 <= s /\ A0 <= &2 * R - s
     ==> stds_kap g0 A0 R (&2 * R - s) = inv(stds_kap g0 A0 R s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STDS_KAP_HIGH; GSYM REAL_EXP_NEG] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* k and kinv are mutually inverse radial maps.                              *)

let STDS_DIR_NORM = prove
 (`!r (x:real^3). &0 <= r /\ ~(x = vec 0) ==> norm((r * inv(norm x)) % x) = r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= r ==> abs r = r`] THEN
  UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let STDS_DIR_DIR = prove
 (`!r (x:real^3). &0 < r /\ ~(x = vec 0)
     ==> inv(norm((r * inv(norm x)) % x)) % ((r * inv(norm x)) % x) = inv(norm x) % x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[STDS_DIR_NORM; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let STDS_K_0 = prove
 (`!g0 A0 R. stds_k g0 A0 R (vec 0) = vec 0 /\ stds_kinv g0 A0 R (vec 0) = vec 0`,
  REWRITE_TAC[stds_k; stds_kinv; VECTOR_MUL_RZERO]);;

let STDS_KINV_FACTS = prove
 (`!g0 A0 R (y:real^3).
     p3_std_initial g0 A0
     ==> p3_std_dist g0 (stds_kinv g0 A0 R y) = stds_kapinv g0 A0 R (norm y) /\
         stds_k g0 A0 R (stds_kinv g0 A0 R y) = y /\
         (~(y = vec 0) ==> ~(stds_kinv g0 A0 R y = vec 0) /\
                           inv(norm(stds_kinv g0 A0 R y)) % stds_kinv g0 A0 R y =
                           inv(norm y) % y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[STDS_K_0; NORM_0] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `&0`] STDS_KAPINV_LOW) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; P3S_RHO_0];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `norm(y:real^3)`] STDS_KAPINV_FACTS) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; NORM_POS_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_kapinv g0 A0 R (norm(y:real^3))`]
    P3S_RINV_POS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_kapinv g0 A0 R (norm(y:real^3))`]
    P3S_RINV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(stds_kinv g0 A0 R y) = p3s_rad_rinv g0 (stds_kapinv g0 A0 R (norm(y:real^3))) /\
    ~(stds_kinv g0 A0 R y = vec 0) /\
    inv(norm(stds_kinv g0 A0 R y)) % stds_kinv g0 A0 R y = inv(norm y) % y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[stds_kinv] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    ASM_SIMP_TAC[STDS_DIR_NORM; STDS_DIR_DIR; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (stds_kinv g0 A0 R y) = stds_kapinv g0 A0 R (norm(y:real^3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_kinv g0 A0 R y`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[stds_k] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stds_kinv; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < p3s_rad_rinv g0 (stds_kapinv g0 A0 R (norm(y:real^3)))` THEN
  UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
  CONV_TAC REAL_FIELD);;

let STDS_K_FACTS = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> norm(stds_k g0 A0 R x) = stds_kap g0 A0 R (p3_std_dist g0 x) /\
         ~(stds_k g0 A0 R x = vec 0) /\
         inv(norm(stds_k g0 A0 R x)) % stds_k g0 A0 R x = inv(norm x) % x /\
         stds_kinv g0 A0 R (stds_k g0 A0 R x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_DIST_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p3_std_dist g0 (x:real^3)`] STDS_KAP_FACTS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `norm(stds_k g0 A0 R x) = stds_kap g0 A0 R (p3_std_dist g0 (x:real^3)) /\
    ~(stds_k g0 A0 R x = vec 0) /\
    inv(norm(stds_k g0 A0 R x)) % stds_k g0 A0 R x = inv(norm x) % x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[stds_k] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    ASM_SIMP_TAC[STDS_DIR_NORM; STDS_DIR_DIR; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[stds_kinv] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[stds_k; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < stds_kap g0 A0 R (p3_std_dist g0 (x:real^3))` THEN
  UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
  CONV_TAC REAL_FIELD);;

let STDS_K_REFL = prove
 (`!g0 A0 R (x:real^3).
     p3_std_initial g0 A0 /\ x IN stds_neck g0 A0 R
     ==> stds_k g0 A0 R (stds_refl g0 A0 R x) =
         inv(norm(stds_k g0 A0 R x) pow 2) % stds_k g0 A0 R x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_NECK_NZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_REFL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 (x:real^3) /\ p3_std_dist g0 x < &2 * R - A0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN stds_neck g0 A0 R` THEN REWRITE_TAC[stds_neck; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. stds_k g0 A0 R z =
                           stds_kap g0 A0 R (p3_std_dist g0 z) % (inv(norm z) % z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[stds_k; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `inv(norm(stds_refl g0 A0 R x)) % stds_refl g0 A0 R x =
                      inv(norm x) % (x:real^3)`;
              ASSUME `p3_std_dist g0 (stds_refl g0 A0 R x) =
                      &2 * R - p3_std_dist g0 (x:real^3)`] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p3_std_dist g0 (x:real^3)`] STDS_KAP_REFL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p3_std_dist g0 (x:real^3)`] STDS_KAP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < stds_kap g0 A0 R (p3_std_dist g0 (x:real^3))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[NORM_MUL; STDS_UNIT_NORM; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < stds_kap g0 A0 R (p3_std_dist g0 (x:real^3))` THEN CONV_TAC REAL_FIELD);;

(* Near the tip, k is the dilation by mu and kinv the dilation by 1/mu.      *)

let STDS_K_NEAR0 = prove
 (`!g0 A0 R (x:real^3). p3_std_initial g0 A0 /\ p3_std_dist g0 x <= A0
     ==> stds_k g0 A0 R x = stds_mu g0 A0 R % x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[STDS_K_0; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[stds_k] THEN ASM_SIMP_TAC[STDS_KAP_LOW] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
  CONV_TAC REAL_FIELD);;

let STDS_KINV_NEAR0 = prove
 (`!g0 A0 R (y:real^3). p3_std_initial g0 A0 /\ norm y <= exp(A0 - R)
     ==> stds_kinv g0 A0 R y = inv(stds_mu g0 A0 R) % y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[STDS_K_0; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_MU_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[stds_kinv] THEN ASM_SIMP_TAC[STDS_KAPINV_LOW] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3) / stds_mu g0 A0 R`]
    P3S_RINV_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
  UNDISCH_TAC `&0 < stds_mu g0 A0 R` THEN CONV_TAC REAL_FIELD);;

(* Continuity.                                                               *)

let STDS_DIST_CONT = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> (lift o p3_std_dist g0) continuous_on (:real^3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`] MFD_DIST_CONTINUOUS_RIGHT) THEN
  ANTS_TAC THENL [REWRITE_TAC[P2C_EUCLID_FACTS] THEN ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; p3_std_dist]);;

let STDS_DIST_CONT_AT = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0 ==> (lift o p3_std_dist g0) continuous at x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o p3_std_dist g0`; `(:real^3)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ASM_MESON_TAC[STDS_DIST_CONT]);;

let STDS_RINV_CONT_AT = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s ==> p3s_rad_rinv g0 real_continuous atreal s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
  REWRITE_TAC[real_differentiable] THEN ASM_MESON_TAC[P3S_RINV_DERIV]);;

let STDS_RHO_CONT_AT = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r ==> p3s_rad_rho g0 real_continuous atreal r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
  REWRITE_TAC[real_differentiable] THEN ASM_MESON_TAC[P3S_RHO_DERIV]);;

let STDS_KAP_CONT_AT = prove
 (`!g0 A0 R s. p3_std_initial g0 A0 /\ &0 < s
     ==> stds_kap g0 A0 R real_continuous atreal s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `stds_kap g0 A0 R =
    (\s. stds_mu g0 A0 R *
         (p3s_rad_rinv g0 o (\s. min s A0)) s * (exp o (\s. max s A0 - A0)) s)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_kap; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN
  REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    BETA_TAC THEN MATCH_MP_TAC STDS_RINV_CONT_AT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    REWRITE_TAC[REAL_CONTINUOUS_AT_EXP]]);;

let STDS_KAPINV_CONT_AT = prove
 (`!g0 A0 R u. p3_std_initial g0 A0 /\ &0 < u
     ==> stds_kapinv g0 A0 R real_continuous atreal u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_MU_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `stds_kapinv g0 A0 R =
    (\u. (p3s_rad_rho g0 o (\u. inv(stds_mu g0 A0 R) * min u (exp(A0 - R)))) u +
         (log o (\u. inv(exp(A0 - R)) * max u (exp(A0 - R)))) u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; stds_kapinv; o_THM; real_div] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN REWRITE_TAC[ETA_AX] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    BETA_TAC THEN MATCH_MP_TAC STDS_RHO_CONT_AT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_MIN; REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    BETA_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_AT_LOG THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_EXP_POS_LT; REAL_LT_MAX]]);;

let STDS_K_CONT_AT = prove
 (`!g0 A0 R (x:real^3). p3_std_initial g0 A0 ==> stds_k g0 A0 R continuous at x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `p3_std_dist g0 (x:real^3) < A0` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\z:real^3. stds_mu g0 A0 R % z` THEN
    EXISTS_TAC `p3s_rad_rinv g0 A0 - norm(x:real^3)` THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`; `x:real^3`]
      STDS_DIST_LT_EQ) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC STDS_K_NEAR0 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`; `z:real^3`]
        STDS_DIST_LT_EQ) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(K ALL_TAC) THEN
      UNDISCH_TAC `dist(z:real^3,x) < p3s_rad_rinv g0 A0 - norm x` THEN
      REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[CONTINUOUS_AT_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(p3_std_dist g0 (x:real^3) < A0)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `stds_k g0 A0 R =
                (\z:real^3. (\z. stds_kap g0 A0 R (p3_std_dist g0 z) * inv(norm z)) z % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_k]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
  SUBGOAL_THEN `lift o (\z:real^3. stds_kap g0 A0 R (p3_std_dist g0 z) * inv(norm z)) =
                (\z. (stds_kap g0 A0 R o p3_std_dist g0) z % (lift o inv o (\z. norm z)) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o stds_kap g0 A0 R o p3_std_dist g0 =
                  (lift o stds_kap g0 A0 R o drop) o (lift o p3_std_dist g0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    REWRITE_TAC[o_THM; GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC STDS_DIST_CONT_AT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_KAP_CONT_AT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_INV THEN
    REWRITE_TAC[NETLIMIT_AT; NORM_EQ_0; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM]]);;

let STDS_KINV_CONT_AT = prove
 (`!g0 A0 R (y:real^3). p3_std_initial g0 A0 ==> stds_kinv g0 A0 R continuous at y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `norm(y:real^3) < exp(A0 - R)` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\z:real^3. inv(stds_mu g0 A0 R) % z` THEN
    EXISTS_TAC `exp(A0 - R) - norm(y:real^3)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_KINV_NEAR0 THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `norm(z - y:real^3) < exp(A0 - R) - norm y` THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[CONTINUOUS_AT_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `A0 - R` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `stds_kinv g0 A0 R =
                (\z:real^3. (\z. p3s_rad_rinv g0 (stds_kapinv g0 A0 R (norm z)) * inv(norm z)) z % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stds_kinv]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
  SUBGOAL_THEN
   `lift o (\z:real^3. p3s_rad_rinv g0 (stds_kapinv g0 A0 R (norm z)) * inv(norm z)) =
    (\z. (p3s_rad_rinv g0 o stds_kapinv g0 A0 R o (\z. norm z)) z %
         (lift o inv o (\z. norm z)) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o p3s_rad_rinv g0 o stds_kapinv g0 A0 R o (norm:real^3->real) =
                  (lift o (p3s_rad_rinv g0 o stds_kapinv g0 A0 R) o drop) o
                  (lift o (norm:real^3->real))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM] THEN
    REWRITE_TAC[o_THM; GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC STDS_KAPINV_CONT_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_RINV_CONT_AT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `norm(y:real^3)`]
        STDS_KAPINV_FACTS) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC CONTINUOUS_INV THEN
    REWRITE_TAC[NETLIMIT_AT; ETA_AX] THEN
    CONJ_TAC THENL [REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM]; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The double D_R of the ball {d < R} of g0, on the unit sphere              *)
(* of real^4.  Its two charts are k^-1 o stereo3_n and k^-1 o stereo3_s on  *)
(* the parts where the stereographic coordinate is shorter than           *)
(* exp(R - A0); both have image {d < 2R - A0}, and the transition map is    *)
(* the reflection of the neck (the stereographic transition is the         *)
(* inversion, and k o stds_refl = inversion o k).                          *)
(* ------------------------------------------------------------------------- *)

let stds_cdom_n = new_definition
 `stds_cdom_n (A0:real) (R:real) =
    {p:real^4 | p IN sphere(vec 0,&1) DELETE basis 4 /\ norm(stereo3_n p) < exp(R - A0)}`;;

let stds_cdom_s = new_definition
 `stds_cdom_s (A0:real) (R:real) =
    {p:real^4 | p IN sphere(vec 0,&1) DELETE --(basis 4) /\
                norm(stereo3_s p) < exp(R - A0)}`;;

let stds_atlas = new_definition
 `stds_atlas (g0:real^3->real^3^3) (A0:real) (R:real) =
    {(stds_cdom_n A0 R,(\p. stds_kinv g0 A0 R (stereo3_n p))),
     (stds_cdom_s A0 R,(\p. stds_kinv g0 A0 R (stereo3_s p)))}`;;

let STDS_ATLAS_CASES = prove
 (`!g0 A0 R c.
     c IN stds_atlas g0 A0 R <=>
     c = (stds_cdom_n A0 R,(\p. stds_kinv g0 A0 R (stereo3_n p))) \/
     c = (stds_cdom_s A0 R,(\p. stds_kinv g0 A0 R (stereo3_s p)))`,
  REWRITE_TAC[stds_atlas; IN_INSERT; NOT_IN_EMPTY]);;

(* kapinv is strictly increasing on [0,inf); thresholds of the chart        *)
(* domains.                                                                  *)

let STDS_KAPINV_MONO = prove
 (`!g0 A0 R u v. p3_std_initial g0 A0 /\ &0 <= u /\ &0 <= v
     ==> (stds_kapinv g0 A0 R u < stds_kapinv g0 A0 R v <=> u < v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `u:real`] STDS_KAPINV_FACTS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `v:real`] STDS_KAPINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = stds_kapinv g0 A0 R u` THEN ABBREV_TAC `b = stds_kapinv g0 A0 R v` THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `a:real`; `b:real`]
      STDS_KAP_MONO) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `b:real = a` THENL
     [UNDISCH_TAC `u < v` THEN UNDISCH_TAC `stds_kap g0 A0 R a = u` THEN
      UNDISCH_TAC `stds_kap g0 A0 R b = v` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `b:real`; `a:real`]
        STDS_KAP_MONO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]]);;

let STDS_KAPINV_THRESH = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> stds_kapinv g0 A0 R (exp(A0 - R)) = A0 /\
         stds_kapinv g0 A0 R (exp(R - A0)) = &2 * R - A0`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[STDS_KAPINV_HIGH; REAL_LE_REFL; LOG_EXP] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `exp(A0 - R) <= exp(R - A0)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[STDS_KAPINV_HIGH; LOG_EXP] THEN REAL_ARITH_TAC]]);;

let STDS_DOM_EQ = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> stds_dom g0 A0 R = ball(vec 0:real^3,p3s_rad_rinv g0 (&2 * R - A0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; stds_dom; IN_ELIM_THM; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&2 * R - A0`; `x:real^3`]
    STDS_DIST_LT_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let STDS_DOM_OPEN = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R ==> open(stds_dom g0 A0 R)`,
  SIMP_TAC[STDS_DOM_EQ; OPEN_BALL]);;

let STDS_K_BALL = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> (!x. x IN stds_dom g0 A0 R
              ==> stds_k g0 A0 R x IN ball(vec 0,exp(R - A0)) /\
                  stds_kinv g0 A0 R (stds_k g0 A0 R x) = x) /\
         (!y. y IN ball(vec 0,exp(R - A0))
              ==> stds_kinv g0 A0 R y IN stds_dom g0 A0 R /\
                  stds_k g0 A0 R (stds_kinv g0 A0 R y) = y) /\
         IMAGE (stds_k g0 A0 R) (stds_dom g0 A0 R) = ball(vec 0,exp(R - A0)) /\
         IMAGE (stds_kinv g0 A0 R) (ball(vec 0,exp(R - A0))) = stds_dom g0 A0 R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_KAPINV_THRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN stds_dom g0 A0 R
                ==> stds_k g0 A0 R x IN ball(vec 0,exp(R - A0)) /\
                    stds_kinv g0 A0 R (stds_k g0 A0 R x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[stds_dom; IN_ELIM_THM; IN_BALL_0] THEN
    DISCH_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[STDS_K_0; NORM_0; REAL_EXP_POS_LT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_K_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `exp(R - A0) = stds_kap g0 A0 R (&2 * R - A0)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `&2 * R - A0`] STDS_KAP_HIGH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC STDS_KAP_MONO THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P3S_RHO_POS_LE THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN ball(vec 0,exp(R - A0))
                ==> stds_kinv g0 A0 R y IN stds_dom g0 A0 R /\
                    stds_k g0 A0 R (stds_kinv g0 A0 R y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `y:real^3`] STDS_KINV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[stds_dom; IN_ELIM_THM] THEN
    GEN_REWRITE_TAC RAND_CONV
      [SYM(ASSUME `stds_kapinv g0 A0 R (exp(R - A0)) = &2 * R - A0`)] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `norm(y:real^3)`; `exp(R - A0)`] STDS_KAPINV_MONO) THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

let STDS_K_HOMEO = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> homeomorphism (stds_dom g0 A0 R,ball(vec 0,exp(R - A0)))
                       (stds_k g0 A0 R,stds_kinv g0 A0 R)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_K_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[homeomorphism] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[STDS_K_CONT_AT; STDS_KINV_CONT_AT]);;

(* The two stereographic chart domains.                                      *)

let STDS_CDOM_N_EQ = prove
 (`!A0 R. stds_cdom_n A0 R = IMAGE stereo3_n_inv (ball(vec 0,exp(R - A0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; stds_cdom_n; IN_ELIM_THM; IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `p:real^4` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `stereo3_n p` THEN ASM_SIMP_TAC[STEX_STEREO3_N_LEFT];
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[STEX_STEREO3_N_INV_IN; STEX_STEREO3_N_RIGHT]]);;

let STDS_CDOM_S_EQ = prove
 (`!A0 R. stds_cdom_s A0 R = IMAGE stereo3_s_inv (ball(vec 0,exp(R - A0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; stds_cdom_s; IN_ELIM_THM; IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `p:real^4` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `stereo3_s p` THEN ASM_SIMP_TAC[STEX_STEREO3_S_LEFT];
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[STEX_STEREO3_S_INV_IN; STEX_STEREO3_S_RIGHT]]);;

let STDS_STEREO_N_HOMEO = prove
 (`!A0 R. homeomorphism (stds_cdom_n A0 R,ball(vec 0,exp(R - A0))) (stereo3_n,stereo3_n_inv)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^4,&1) DELETE basis 4`; `(:real^3)`] THEN
  REWRITE_TAC[STEX_STEREO3_HOMEOMORPHISMS; SUBSET_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; stds_cdom_n; IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[STDS_CDOM_N_EQ; GSYM IMAGE_o] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_I] THEN MATCH_MP_TAC IMAGE_EQ THEN
    SIMP_TAC[o_THM; I_THM; STEX_STEREO3_N_RIGHT]]);;

let STDS_STEREO_S_HOMEO = prove
 (`!A0 R. homeomorphism (stds_cdom_s A0 R,ball(vec 0,exp(R - A0))) (stereo3_s,stereo3_s_inv)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `(:real^3)`] THEN
  REWRITE_TAC[STEX_STEREO3_HOMEOMORPHISMS; SUBSET_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; stds_cdom_s; IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[STDS_CDOM_S_EQ; GSYM IMAGE_o] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_I] THEN MATCH_MP_TAC IMAGE_EQ THEN
    SIMP_TAC[o_THM; I_THM; STEX_STEREO3_S_RIGHT]]);;

let STDS_CDOM_OPEN = prove
 (`!A0 R. open_in (subtopology euclidean (sphere(vec 0:real^4,&1))) (stds_cdom_n A0 R) /\
          open_in (subtopology euclidean (sphere(vec 0:real^4,&1))) (stds_cdom_s A0 R)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THENL
   [EXISTS_TAC `sphere(vec 0:real^4,&1) DELETE basis 4`;
    EXISTS_TAC `sphere(vec 0:real^4,&1) DELETE --(basis 4)`] THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     ONCE_REWRITE_TAC[SET_RULE `(s:real^4->bool) DELETE a = s INTER ((:real^4) DELETE a)`] THEN
     MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_DELETE THEN
     REWRITE_TAC[OPEN_UNIV]]) THENL
   [REWRITE_TAC[STDS_CDOM_N_EQ] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    EXISTS_TAC `stereo3_n` THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN REWRITE_TAC[STEX_STEREO3_HOMEOMORPHISMS];
    REWRITE_TAC[STDS_CDOM_S_EQ] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    EXISTS_TAC `stereo3_s` THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN REWRITE_TAC[STEX_STEREO3_HOMEOMORPHISMS]]);;

let STDS_CHART_HOMEO = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> homeomorphism (stds_cdom_n A0 R,stds_dom g0 A0 R)
                       ((\p. stds_kinv g0 A0 R (stereo3_n p)),stereo3_n_inv o stds_k g0 A0 R) /\
         homeomorphism (stds_cdom_s A0 R,stds_dom g0 A0 R)
                       ((\p. stds_kinv g0 A0 R (stereo3_s p)),stereo3_s_inv o stds_k g0 A0 R)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF] `stds_kinv g0 A0 R o stereo3_n`);
              GSYM(REWRITE_CONV[o_DEF] `stds_kinv g0 A0 R o stereo3_s`)] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `ball(vec 0:real^3,exp(R - A0))` THEN
  REWRITE_TAC[STDS_STEREO_N_HOMEO; STDS_STEREO_S_HOMEO] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_SIMP_TAC[STDS_K_HOMEO]);;

(* Transition maps: on the overlap of the two chart domains the chart        *)
(* values are exchanged by the reflection.                                   *)

let STDS_TRANS = prove
 (`!g0 A0 R p. p3_std_initial g0 A0 /\ A0 < R /\
               p IN stds_cdom_n A0 R /\ p IN stds_cdom_s A0 R
     ==> stds_kinv g0 A0 R (stereo3_n p) IN stds_neck g0 A0 R /\
         stds_kinv g0 A0 R (stereo3_s p) IN stds_neck g0 A0 R /\
         stds_kinv g0 A0 R (stereo3_s p) =
           stds_refl g0 A0 R (stds_kinv g0 A0 R (stereo3_n p)) /\
         stds_kinv g0 A0 R (stereo3_n p) =
           stds_refl g0 A0 R (stds_kinv g0 A0 R (stereo3_s p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  UNDISCH_TAC `(p:real^4) IN stds_cdom_n A0 R` THEN
  UNDISCH_TAC `(p:real^4) IN stds_cdom_s A0 R` THEN
  REWRITE_TAC[stds_cdom_n; stds_cdom_s; IN_ELIM_THM] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(SPEC `p:real^4` RFB_SPHERE3_TRANS_NS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y = stereo3_n p` THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(stereo3_s p) = inv(norm(y:real^3))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(A0 - R) < norm(y:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(stereo3_s p) < exp(R - A0)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `exp(A0 - R) = inv(exp(R - A0))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_KAPINV_THRESH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `y:real^3`] STDS_KINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_kinv g0 A0 R y IN stds_neck g0 A0 R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[stds_neck; IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV
        [SYM(ASSUME `stds_kapinv g0 A0 R (exp(A0 - R)) = A0`)] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `exp(A0 - R)`;
                     `norm(y:real^3)`] STDS_KAPINV_MONO);
      GEN_REWRITE_TAC RAND_CONV
        [SYM(ASSUME `stds_kapinv g0 A0 R (exp(R - A0)) = &2 * R - A0`)] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `norm(y:real^3)`;
                     `exp(R - A0)`] STDS_KAPINV_MONO)] THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE; NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_kinv g0 A0 R y`]
    STDS_REFL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_kinv g0 A0 R y`]
    STDS_K_REFL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`;
                 `stds_refl g0 A0 R (stds_kinv g0 A0 R y)`] STDS_K_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_kinv g0 A0 R (stereo3_s p) = stds_refl g0 A0 R (stds_kinv g0 A0 R y)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC LAND_CONV
      [SYM(ASSUME `stds_kinv g0 A0 R (stds_k g0 A0 R (stds_refl g0 A0 R (stds_kinv g0 A0 R y))) =
                   stds_refl g0 A0 R (stds_kinv g0 A0 R y)`)] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The atlas of the double is smooth.                                        *)

let STDS_COVER = prove
 (`!A0 R p. A0 < R /\ p IN sphere(vec 0:real^4,&1)
            ==> p IN stds_cdom_n A0 R \/ p IN stds_cdom_s A0 R`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_cdom_n; stds_cdom_s; IN_ELIM_THM; IN_DELETE] THEN
  SUBGOAL_THEN `&1 < exp(R - A0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p = basis 4:real^4` THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `basis 4:real^4` (CONJUNCT2 STEX_STEREO3_ZERO)) THEN
    SUBGOAL_THEN `~(basis 4:real^4 = --(basis 4))` ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_4; ARITH];
      ALL_TAC] THEN
    UNDISCH_TAC `(p:real^4) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; REAL_EXP_POS_LT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = --(basis 4):real^4` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `--(basis 4):real^4` (CONJUNCT1 STEX_STEREO3_ZERO)) THEN
    SUBGOAL_THEN `~(--(basis 4):real^4 = basis 4)` ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `--x:real^N = x <=> x = vec 0`] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_4; ARITH];
      ALL_TAC] THEN
    UNDISCH_TAC `(p:real^4) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `norm(stereo3_n p) < exp(R - A0)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `p:real^4` RFB_SPHERE3_TRANS_NS) THEN ASM_REWRITE_TAC[IN_DELETE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(stereo3_n p)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(stereo3_n p) pow 2) * norm(stereo3_n p) = inv(norm(stereo3_n p))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(stereo3_n p)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC);;

let STDS_HOMEO_MAP = prove
 (`!(f:real^4->real^3) g s t.
     homeomorphism (s,t) (f,g)
     ==> homeomorphic_map (subtopology euclidean s,subtopology euclidean t) f /\
         IMAGE f s = t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY; HOMEOMORPHIC_MAPS_MAP];
    ASM_MESON_TAC[homeomorphism]]);;

let STDS_CDOM_SUBSET = prove
 (`!A0 R. stds_cdom_n A0 R SUBSET sphere(vec 0:real^4,&1) /\
          stds_cdom_s A0 R SUBSET sphere(vec 0:real^4,&1)`,
  REWRITE_TAC[stds_cdom_n; stds_cdom_s; SUBSET; IN_ELIM_THM; IN_DELETE] THEN SIMP_TAC[]);;

let STDS_ATLAS_SMOOTH = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^4,&1)))
                               (stds_atlas g0 A0 R)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP STDS_HOMEO_MAP)) THEN
  REWRITE_TAC[smooth_manifold_atlas; STDS_ATLAS_CASES; PAIR_EQ;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[STDS_CDOM_OPEN; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MP_TAC(SPECL [`A0:real`; `R:real`] STDS_CDOM_SUBSET) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (SET_RULE
      `(s:real^4->bool) SUBSET t /\ s' SUBSET t ==> t INTER s = s /\ t INTER s' = s'`) th]) THEN
    ASM_SIMP_TAC[STDS_DOM_OPEN];
    X_GEN_TAC `p:real^4` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`A0:real`; `R:real`; `p:real^4`] STDS_COVER) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST [EXISTS_TAC `\x:real^3. x` THEN REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN NO_TAC;
           EXISTS_TAC `stds_refl g0 A0 R` THEN CONJ_TAC THENL
            [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
             ASM_SIMP_TAC[STDS_REFL_SMOOTH] THEN
             REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN
             MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^4`]
               STDS_TRANS) THEN
             ASM_REWRITE_TAC[] THEN MESON_TAC[];
             REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
             MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^4`]
               STDS_TRANS) THEN
             ASM_REWRITE_TAC[] THEN MESON_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The metric of the double, g0 in the coordinates of the                   *)
(* chart chosen at each point (the pattern of round3_metric).  Both local   *)
(* expressions are g0, since the transition map is a g0-isometry; hence    *)
(* the double is a smooth compact Riemannian 3-manifold whose sectional     *)
(* curvatures are those of g0 at the chart points.                         *)
(* ------------------------------------------------------------------------- *)

let stds_dmetric = new_definition
 `stds_dmetric (g0:real^3->real^3^3) (A0:real) (R:real) (p:real^4) =
    g0(SND(chart_at (stds_atlas g0 A0 R) p) p)`;;

(* The overlap of the two chart domains is the neck in both charts, and the *)
(* chart transitions are the reflection there.                              *)

let STDS_OVERLAP_N = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> IMAGE (\p. stds_kinv g0 A0 R (stereo3_n p))
               (stds_cdom_n A0 R INTER stds_cdom_s A0 R) = stds_neck g0 A0 R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^4`] STDS_TRANS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_NECK_NZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 (x:real^3) /\ p3_std_dist g0 x < &2 * R - A0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN stds_neck g0 A0 R` THEN REWRITE_TAC[stds_neck; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_K_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[stds_dom; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^3`] STDS_K_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `stereo3_n_inv(stds_k g0 A0 R x)` THEN
  REWRITE_TAC[STEX_STEREO3_N_RIGHT] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `stds_k g0 A0 R x IN ball(vec 0,exp(R - A0))` MP_TAC THENL
   [ASM_SIMP_TAC[]; REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC] THEN
  REWRITE_TAC[stds_cdom_n; stds_cdom_s; IN_ELIM_THM; STEX_STEREO3_N_INV_IN;
              STEX_STEREO3_N_RIGHT] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `stds_k g0 A0 R x` STEX_STEREO3_N_INV_IN) THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(stereo3_n_inv(stds_k g0 A0 R x) = --(basis 4))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPEC `stereo3_n_inv(stds_k g0 A0 R x)` (CONJUNCT1 STEX_STEREO3_ZERO)) THEN
    ASM_REWRITE_TAC[IN_DELETE; STEX_STEREO3_N_RIGHT];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `exp(A0 - R) < stds_kap g0 A0 R (p3_std_dist g0 (x:real^3)) /\
                &0 < stds_kap g0 A0 R (p3_std_dist g0 x)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p3_std_dist g0 (x:real^3)`]
      STDS_KAP_HIGH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `stereo3_n_inv(stds_k g0 A0 R x)` RFB_SPHERE3_TRANS_NS) THEN
  ASM_REWRITE_TAC[IN_DELETE; STEX_STEREO3_N_RIGHT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  SUBGOAL_THEN `inv(stds_kap g0 A0 R (p3_std_dist g0 (x:real^3)) pow 2) *
                stds_kap g0 A0 R (p3_std_dist g0 x) =
                inv(stds_kap g0 A0 R (p3_std_dist g0 x))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < stds_kap g0 A0 R (p3_std_dist g0 (x:real^3))` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(R - A0) = inv(exp(A0 - R))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

let STDS_REFL_IMAGE = prove
 (`!g0 A0 R. p3_std_initial g0 A0
     ==> IMAGE (stds_refl g0 A0 R) (stds_neck g0 A0 R) = stds_neck g0 A0 R`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[STDS_REFL_PROPS];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `stds_refl g0 A0 R x` THEN ASM_MESON_TAC[STDS_REFL_PROPS]]);;

let STDS_OVERLAP_S = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> IMAGE (\p. stds_kinv g0 A0 R (stereo3_s p))
               (stds_cdom_n A0 R INTER stds_cdom_s A0 R) = stds_neck g0 A0 R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\p. stds_kinv g0 A0 R (stereo3_s p))
                      (stds_cdom_n A0 R INTER stds_cdom_s A0 R) =
                IMAGE (stds_refl g0 A0 R)
                  (IMAGE (\p. stds_kinv g0 A0 R (stereo3_n p))
                         (stds_cdom_n A0 R INTER stds_cdom_s A0 R))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[IN_INTER; o_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `x:real^4`] STDS_TRANS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ASM_SIMP_TAC[STDS_OVERLAP_N; STDS_REFL_IMAGE]]);;

(* Chart images, chart inverses and transitions of the double.               *)

let STDS_CHART_IMAGE = prove
 (`!g0 A0 R c. p3_std_initial g0 A0 /\ A0 < R /\ c IN stds_atlas g0 A0 R
     ==> IMAGE (SND c) (FST c) = stds_dom g0 A0 R /\
         FST c SUBSET sphere(vec 0:real^4,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP STDS_HOMEO_MAP)) THEN
  UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN stds_atlas g0 A0 R` THEN
  REWRITE_TAC[STDS_ATLAS_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[STDS_CDOM_SUBSET]);;

let STDS_CHART_TRANS = prove
 (`!g0 A0 R c c'. p3_std_initial g0 A0 /\ A0 < R /\
                  c IN stds_atlas g0 A0 R /\ c' IN stds_atlas g0 A0 R /\ ~(c = c')
     ==> IMAGE (SND c) (FST c INTER FST c') = stds_neck g0 A0 R /\
         (!y. y IN stds_neck g0 A0 R ==> chart_trans c c' y = stds_refl g0 A0 R y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (SND (c:(real^4->bool)#(real^4->real^3)))
          (FST c INTER FST (c':(real^4->bool)#(real^4->real^3))) = stds_neck g0 A0 R /\
    (!p. p IN FST c INTER FST c'
         ==> SND c' p = stds_refl g0 A0 R (SND c p))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((c:(real^4->bool)#(real^4->real^3)) = c')` THEN
    UNDISCH_TAC `(c':(real^4->bool)#(real^4->real^3)) IN stds_atlas g0 A0 R` THEN
    UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN stds_atlas g0 A0 R` THEN
    REWRITE_TAC[STDS_ATLAS_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `stds_cdom_s A0 R INTER stds_cdom_n A0 R =
                          stds_cdom_n A0 R INTER stds_cdom_s A0 R`] THEN
    ASM_SIMP_TAC[STDS_OVERLAP_N; STDS_OVERLAP_S] THEN
    REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p:real^4`] STDS_TRANS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. p IN FST c INTER FST (c':(real^4->bool)#(real^4->real^3)) /\
                    SND (c:(real^4->bool)#(real^4->real^3)) p = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN stds_neck g0 A0 R` THEN
    REWRITE_TAC[SYM(ASSUME `IMAGE (SND (c:(real^4->bool)#(real^4->real^3)))
                                  (FST c INTER FST (c':(real^4->bool)#(real^4->real^3))) =
                             stds_neck g0 A0 R`)] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `FST(c:(real^4->bool)#(real^4->real^3))`;
                 `SND(c:(real^4->bool)#(real^4->real^3))`;
                 `FST(c':(real^4->bool)#(real^4->real^3))`;
                 `SND(c':(real^4->bool)#(real^4->real^3))`; `p:real^4`] CHART_TRANS_AT) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The local expressions of the metric of the double are g0.                 *)

let STDS_DMETRIC_LOCAL = prove
 (`!g0 A0 R c y. p3_std_initial g0 A0 /\ A0 < R /\ c IN stds_atlas g0 A0 R /\
                 y IN stds_dom g0 A0 R
     ==> metric_local (stds_atlas g0 A0 R) c (stds_dmetric g0 A0 R) y = g0 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `FST(c:(real^4->bool)#(real^4->real^3))`;
                 `SND(c:(real^4->bool)#(real^4->real^3))`] CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  ABBREV_TAC `q = chart_inv (c:(real^4->bool)#(real^4->real^3)) y` THEN
  SUBGOAL_THEN `(q:real^4) IN FST(c:(real^4->bool)#(real^4->real^3)) /\
                SND(c:(real^4->bool)#(real^4->real^3)) q = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `q:real^4`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[metric_local; stds_dmetric] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `chart_at (stds_atlas g0 A0 R) q = (c:(real^4->bool)#(real^4->real^3))` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `FST(c:(real^4->bool)#(real^4->real^3))`;
                   `SND(c:(real^4->bool)#(real^4->real^3))`; `q:real^4`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID];
    ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (stds_atlas g0 A0 R) q` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`;
                 `c:(real^4->bool)#(real^4->real^3)`; `c':(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_TRANS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN stds_neck g0 A0 R` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `stds_neck g0 A0 R`)) THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `q:real^4` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c':(real^4->bool)#(real^4->real^3)) q = stds_refl g0 A0 R y` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `FST(c:(real^4->bool)#(real^4->real^3))`;
                   `SND(c:(real^4->bool)#(real^4->real^3))`;
                   `FST(c':(real^4->bool)#(real^4->real^3))`;
                   `SND(c':(real^4->bool)#(real^4->real^3))`; `q:real^4`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_jac (c:(real^4->bool)#(real^4->real^3)) c' q =
                frechet_derivative (stds_refl g0 A0 R) (at y)` SUBST1_TAC THENL
   [REWRITE_TAC[chart_jac] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `stds_neck g0 A0 R` THEN ASM_SIMP_TAC[STDS_NECK_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM mpullback] THEN MATCH_MP_TAC STDS_REFL_ISOM THEN ASM_REWRITE_TAC[]);;

let STDS_DMETRIC_RIEM = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> riemannian_metric (stds_atlas g0 A0 R) (stds_dmetric g0 A0 R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `c:(real^4->bool)#(real^4->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN EXISTS_TAC `g0:real^3->real^3^3` THEN
  ASM_SIMP_TAC[STDS_DMETRIC_LOCAL] THEN
  MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
  ASM_SIMP_TAC[STDS_DOM_OPEN; SUBSET_UNIV] THEN ASM_MESON_TAC[P3S_STD_METRIC_FIELD]);;

(* Sectional curvatures of the double are those of g0 at the chart point.    *)

let STDS_DMETRIC_SEC = prove
 (`!g0 A0 R p u v. p3_std_initial g0 A0 /\ A0 < R /\ p IN sphere(vec 0:real^4,&1)
     ==> mfd_sectional (stds_atlas g0 A0 R) (stds_dmetric g0 A0 R) p u v =
         mfd_sectional (open_set_atlas (:real^3)) g0
                       (SND(chart_at (stds_atlas g0 A0 R) p) p) u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `p:real^4`] CHART_AT) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (stds_atlas g0 A0 R) p` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `stds_dom g0 A0 R` THEN
  ASM_SIMP_TAC[STDS_DOM_OPEN; STDS_DMETRIC_LOCAL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `stds_dom g0 A0 R`)) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

(* Curvature bounds of the double from those of g0.                          *)

let STDS_G0_SEC_BOUND = prove
 (`!g0 A0 C0. p3_std_initial g0 A0 /\
     (!x. lrm_deriv_norm2 0 (metric_local (open_set_atlas (:real^3))
                                (chart_at (open_set_atlas (:real^3)) x) g0)
                            (SND(chart_at (open_set_atlas (:real^3)) x) x) <= C0)
     ==> !x u v. ~collinear {vec 0,u,v}
                 ==> abs(mfd_sectional (open_set_atlas (:real^3)) g0 x u v) <= sqrt C0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real^3`; `v:real^3`] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
  SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  DISCH_TAC THEN REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  SUBGOAL_THEN `metric_field (:real^3) (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_STD_METRIC_FIELD]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lrm_deriv_norm2 0 (g0:real^3->real^3^3) x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[IN_UNIV];
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[IN_UNIV]]);;

let STDS_DMETRIC_CURV = prove
 (`!g0 A0 R K p. p3_std_initial g0 A0 /\ A0 < R /\ p IN sphere(vec 0:real^4,&1) /\
     (!x u v. ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional (open_set_atlas (:real^3)) g0 x u v) <= K)
     ==> mfd_rm_norm (stds_atlas g0 A0 R) (stds_dmetric g0 A0 R) p <= K /\
         (!u v. ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (stds_atlas g0 A0 R) (stds_dmetric g0 A0 R) p u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[STDS_DMETRIC_SEC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[STDS_DMETRIC_SEC];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The embedding of the ball {d < 2R - A0} of g0 into the                   *)
(* double, phi = stereo3_n_inv o k (the inverse of the first chart): a      *)
(* diffeomorphism onto its image, under which the metric of the double      *)
(* pulls back to g0 exactly.                                                 *)
(* ------------------------------------------------------------------------- *)

let stds_phi = new_definition
 `stds_phi (g0:real^3->real^3^3) (A0:real) (R:real) (x:real^3) =
    stereo3_n_inv(stds_k g0 A0 R x)`;;

let STDS_CHART_INV_UNIV = prove
 (`!y:real^3. chart_inv ((:real^3),(\x. x)) y = y`,
  REWRITE_TAC[chart_inv; IN_UNIV] THEN MESON_TAC[]);;

let STDS_PHI_FACTS = prove
 (`!g0 A0 R. p3_std_initial g0 A0 /\ A0 < R
     ==> (!x. x IN stds_dom g0 A0 R
              ==> stds_phi g0 A0 R x IN stds_cdom_n A0 R /\
                  stds_kinv g0 A0 R (stereo3_n (stds_phi g0 A0 R x)) = x) /\
         (!x. x IN stds_dom g0 A0 R
              ==> (stds_phi g0 A0 R x IN stds_cdom_s A0 R <=> x IN stds_neck g0 A0 R)) /\
         homeomorphism (stds_dom g0 A0 R,stds_cdom_n A0 R)
                       (stds_phi g0 A0 R,(\p. stds_kinv g0 A0 R (stereo3_n p)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (stds_dom g0 A0 R,stds_cdom_n A0 R)
                  (stds_phi g0 A0 R,(\p. stds_kinv g0 A0 R (stereo3_n p)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `stds_phi g0 A0 R = stereo3_n_inv o stds_k g0 A0 R` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; stds_phi]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!x. x IN stds_dom g0 A0 R
                    ==> stds_phi g0 A0 R x IN stds_cdom_n A0 R /\
                        stds_kinv g0 A0 R (stereo3_n (stds_phi g0 A0 R x)) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!y. y IN stds_dom g0 A0 R
                     ==> (\p. stds_kinv g0 A0 R (stereo3_n p)) (stds_phi g0 A0 R y) = y` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_phi g0 A0 R x`]
      STDS_TRANS) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_OVERLAP_N) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\s:real^3->bool. (x:real^3) IN s`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^4` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `stds_phi g0 A0 R x = p` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    UNDISCH_TAC `!x. x IN stds_cdom_n A0 R
                     ==> stds_phi g0 A0 R ((\p. stds_kinv g0 A0 R (stereo3_n p)) x) = x` THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^4`) THEN ASM_REWRITE_TAC[]]);;

let STDS_PHI_DIFFEO = prove
 (`!g0 A0 R W. p3_std_initial g0 A0 /\ A0 < R /\ open W /\ W SUBSET stds_dom g0 A0 R
     ==> mfd_diffeo euclidean (open_set_atlas (:real^3)) W
                    (subtopology euclidean (sphere(vec 0:real^4,&1))) (stds_atlas g0 A0 R)
                    (IMAGE (stds_phi g0 A0 R) W) (stds_phi g0 A0 R)
                    (\p. stds_kinv g0 A0 R (stereo3_n p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_PHI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (W,IMAGE (stds_phi g0 A0 R) W)
                  (stds_phi g0 A0 R,(\p. stds_kinv g0 A0 R (stereo3_n p)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`stds_dom g0 A0 R`; `stds_cdom_n A0 R`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (stds_phi g0 A0 R) W SUBSET stds_cdom_n A0 R` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_IN];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `stds_cdom_n A0 R` THEN
    REWRITE_TAC[STDS_CDOM_OPEN] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`\p. stds_kinv g0 A0 R (stereo3_n p)`; `stds_dom g0 A0 R`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_SIMP_TAC[STDS_DOM_OPEN];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `sphere(vec 0:real^4,&1) INTER IMAGE (stds_phi g0 A0 R) W =
                  IMAGE (stds_phi g0 A0 R) W` SUBST1_TAC THENL
     [MP_TAC(SPECL [`A0:real`; `R:real`] STDS_CDOM_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY];
    REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES; STDS_ATLAS_CASES] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[STDS_CHART_INV_UNIV; IN_UNIV; INTER_UNIV; o_DEF; IMAGE_ID] THEN
    REWRITE_TAC[ETA_AX; IMAGE_ID] THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. x` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `stds_refl g0 A0 R` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(x:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_phi g0 A0 R x`]
          STDS_TRANS) THEN
        ASM_SIMP_TAC[] THEN MESON_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
        ASM_SIMP_TAC[STDS_REFL_SMOOTH] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(x:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[]]]];
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES; STDS_ATLAS_CASES] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNIV; o_DEF] THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                     `stds_cdom_n A0 R`; `\p. stds_kinv g0 A0 R (stereo3_n p)`] CHART_INV) THEN
      ASM_REWRITE_TAC[STDS_ATLAS_CASES] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^3. y` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_ID; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                     `stds_cdom_s A0 R`; `\p. stds_kinv g0 A0 R (stereo3_s p)`] CHART_INV) THEN
      ASM_REWRITE_TAC[STDS_ATLAS_CASES] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `stds_refl g0 A0 R` THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `p:real^4` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p:real^4`] STDS_TRANS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; MESON_TAC[]];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
        ASM_SIMP_TAC[STDS_REFL_SMOOTH] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `p:real^4` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `p:real^4`] STDS_TRANS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; MESON_TAC[]]]]]);;

let STDS_PHI_PULLBACK = prove
 (`!g0 A0 R (g:real^4->real^3^3) z.
     p3_std_initial g0 A0 /\ A0 < R /\ z IN stds_dom g0 A0 R /\
     (!p. p IN sphere(vec 0,&1) ==> g p = stds_dmetric g0 A0 R p)
     ==> rfs_pullback (stds_atlas g0 A0 R) (stds_phi g0 A0 R) g z = g0 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_ATLAS_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] STDS_PHI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stds_phi g0 A0 R z IN sphere(vec 0:real^4,&1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`A0:real`; `R:real`] STDS_CDOM_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                 `stds_phi g0 A0 R z`] CHART_AT) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_pullback] THEN
  ABBREV_TAC `c = chart_at (stds_atlas g0 A0 R) (stds_phi g0 A0 R z)` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `c:(real^4->bool)#(real^4->real^3)`]
    STDS_CHART_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) g0 z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN
    SUBGOAL_THEN `(SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) z IN
                  stds_dom g0 A0 R` ASSUME_TAC THENL
     [REWRITE_TAC[o_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
                   `c:(real^4->bool)#(real^4->real^3)`; `g:real^4->real^3^3`;
                   `stds_dmetric g0 A0 R`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC
      `(SND(c:(real^4->bool)#(real^4->real^3)) o stds_phi g0 A0 R) z`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC STDS_DMETRIC_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN stds_atlas g0 A0 R` THEN
  REWRITE_TAC[STDS_ATLAS_CASES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (\x:real^3. x) g0 z` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[P2B9_MPULLBACK_ID]] THEN
    MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN
    EXISTS_TAC `stds_dom g0 A0 R` THEN ASM_SIMP_TAC[STDS_DOM_OPEN; o_THM];
    SUBGOAL_THEN `(z:real^3) IN stds_neck g0 A0 R` ASSUME_TAC THENL
     [UNDISCH_TAC `stds_phi g0 A0 R z IN stds_cdom_s A0 R` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (stds_refl g0 A0 R) g0 z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `stds_neck g0 A0 R` THEN
      ASM_SIMP_TAC[STDS_NECK_OPEN; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN stds_dom g0 A0 R` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) IN stds_neck g0 A0 R` THEN
        REWRITE_TAC[stds_neck; stds_dom; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `stds_phi g0 A0 R w IN stds_cdom_n A0 R /\
                    stds_phi g0 A0 R w IN stds_cdom_s A0 R /\
                    stds_kinv g0 A0 R (stereo3_n (stds_phi g0 A0 R w)) = w`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `stds_phi g0 A0 R w`]
        STDS_TRANS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC STDS_REFL_ISOM THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The exhaustion of R^3 by the g0-balls about the tip and the              *)
(* flows on the doubles (PDE_CURVATURE_TIME with a curvature bound K of g0, *)
(* uniform in the doubling radius).                                         *)
(* ------------------------------------------------------------------------- *)

let stds_W = new_definition
 `stds_W (g0:real^3->real^3^3) (m:num) = {x:real^3 | p3_std_dist g0 x < &m + &1}`;;

let STDS_W_BALL = prove
 (`!g0 A0 m. p3_std_initial g0 A0
     ==> stds_W g0 m = ball(vec 0:real^3,p3s_rad_rinv g0 (&m + &1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; stds_W; IN_ELIM_THM; IN_BALL_0] THEN
  X_GEN_TAC `x:real^3` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&m + &1`; `x:real^3`] STDS_DIST_LT_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; SIMP_TAC[]]);;

let STDS_W_FACTS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> (!m. open_in euclidean (stds_W g0 m) /\ vec 0 IN stds_W g0 m /\
              compact_in euclidean (euclidean closure_of stds_W g0 m) /\
              euclidean closure_of stds_W g0 m SUBSET stds_W g0 (SUC m)) /\
         UNIONS {stds_W g0 m | m IN (:num)} = (:real^3) /\
         (!m n. m <= n ==> stds_W g0 m SUBSET stds_W g0 n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m. &0 < p3s_rad_rinv g0 (&m + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> p3s_rad_rinv g0 (&m + &1) <= p3s_rad_rinv g0 (&n + &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:num = n` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STDS_RINV_MONO THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[REAL_LT_RADD; REAL_OF_NUM_LT] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
   [X_GEN_TAC `m:num` THEN REWRITE_TAC[MATCH_MP STDS_W_BALL (ASSUME `p3_std_initial g0 A0`)] THEN
    ASM_SIMP_TAC[GSYM OPEN_IN; OPEN_BALL; CENTRE_IN_BALL; EUCLIDEAN_CLOSURE_OF;
                 CLOSURE_BALL; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `p3s_rad_rinv g0 (&m + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDS_RINV_MONO THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    REWRITE_TAC[MATCH_MP STDS_W_BALL (ASSUME `p3_std_initial g0 A0`)] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    MP_TAC(SPEC `p3_std_dist g0 (x:real^3)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `ball(vec 0:real^3,p3s_rad_rinv g0 (&n + &1))` THEN CONJ_TAC THENL
     [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(MATCH_MP STDS_W_BALL (ASSUME `p3_std_initial g0 A0`))] THEN REWRITE_TAC[stds_W; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[MATCH_MP STDS_W_BALL (ASSUME `p3_std_initial g0 A0`)] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_SIMP_TAC[]]);;

let STDS_DOUBLE_FLOWS = prove
 (`!d:real^4->bool.
     PDE_CURVATURE_TIME_STATEMENT d (:3)
     ==> ?c C. &0 < c /\ &0 < C /\
               !g0 A0 K R.
                 p3_std_initial g0 A0 /\ A0 < R /\ &0 < K /\
                 (!x u v. ~collinear {vec 0,u,v}
                          ==> abs(mfd_sectional (open_set_atlas (:real^3)) g0 x u v) <= K)
                 ==> ?b gf. c / K < b /\
                            ricci_flow_from (subtopology euclidean (sphere(vec 0,&1)),
                                             stds_atlas g0 A0 R) (&0) b gf /\
                            (!p. p IN sphere(vec 0,&1)
                                 ==> gf (&0) p = stds_dmetric g0 A0 R p) /\
                            (!t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
                                   ==> mfd_rm_norm (stds_atlas g0 A0 R) (gf t) p <= C * K)`,
  GEN_TAC THEN REWRITE_TAC[PDE_CURVATURE_TIME_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `K:real`; `R:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `stds_atlas g0 A0 R`;
     `stds_dmetric g0 A0 R`; `&0`; `K:real`]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; REAL_ADD_LID; DIMINDEX_3; ARITH] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[STDS_ATLAS_SMOOTH; STDS_DMETRIC_RIEM] THEN
    REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] POINCARE_SMOOTH_HYPOTHESES_SPHERE_3] THEN
    X_GEN_TAC `p:real^4` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`; `K:real`; `p:real^4`]
      STDS_DMETRIC_CURV) THEN
    ASM_SIMP_TAC[];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A flow on R^3 from g0 with bounded curvature on [0,te) is a               *)
(* partial standard flow (completeness by the uniform equivalence of the    *)
(* metrics under the Ricci bound).                                          *)
(* ------------------------------------------------------------------------- *)

let STDS_PARTIAL_FROM_BOUND = prove
 (`!g0 A0 te (g:real->real^3->real^3^3) M.
     p3_std_initial g0 A0 /\ &0 <= M /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te g /\ g (&0) = g0 /\
     (!s y. &0 <= s /\ s < te ==> mfd_rm_norm (open_set_atlas (:real^3)) (g s) y <= M)
     ==> p3_partial_std g0 te g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[p3_partial_std] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `t1:real` THEN DISCH_TAC THEN EXISTS_TAC `M:real` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RIC"))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < te
                    ==> riemannian_metric (open_set_atlas (:real^3)) ((g:real->real^3->real^3^3) t)`
  (LABEL_TAC "RM") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
     [ASM_MESON_TAC[ricci_flow_from];
      UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te
                     (g:real->real^3->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `te:real`;
                 `g:real->real^3->real^3^3`; `Cr * M`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "RIC" (MP_TAC o ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                     `(g:real->real^3->real^3^3) t`; `x:real^3`; `M:real`;
                                     `v:real^3`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_MUL_ASSOC]] THEN
    ASM_SIMP_TAC[P2C_EUCLID_FACTS; IN_UNIV];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; REAL_SUB_RZERO] THEN
    DISCH_THEN(LABEL_TAC "EQV")] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) g0 /\
                mfd_complete (euclidean,open_set_atlas (:real^3)) g0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MATCH_MP_TAC P2CO_COMPLETE_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `exp(&2 * (Cr * M) * t)`] THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; REAL_EXP_POS_LT; IN_UNIV] THEN
  CONJ_TAC THENL [USE_THEN "RM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN
  USE_THEN "EQV" (MP_TAC o SPECL [`t:real`; `z:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * (Cr * M) * t) *
              (exp(--(&2 * (Cr * M) * t)) * ((v:real^3) dot ((g0:real^3->real^3^3) z ** v)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of Prop 5.14 for the flows of the doubles                  *)
(* D_{R_n}, R_n = A0 + n + 3, based at the first tip at time 0: the views,   *)
(* the exact slice limit at time 0 and the persistence and curvature        *)
(* hypothesis on the regions phi_n(W_m).                                    *)
(* ------------------------------------------------------------------------- *)

let stds_view = new_definition
 `stds_view (g0:real^3->real^3^3) (A0:real) (bf:num->real)
            (gf:num->real->real^4->real^3^3) (n:num) =
    rfs_flow_view (subtopology euclidean (sphere(vec 0:real^4,&1)),
                   stds_atlas g0 A0 (A0 + &n + &3))
                  {s | &0 <= s /\ s < bf n} (gf n)`;;

let STDS_VIEW_PARTS = prove
 (`!g0 A0 bf gf n s.
     rfs_vtop (stds_view g0 A0 bf gf n) s =
       (if &0 <= s /\ s < bf n then subtopology euclidean (sphere(vec 0:real^4,&1))
        else discrete_topology {}) /\
     rfs_vatlas (stds_view g0 A0 bf gf n) s = stds_atlas g0 A0 (A0 + &n + &3) /\
     rfs_vmetric (stds_view g0 A0 bf gf n) s = gf n s`,
  REWRITE_TAC[stds_view; P2CF_FLOW_VIEW_PARTS; IN_ELIM_THM]);;

let STDS_CHART_INV_I = prove
 (`chart_inv ((:real^3),(\x:real^3. x)) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_THM; STDS_CHART_INV_UNIV]);;

(* A compact set lies in one of the balls of the exhaustion.                 *)

let STDS_W_COMPACT = prove
 (`!g0 A0 K. p3_std_initial g0 A0 /\ compact K ==> ?k0. !k. k0 <= k ==> K SUBSET stds_W g0 k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^3->bool`; `vec 0:real^3`] BOUNDED_SUBSET_BALL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `p3s_rad_rho g0 r` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; stds_W; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `p3s_rad_rho g0 r` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `r:real`]
      P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    MP_TAC(SPEC `k:num` REAL_POS) THEN
    UNDISCH_TAC `(k0:num) <= k` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `p3s_rad_rho g0 r <= &k0` THEN REAL_ARITH_TAC]);;

let STDS_W_DOM = prove
 (`!g0 A0 m n. p3_std_initial g0 A0 /\ m <= n
               ==> stds_W g0 m SUBSET stds_dom g0 A0 (A0 + &n + &3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; stds_W; stds_dom; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  UNDISCH_TAC `m:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `&0 < A0` THEN MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC);;

(* The slice limit at time 0 is exact: the embeddings pull the initial       *)
(* metrics of the doubles back to g0 on the exhaustion.                     *)

let STDS_SLICE_LIMIT = prove
 (`!g0 A0 (bf:num->real) (gf:num->real->real^4->real^3^3).
     p3_std_initial g0 A0 /\ (!n. &0 < bf n) /\
     (!n p. p IN sphere(vec 0,&1) ==> gf n (&0) p = stds_dmetric g0 A0 (A0 + &n + &3) p)
     ==> p2c_slice_limit_with (stds_view g0 A0 bf gf)
           (\n. stereo3_n_inv(vec 0)) (\n. &0) (\n. &1)
           (euclidean,open_set_atlas (:real^3)) g0 (vec 0) (stds_W g0)
           (\n. stds_phi g0 A0 (A0 + &n + &3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. A0 < A0 + &n + &3` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_W_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_slice_limit_with; STDS_VIEW_PARTS; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; REAL_LT_01] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[p3_std_initial];
    REWRITE_TAC[stds_phi; STDS_K_0];
    X_GEN_TAC `k:num` THEN EXISTS_TAC `\p. stds_kinv g0 A0 (A0 + &k + &3) (stereo3_n p)` THEN
    MATCH_MP_TAC STDS_PHI_DIFFEO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN]; MATCH_MP_TAC STDS_W_DOM THEN ASM_REWRITE_TAC[LE_REFL]];
    MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `eta:real`] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `K:real^3->bool`] STDS_W_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(K:real^3->bool) SUBSET stds_W g0 k` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN stds_dom g0 A0 (A0 + &k + &3)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `k:num`; `k:num`] STDS_W_DOM) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
    REWRITE_TAC[STDS_CHART_INV_I; I_O_ID; MATRIX_CMUL_LID; ETA_AX] THEN
    MP_TAC(ISPECL [`m:num`; `g0:real^3->real^3^3`; `g0:real^3->real^3^3`;
                   `g0:real^3->real^3^3`;
                   `rfs_pullback (stds_atlas g0 A0 (A0 + &k + &3))
                                 (stds_phi g0 A0 (A0 + &k + &3))
                                 ((gf:num->real->real^4->real^3^3) k (&0))`;
                   `stds_dom g0 A0 (A0 + &k + &3)`; `y:real^3`] LCK_DIST2_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[STDS_DOM_OPEN] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_PHI_PULLBACK THEN ASM_SIMP_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[P2BL_LCK_DIST2_REFL]]]);;

(* The persistence and curvature hypothesis of Prop 5.14 on the regions     *)
(* phi_n(W_m), n >= m, with the constant C K (t_n = 0, Q_n = 1).            *)

let STDS_P514_REGION = prove
 (`!g0 A0 c C K (bf:num->real) (gf:num->real->real^4->real^3^3).
     p3_std_initial g0 A0 /\ (!n. c / K < bf n) /\
     (!n t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
              ==> mfd_rm_norm (stds_atlas g0 A0 (A0 + &n + &3)) (gf n t) p <= C * K)
     ==> !m a b. real_interval[a,b] SUBSET real_interval[&0,c / K]
           ==> ?CM N. !n. N <= n
                 ==> (!s. a <= s /\ s <= b
                          ==> IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m) SUBSET
                              topspace(rfs_vtop (stds_view g0 A0 bf gf n) s)) /\
                     rfs_persists (stds_view g0 A0 bf gf n)
                                  (IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m)) a b /\
                     !s y. a <= s /\ s <= b /\
                           y IN IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m)
                           ==> p3_vrm (stds_view g0 A0 bf gf n) s y <= CM`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> &0 <= s /\ s <= c / K` (LABEL_TAC "ab") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s IN real_interval[&0,c / K]` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`C * K`; `m:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `A0 < A0 + &n + &3` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
                  (IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &n + &3`; `stds_W g0 m`]
      STDS_PHI_DIFFEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_W_FACTS) THEN
        ASM_SIMP_TAC[OPEN_IN];
        MATCH_MP_TAC STDS_W_DOM THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[mfd_diffeo]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m) SUBSET
                sphere(vec 0:real^4,&1)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
     `open_in (subtopology euclidean (sphere(vec 0:real^4,&1)))
              (IMAGE (stds_phi g0 A0 (A0 + &n + &3)) (stds_W g0 m))`)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b
                    ==> rfs_vtop (stds_view g0 A0 bf gf n) s =
                        subtopology euclidean (sphere(vec 0:real^4,&1))` (LABEL_TAC "top") THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[STDS_VIEW_PARTS] THEN
    SUBGOAL_THEN `&0 <= s /\ s < (bf:num->real) n` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. c / K < (bf:num->real) n`)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "top" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= s /\ s <= b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "top" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[STDS_VIEW_PARTS; STDS_ATLAS_SMOOTH];
    REWRITE_TAC[p3_vrm; STDS_VIEW_PARTS] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^4`] THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The curvature of the limit flow: a bound M on |Rm| of the rescaled views  *)
(* passes to the limit (LIM_CURV, via the sectional curvatures).            *)

let STDS_LIM_RM_BOUND = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real) (J:real->bool) (top:B topology)
    (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) (s:real) (y:B) (M:real).
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n. p2c_regular_view (V n)) /\
     s IN J /\ y IN topspace top /\ riemannian_metric atlas (g s) /\
     (!k z. z IN topspace (rfs_vtop (V k) (t k + s / Q k))
            ==> mfd_rm_norm (rfs_vatlas (V k) (t k + s / Q k))
                            (rfs_vmetric (V k) (t k + s / Q k)) z <= M * Q k)
     ==> mfd_rm_norm atlas (g s) y <= M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "rv")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n tau. ~(topspace(rfs_vtop
               ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n) tau) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  (LABEL_TAC "reg") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `tau:real`] THEN DISCH_TAC THEN
    USE_THEN "rv" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k z u v. z IN topspace (rfs_vtop
                ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) (t k + s / Q k)) /\
              ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional (rfs_vatlas (V k) (t k + s / Q k))
                                    (rfs_vmetric (V k) (t k + s / Q k)) z u v / Q k) <= M`
  (LABEL_TAC "vb") THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `z:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "reg" (MP_TAC o SPECL [`k:num`; `(t:num->real) k + s / (Q:num->real) k`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL
     [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) ((t:num->real) k + s / (Q:num->real) k)`;
      `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) k) ((t:num->real) k + s / (Q:num->real) k)`;
      `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) ((t:num->real) k + s / (Q:num->real) k)`;
      `z:A`; `u:real^3`; `v:real^3`] RFA_MFD_SECTIONAL_LE_NORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPECL [`k:num`; `z:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < q ==> abs q = q`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:B)`] LIM_CURV) THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (MP_TAC o SPEC `--M:real`) (MP_TAC o SPEC `M:real`))) THEN
  ANTS_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    USE_THEN "vb" (MP_TAC o SPECL [`k:num`; `z:A`; `u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    USE_THEN "vb" (MP_TAC o SPECL [`k:num`; `z:A`; `u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The existence route.  K bounds |sec g0| (bounded geometry,                *)
(* l = 0); the doubles D_{R_n} carry flows on [0,c/K] with |Rm| <= C K       *)
(* (PDE_CURVATURE_TIME); Prop 5.14 at the first tip with t_n = 0, Q_n = 1    *)
(* gives a limit flow on R^3 from g0 on [0,c/K], with |Rm| <= C K by        *)
(* LIM_CURV; it is a partial standard flow (STDS_PARTIAL_FROM_BOUND).       *)
(* ------------------------------------------------------------------------- *)

let STDS_PARTIAL_EXISTS_ROUTE = prove
 (`!d:real^4->bool. P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT d`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT; P2C_STD_PARTIAL_EXISTS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pde") (CONJUNCTS_THEN2 (LABEL_TAC "p514")
    (CONJUNCTS_THEN2 (LABEL_TAC "freg") (LABEL_TAC "bg")))) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?K. &0 < K /\
                    !x u v. ~collinear {vec 0,u,v}
                            ==> abs(mfd_sectional (open_set_atlas (:real^3)) g0 x u v) <= K`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "bg" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
                   REWRITE_RULE[P2C_STD_BOUNDED_GEOM_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN
    DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
    EXISTS_TAC `max (&1) (sqrt C0)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt C0` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `C0:real`] STDS_G0_SEC_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "pde" (MP_TAC o MATCH_MP STDS_DOUBLE_FLOWS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fl"))))) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. A0 < A0 + &n + &3` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?b (g:real->real^4->real^3^3).
          c / K < b /\
          ricci_flow_from (subtopology euclidean (sphere(vec 0:real^4,&1)),
                           stds_atlas g0 A0 (A0 + &n + &3)) (&0) b g /\
          (!p. p IN sphere(vec 0,&1) ==> g (&0) p = stds_dmetric g0 A0 (A0 + &n + &3) p) /\
          (!t p. &0 <= t /\ t <= c / K /\ p IN sphere(vec 0,&1)
                 ==> mfd_rm_norm (stds_atlas g0 A0 (A0 + &n + &3)) (g t) p <= C * K)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "fl" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `K:real`; `A0 + &n + &3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `bf:num->real`
      (X_CHOOSE_THEN `gf:num->real->real^4->real^3^3` (LABEL_TAC "sk")))] THEN
  SUBGOAL_THEN `&0 < c / K` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (bf:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "p514" (MP_TAC o SPECL
    [`stds_view g0 A0 (bf:num->real) (gf:num->real->real^4->real^3^3)`;
     `\n:num. stereo3_n_inv(vec 0)`; `\n:num. &0`; `\n:num. &1`;
     `real_interval[&0,c / K]`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
     `g0:real^3->real^3^3`; `vec 0:real^3`; `stds_W g0`;
     `\n. stds_phi g0 A0 (A0 + &n + &3)`] o REWRITE_RULE[P2C_PROP_5_14_STATEMENT]) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[stds_view] THEN
      USE_THEN "freg" (MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]) THEN
      ASM_REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
                        POINCARE_SMOOTH_HYPOTHESES_SPHERE_3];
      MATCH_MP_TAC STDS_SLICE_LIMIT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID] THEN
      MATCH_MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `C:real`; `K:real`;
                           `bf:num->real`; `gf:num->real->real^4->real^3^3`]
                          STDS_P514_REGION) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c / K`; `g:real->real^3->real^3^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STDS_PARTIAL_FROM_BOUND THEN
  MAP_EVERY EXISTS_TAC [`A0:real`; `C * K`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`\n. stds_view g0 A0 (bf:num->real) (gf:num->real->real^4->real^3^3) ((sub:num->num) n)`;
     `(\n:num. stereo3_n_inv(vec 0)) o (sub:num->num)`;
     `(\n:num. &0) o (sub:num->num)`; `(\n:num. &1) o (sub:num->num)`;
     `real_interval[&0,c / K]`; `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
     `g:real->real^3->real^3^3`; `vec 0:real^3`; `stds_W g0`;
     `(\n. stds_phi g0 A0 (A0 + &n + &3)) o (sub:num->num)`; `s:real`; `y:real^3`; `C * K`]
    STDS_LIM_RM_BOUND) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[stds_view] THEN
    USE_THEN "freg" (MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]) THEN
    ASM_REWRITE_TAC[REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]
                      POINCARE_SMOOTH_HYPOTHESES_SPHERE_3];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_THM; REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID; STDS_VIEW_PARTS] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `z:real^4`] THEN
    SUBGOAL_THEN `&0 <= s /\ s < (bf:num->real) ((sub:num->num) k)`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `c / K` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_TAC THEN
    USE_THEN "sk" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `(sub:num->num) k`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

