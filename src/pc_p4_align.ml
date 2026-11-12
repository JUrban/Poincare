(* ========================================================================= *)
(* Unit pc_p4_align: alignment of Part 4 with Part 3.  Part 3 states         *)
(* P4_EXTINCTION_STATEMENT (pc_p3_core) with its invariant p3_inv            *)
(* (pc_p3_inv) in place of rfs_controlled.  P4_EXTINCTION_ALIGN proves it    *)
(* from FINITE_EXTINCTION_STATEMENT and one bridge statement,                *)
(* P4_PINCH_FROM_INV_STATEMENT: the invariant (the caps and the smooth       *)
(* radial collapses of p3_cap_ok, the limit metrics) gives the pinch maps    *)
(* p4_pinch_ok (MT Prop 15.12 with the extension of the map written out, and *)
(* a (1+eta)-Lipschitz bound for t < T in place of distance decreasing) for  *)
(* histories starting at a closed simply connected manifold (the cut spheres *)
(* then separate, as in MT Remark 0.6(ii)).  P4_EXTINCTION_CM1 combines it   *)
(* with the CM level of pc_p4_cm.  P4_FINITE_EXTINCTION_CM2 and              *)
(* P4_EXTINCTION_CM2 drop the five elementary area and width facts, proved   *)
(* in pc_p4_width.                                                           *)
(* ========================================================================= *)

needs "src/pc_p3_assembly.ml";;
needs "src/pc_p4_cm.ml";;
needs "src/pc_p4_width.ml";;

prioritize_real();;
type_invention_error := true;;

let P4_PINCH_FROM_INV_STATEMENT = new_definition
 `P4_PINCH_FROM_INV_STATEMENT (u:A->bool) <=>
    !C eps hf md g0 A0 rs ks dd (hs:(A+num#num#real^3)rfs_history)
     top atlas g iota iota'.
        &1 < C /\ &0 < eps /\ p3_hfun C hf /\ p3_modulus md /\
        p3_std_initial g0 A0 /\
        p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top /\ riemannian_metric atlas g /\
        rfs_initial (top,atlas) g hs iota iota'
        ==> p4_pinch_ok hs`;;

let P4_EXTINCTION_ALIGN = prove
 (`FINITE_EXTINCTION_STATEMENT (:A) /\ P4_PINCH_FROM_INV_STATEMENT (:A)
   ==> P4_EXTINCTION_STATEMENT (:A)`,
  REWRITE_TAC[FINITE_EXTINCTION_STATEMENT; P4_PINCH_FROM_INV_STATEMENT;
              P4_EXTINCTION_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin") (LABEL_TAC "pin")) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`] THEN STRIP_TAC THEN
  USE_THEN "fin" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  EXISTS_TAC `T0:real` THEN
  MAP_EVERY X_GEN_TAC
   [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
    `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`; `ks:num->real`; `dd:num->real`;
    `hs:(A+num#num#real^3)rfs_history`; `iota:A->A+num#num#real^3`;
    `iota':A+num#num#real^3->A`] THEN
  STRIP_TAC THEN
  USE_THEN "ext" (MP_TAC o SPECL
   [`hs:(A+num#num#real^3)rfs_history`; `C:real`; `eps:real`;
    `p3_stepf rs`; `p3_stepf dd`; `p3_stepf ks`;
    `p3_hscale hf (p3_stepf rs) (p3_stepf dd)`;
    `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3_INV_CONTROLLED THEN
    MAP_EVERY EXISTS_TAC [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "pin" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
      `g0:real^3->real^3^3`; `A0:real`; `rs:num->real`; `ks:num->real`; `dd:num->real`;
      `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
      `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
    ASM_REWRITE_TAC[]]);;

let P4_EXTINCTION_CM1 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_AREA_TAYLOR_STATEMENT (:A+num#num#real^3) /\
   P4_WIDTH_CONTINUITY_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_CM_NONNEG_STATEMENT (:A+num#num#real^3) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:A+num#num#real^3) /\
   P4_PINCH_FROM_INV_STATEMENT (:A)
   ==> P4_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_EXTINCTION_ALIGN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_FINITE_EXTINCTION_CM1 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* CM2: the five elementary facts are theorems (pc_p4_width), so finite      *)
(* extinction and its Part 3 form P4_EXTINCTION_STATEMENT follow from the    *)
(* analytic core (CM Thm 1.14 + Prop 1.5, Lemma 1.22), the three topology    *)
(* statements and, for the Part 3 form, the pinch bridge.                    *)
(* ------------------------------------------------------------------------- *)

let P4_FINITE_EXTINCTION_CM2 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A)
   ==> FINITE_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_FINITE_EXTINCTION_CM1 THEN
  ASM_REWRITE_TAC[P4_AREA_TAYLOR; P4_WIDTH_CONTINUITY; P4_PINCH_AREA;
                  P4_CM_NONNEG; P4_CM_ISOMETRY]);;

let P4_EXTINCTION_CM2 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_FROM_INV_STATEMENT (:A)
   ==> P4_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_EXTINCTION_ALIGN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_FINITE_EXTINCTION_CM2 THEN ASM_REWRITE_TAC[]);;

