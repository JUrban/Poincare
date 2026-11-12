(* ========================================================================= *)
(* Unit pc_p2c_c1116 (Part 2C): MT Corollary 11.16 in flow form              *)
(* (pp. 273-277): for a Ricci flow on (-T,0] of a connected 3-manifold with  *)
(* complete slices of sec >= 0, canonical neighbourhoods at R > 4, locally   *)
(* bounded curvature, bounded curvature at bounded distance and separating   *)
(* neck spheres, the scalar curvature is bounded on B(xl,0,A) x (-T,0] for   *)
(* every A.  The main theorem is                                             *)
(* P2C_COR_11_16_FLOW_ROUTE: |- !w. P2C_COR_11_16_FLOW_ROUTE_STATEMENT w     *)
(* (the statement of pc_p2c_c1116req).                                       *)
(* ========================================================================= *)

needs "src/pc_p2c_c1116b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The flow context (the hypotheses of the statement with eps <= 1/100,      *)
(* apart from the base point), the bound (s + T) R <= Q, the distance        *)
(* comparison of Claim 11.12, and MT Claim 11.14: a point y far from xl at   *)
(* time 0 (with z from Lemma 11.13) has bounded curvature on (-T,0] (p.      *)
(* 275-277).                                                                 *)
(* ------------------------------------------------------------------------- *)

let p2fl_ctx = new_definition
 `p2fl_ctx (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
           (g:real->B->real^3^3) Tm C eps <=>
    &1 < C /\ &0 < eps /\ eps <= &1 / &100 /\ &0 < Tm /\ hausdorff_space top /\
    smooth_manifold_atlas top atlas /\ connected_space top /\ apx_sphere_sep top atlas /\
    (!a b. --Tm < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
    (!a. --Tm < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!s. --Tm < s /\ s <= &0
         ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
             (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional atlas (g s) y u v) /\
             (!y. y IN topspace top /\ &4 < mfd_scalar atlas (g s) y
                  ==> ?U. rfs_canonical_nbhd (top,atlas) (g s) C eps y U)) /\
    (!a. --Tm < a ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                ==> mfd_rm_norm atlas (g s) y <= K) /\
    (!A. ?D. !s y z. --Tm < s /\ s <= &0 /\ y IN topspace top /\ z IN topspace top /\
                     &2 <= mfd_scalar atlas (g s) y /\
                     mfd_dist (top,atlas) (g s) y z <= A * inv(sqrt(mfd_scalar atlas (g s) y))
                     ==> mfd_scalar atlas (g s) z <= D * mfd_scalar atlas (g s) y)`;;

let P2FL_CTX_SLICES = prove
 (`!top atlas (g:real->B->real^3^3) Tm C eps.
     p2fl_ctx top atlas g Tm C eps
     ==> !s. --Tm < s /\ s <= &0
             ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
                 (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas (g s) y u v)`,
  REWRITE_TAC[p2fl_ctx] THEN MESON_TAC[]);;

let P2FL_CTX_Q = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm C eps.
     P2C_REQ_HARNACK_STATEMENT w /\ p2fl_ctx top atlas g Tm C eps
     ==> ?Q. &0 < Q /\
             !s x. --Tm < s /\ s <= &0 /\ x IN topspace top
                   ==> &0 <= mfd_scalar atlas (g s) x /\
                       (s + Tm) * mfd_scalar atlas (g s) x <= Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2FL_CTX_SLICES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2fl_ctx]) THEN
  MATCH_MP_TAC P2FL_SCALAR_BOUND THEN EXISTS_TAC `w:B->bool` THEN ASM_REWRITE_TAC[]);;

let P2FL_CTX_DIST = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm C eps Q.
     P2C_REQ_DIST_DISTORTION_STATEMENT w /\ p2fl_ctx top atlas g Tm C eps /\ &0 < Q /\
     (!s x. --Tm < s /\ s <= &0 /\ x IN topspace top
            ==> &0 <= mfd_scalar atlas (g s) x /\ (s + Tm) * mfd_scalar atlas (g s) x <= Q)
     ==> !s x y. --Tm < s /\ s <= &0 /\ x IN topspace top /\ y IN topspace top
                 ==> mfd_dist (top,atlas) (g (&0)) x y <= mfd_dist (top,atlas) (g s) x y /\
                     mfd_dist (top,atlas) (g s) x y <=
                     mfd_dist (top,atlas) (g (&0)) x y + &16 * sqrt(Q * Tm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2FL_CTX_SLICES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2fl_ctx]) THEN
  MATCH_MP_TAC P2FL_CLAIM_11_12 THEN EXISTS_TAC `w:B->bool` THEN ASM_REWRITE_TAC[]);;

(* A scale below a distance. *)

let P2FL_INV_SQRT_LT = prove
 (`!A d R. &0 <= A /\ &0 < d /\ (A / d) pow 2 < R ==> A * inv(sqrt R) < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A / d) pow 2` THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `A / d < sqrt R` ASSUME_TAC THENL
   [SUBGOAL_THEN `A / d = sqrt((A / d) pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  UNDISCH_TAC `A / d < sqrt R` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.14 (p. 275): with d = d_0(xl,y) >= 32 sqrt(Q T) and z from    *)
(* Lemma 11.13 (d_0(y,z) = d, d_0(xl,z) > 3d/2), R(y,.) is bounded on        *)
(* (-T,0].  If R(y,s) is large, Claim 11.15 at time s gives a neck sphere    *)
(* within distance M R(y,s)^(-1/2) of y separating xl from z; distances do   *)
(* not increase in time, so a connected set from xl to z at g(0)-distance >= *)
(* rho from y (P2FL_AVOID_POINT) misses the sphere once M R(y,s)^(-1/2) <    *)
(* rho: a contradiction.                                                     *)
(* ------------------------------------------------------------------------- *)

let P2FL_CLAIM_11_14 = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm C eps Q xl y z.
     P2C_REQ_DIST_DISTORTION_STATEMENT w /\
     p2fl_ctx top atlas g Tm C eps /\ ~compact_space top /\ &0 < Q /\
     (!s x. --Tm < s /\ s <= &0 /\ x IN topspace top
            ==> &0 <= mfd_scalar atlas (g s) x /\ (s + Tm) * mfd_scalar atlas (g s) x <= Q) /\
     xl IN topspace top /\ y IN topspace top /\ z IN topspace top /\
     &32 * sqrt(Q * Tm) <= mfd_dist (top,atlas) (g (&0)) xl y /\
     mfd_dist (top,atlas) (g (&0)) y z = mfd_dist (top,atlas) (g (&0)) xl y /\
     &3 / &2 * mfd_dist (top,atlas) (g (&0)) xl y < mfd_dist (top,atlas) (g (&0)) xl z
     ==> ?Ky. !s. --Tm < s /\ s <= &0 ==> mfd_scalar atlas (g s) y <= Ky`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "sl" o MATCH_MP P2FL_CTX_SLICES) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `Q:real`]
               P2FL_CTX_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dd") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2fl_ctx]) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y` THEN
  ABBREV_TAC `c = &16 * sqrt(Q * Tm)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c <= d /\ &0 < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(y:B = xl) /\ ~(z:B = y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[MFD_DIST_REFL; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `y:B`; `xl:B`; `z:B`] P2FL_AVOID_POINT) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `P:B->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `M = sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) + C` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN EXPAND_TAC "M" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= c ==> &0 <= x + c`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt C` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `max (&4) (((M + &45 * sqrt C) / d) pow 2 + (M / rho) pow 2 + &1)` THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `Ry = mfd_scalar atlas ((g:real->B->real^3^3) s) y` THEN
  SUBGOAL_THEN `&4 < Ry /\ ((M + &45 * sqrt C) / d) pow 2 < Ry /\ (M / rho) pow 2 < Ry`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(M + &45 * sqrt C) / d` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `M / rho` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o C MP (CONJ (ASSUME `--Tm < s`) (ASSUME `s <= &0`)) o
                 SPEC `s:real`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?U. rfs_canonical_nbhd (top,atlas) ((g:real->B->real^3^3) s) C eps y U`
  (X_CHOOSE_TAC `U:B->bool`) THENL
   [FIRST_X_ASSUM(MP_TAC o C MP (CONJ (ASSUME `--Tm < s`) (ASSUME `s <= &0`)) o SPEC `s:real` o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_canonical_nbhd"
                                               with Failure _ -> false)) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = inv(sqrt Ry)` THEN
  SUBGOAL_THEN `(M + &45 * sqrt C) * r < d /\ M * r < rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THEN MATCH_MP_TAC P2FL_INV_SQRT_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `d <= mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y xl /\
    mfd_dist (top,atlas) (g s) y xl <= d + c /\
    d <= mfd_dist (top,atlas) (g s) y z /\ mfd_dist (top,atlas) (g s) y z <= d + c /\
    &3 / &2 * d < mfd_dist (top,atlas) (g s) xl z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) y xl = d`
    ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `y:B`; `xl:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `y:B`; `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `xl:B`; `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a0 = mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y xl` THEN
  ABBREV_TAC `a1 = mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y z` THEN
  ABBREV_TAC `X = mfd_dist (top,atlas) ((g:real->B->real^3^3) s) xl z` THEN
  SUBGOAL_THEN `(a0 - a1) pow 2 + a0 * a1 / &4 < X pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a0 - a1) pow 2 <= (d / &2) pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a0 * a1 <= (&3 / &2 * d) * (&3 / &2 * d)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&3 / &2 * d) pow 2 < X pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d * d` MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
                                            ALL_TAC] THEN
    UNDISCH_TAC `(a0 - a1) pow 2 <= (d / &2) pow 2` THEN
    UNDISCH_TAC `a0 * a1 <= (&3 / &2 * d) * (&3 / &2 * d)` THEN
    UNDISCH_TAC `(&3 / &2 * d) pow 2 < X pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `C:real`; `eps:real`; `y:B`; `xl:B`; `z:B`;
                 `U:B->bool`; `M:real`; `r:real`] P2FL_CLAIM_11_15) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:B->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `apx_separates top (S:B->bool) xl z` THEN REWRITE_TAC[apx_separates] THEN
  STRIP_TAC THEN UNDISCH_TAC
   `~connected_component_of (subtopology top (topspace top DIFF S)) (xl:B) z` THEN
  REWRITE_TAC[connected_component_of] THEN EXISTS_TAC `P:B->bool` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(P:B->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:B) IN mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (M * r)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `y:B`; `q:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rho <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) y q` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The compact case of Cor 11.16 (MT p. 277: min R(.,t) is bounded by        *)
(* Proposition 4.1, then Lemma 11.11 on the whole manifold) and a            *)
(* curve-diameter helper.  Here the bound on min R comes from                *)
(* P2C_REQ_SCALAR_MIN before time -T/2 and from abs Rm on [-T/2,0] after.    *)
(* ------------------------------------------------------------------------- *)

(* Points of a C1 curve are within its length. *)

let P2FL_CURVE_DIAM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t1 t2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma a b /\
     t1 IN real_interval[a,b] /\ t2 IN real_interval[a,b]
     ==> mfd_joinable (top,atlas) (gamma t1) (gamma t2) /\
         mfd_dist (top,atlas) g (gamma t1) (gamma t2) <= mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v. a <= u /\ u <= v /\ v <= b
          ==> mfd_joinable (top,atlas) ((gamma:real->A) u) (gamma v) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (gamma u) (gamma v) <=
              mfd_length atlas g gamma a b`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `u:real`; `b:real`]
                  MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `u:real`; `v:real`; `b:real`]
                  MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma:real->A) u v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `u:real`] MFD_LENGTH_POS_LE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `v:real`; `b:real`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `t1 <= t2 \/ t2 <= t1:real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t2:real`; `t1:real`]) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]);;

(* The compact case. *)

let P2FL_COR_COMPACT = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm C eps xl.
     P2C_REQ_HARNACK_STATEMENT w /\ P2C_REQ_DIST_DISTORTION_STATEMENT w /\
     P2C_REQ_SCALAR_MIN_STATEMENT w /\
     p2fl_ctx top atlas g Tm C eps /\ compact_space top /\ xl IN topspace top
     ==> ?K. !s y. --Tm < s /\ s <= &0 /\ y IN topspace top
                   ==> mfd_scalar atlas (g s) y <= K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "sl" o MATCH_MP P2FL_CTX_SLICES) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`] P2FL_CTX_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `Q:real`]
               P2FL_CTX_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dd") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2fl_ctx]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--Tm / &2` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
        (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  SUBGOAL_THEN `!s y. --Tm / &2 <= s /\ s <= &0 /\ y IN topspace top
                      ==> mfd_scalar atlas ((g:real->B->real^3^3) s) y <= &6 * max K0 (&0)`
  (LABEL_TAC "r6") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mfd_rm_norm atlas ((g:real->B->real^3^3) s) y <= max K0 (&0)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= K ==> x <= max K (&0)`) THEN
      USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `y:B`; `max K0 (&0)`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ASM_SIMP_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. --Tm < s /\ s <= &0
                    ==> ?y. y IN topspace top /\
                            mfd_scalar atlas ((g:real->B->real^3^3) s) y <= &6 * max K0 (&0)`
  (LABEL_TAC "min") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `--Tm / &2 <= s` THENL
     [EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN USE_THEN "r6" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `P2C_REQ_SCALAR_MIN_STATEMENT (w:B->bool)` THEN
    REWRITE_TAC[P2C_REQ_SCALAR_MIN_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                               `(--Tm + s) / &2`; `&0`; `g:real->B->real^3^3`; `s:real`;
                               `--Tm / &2`; `xl:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "ricci_flow_on"
                                 with Failure _ -> false)) (concl th) && is_forall(concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) (--Tm / &2)) xl` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "r6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?B. !p. p IN topspace top
                        ==> mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl p <= B`
  (X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THENL
   [SUBGOAL_THEN `real_bounded (IMAGE (\p. mfd_dist (top,atlas)
                                         ((g:real->B->real^3^3) (&0)) xl p) (topspace top))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[GSYM compact_space] THEN
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `Tm:real`; `&6 * max K0 (&0)`;
                 `&2 * B + &16 * sqrt(Q * Tm)`] P2FL_LEMMA_11_11) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "sl" (MP_TAC o C MP (ASSUME `--Tm < s /\ s <= &0`) o SPEC `s:real`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kx:real` (LABEL_TAC "kx")) THEN
  EXISTS_TAC `Kx:real` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  USE_THEN "min" (MP_TAC o C MP (CONJ (ASSUME `--Tm < s`) (ASSUME `s <= &0`)) o
                  SPEC `s:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC) THEN
  USE_THEN "kx" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`topspace top:B->bool`; `y0:B`] THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE; SUBSET_REFL] THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `q:B`] THEN STRIP_TAC THEN
  USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `p:B`; `q:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p q <= &2 * B`
  MP_TAC THENL
   [SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) p xl /\
                  mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl q`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`; `xl:B`; `q:B`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`; `xl:B`] MFD_DIST_SYM) THEN
    USE_THEN "B" (MP_TAC o C MP (ASSUME `(p:B) IN topspace top`) o SPEC `p:B`) THEN
    USE_THEN "B" (MP_TAC o C MP (ASSUME `(q:B) IN topspace top`) o SPEC `q:B`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The noncompact case of Cor 11.16 (MT p. 277).  A point y0 with d_0(xl,y0) *)
(* >= max(D, 32 sqrt(Q T)) exists (closed balls are compact and the slice is *)
(* not), Claim 11.14 bounds R(y0,.), and Lemma 11.11 with W = a near-minimal *)
(* g(0)-curve from y0 to y bounds R(y,.) on B(xl,0,A).                       *)
(* ------------------------------------------------------------------------- *)

let P2FL_COR_NONCOMPACT = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) Tm C eps xl.
     P2C_REQ_HARNACK_STATEMENT w /\ P2C_REQ_DIST_DISTORTION_STATEMENT w /\
     P2C_REQ_LEMMA_11_13_STATEMENT w /\
     p2fl_ctx top atlas g Tm C eps /\ ~compact_space top /\ xl IN topspace top
     ==> !A. ?K. !s y. --Tm < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                       ==> mfd_scalar atlas (g s) y <= K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `A:real` THEN
  FIRST_ASSUM(LABEL_TAC "sl" o MATCH_MP P2FL_CTX_SLICES) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`] P2FL_CTX_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `Q:real`]
               P2FL_CTX_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dd") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2fl_ctx]) THEN
  USE_THEN "sl" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `P2C_REQ_LEMMA_11_13_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2C_REQ_LEMMA_11_13_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `(g:real->B->real^3^3) (&0)`; `xl:B`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l13"))) THEN
  ABBREV_TAC `D1 = max D0 (&32 * sqrt(Q * Tm))` THEN
  SUBGOAL_THEN `D0 <= D1 /\ &32 * sqrt(Q * Tm) <= D1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?y0. y0 IN topspace top /\
                     D1 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y0`
  (X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `~(!y0. y0 IN topspace top
                          ==> mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y0 < D1)`
    MP_TAC THENL [ALL_TAC; MESON_TAC[REAL_NOT_LT]] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~compact_space(top:B topology)` THEN REWRITE_TAC[compact_space] THEN
    SUBGOAL_THEN `topspace top = mfd_cball (top,atlas) ((g:real->B->real^3^3) (&0)) xl D1`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `p:B` THEN EQ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl p`
        ASSUME_TAC THENL
         [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "l13" (MP_TAC o SPEC `y0:B`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `Q:real`;
                `xl:B`; `y0:B`; `z0:B`] P2FL_CLAIM_11_14) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ky:real` (LABEL_TAC "Ky")) THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y0 + A + &1 +
                  &16 * sqrt(Q * Tm)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `Tm:real`; `Ky:real`; `L:real`] P2FL_LEMMA_11_11) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "sl" (MP_TAC o C MP (ASSUME `--Tm < s /\ s <= &0`) o SPEC `s:real`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kx:real` (LABEL_TAC "kx")) THEN
  EXISTS_TAC `Kx:real` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y0 y /\
                mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y0 xl`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `y0:B`; `y:B`; `&1`] P2BC_DIST_APPROX) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:real->B` STRIP_ASSUME_TAC) THEN
  USE_THEN "kx" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (ga:real->B) (real_interval[&0,&1])`; `y0:B`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
    ASM_MESON_TAC[mfd_c1_curve];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`]
                        MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    USE_THEN "Ky" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  X_GEN_TAC `t2:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `ga:real->B`; `&0`; `&1`; `t1:real`; `t2:real`]
                P2FL_CURVE_DIAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((ga:real->B) t1) IN topspace top /\ ((ga:real->B) t2) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`]
                        MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPECL [`s:real`; `(ga:real->B) t1`; `(ga:real->B) t2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `y0:B`; `xl:B`; `y:B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `y0:B`; `xl:B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.  MT Corollary 11.16 in flow form from the five route    *)
(* inputs (Harnack, distance distortion, Lemma 11.13, the scalar minimum     *)
(* principle on compact slices, no cap in a neck), with eps0 = 1/100.  The   *)
(* input APX_NO_CAP_IN_NECK_STATEMENT is not used by this proof: the cap     *)
(* case of Claim 11.15 also ends in the separation argument.                 *)
(* ------------------------------------------------------------------------- *)

let P2C_COR_11_16_FLOW_ROUTE = prove
 (`!w:B->bool. P2C_COR_11_16_FLOW_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_COR_11_16_FLOW_ROUTE_STATEMENT; P2C_COR_11_16_FLOW_STATEMENT] THEN
  STRIP_TAC THEN EXISTS_TAC `&1 / &100` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `Tm:real`; `xl:B`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2fl_ctx (top:B topology) atlas (g:real->B->real^3^3) Tm C eps` ASSUME_TAC THENL
   [REWRITE_TAC[p2fl_ctx] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN
  ASM_CASES_TAC `compact_space(top:B topology)` THENL
   [MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `xl:B`]
                 P2FL_COR_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl A` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    MP_TAC(SPECL [`w:B->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                  `g:real->B->real^3^3`; `Tm:real`; `C:real`; `eps:real`; `xl:B`]
                 P2FL_COR_NONCOMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SPEC `A:real`)]);;

