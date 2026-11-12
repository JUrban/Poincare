(* ========================================================================= *)
(* Unit pc_p2b_largedr: piece 2 of COR_9_94_L (e) in the Part 2C proof,      *)
(* P2BLD_LARGE_DR_ROUTE |- !w. P2KC_LARGE_DR_ROUTE_STATEMENT w (statement in *)
(* pc_p2c_e994s).  A compact kappa-solution with ksep that is not round at   *)
(* time 0 has times t <= 0 with d_t(p,q)^2 R_t(z) as large as wanted: its    *)
(* asymptotic soliton is not compact round (MT Cor 9.44 at t0 = 0), so it is *)
(* the cylinder model, which is not compact; its complete slice at limit     *)
(* time 0 has far points and a point of positive R, and the distances and R  *)
(* pass to the rescaled slices at -tau_k (LIM_DIST, LIM_CURV), where d^2 R   *)
(* is scale invariant.                                                       *)
(* ========================================================================= *)

needs "src/pc_p2c_e994s.ml";;
needs "src/pc_lim_dist.ml";;     (* LIM_DIST *)
needs "src/pc_lim_curv.ml";;     (* LIM_CURV *)
needs "src/pc_p2b_rmhalf.ml";;   (* P2BX0_RM_NORM_LE_HALF_SCALAR *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Copies, under new names, of lemmas from units outside the load closure of *)
(* this unit (pc_rfa_c971 would add 187 files, pc_p2b_shrinkcl 156).         *)
(* ========================================================================= *)

(* Copy of RFA_C971_KSOL_METRICS (pc_rfa_c971.ml). *)

let P2BLD_KSOL_METRICS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> smooth_manifold_atlas top atlas /\
         !s. s <= &0 ==> riemannian_metric atlas (g s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
  STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Copy of P2BSK_TWIST_NORM (pc_p2b_shrinkcl.ml). *)

let P2BLD_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

(* Copy of P2BSK_CYL_NOT_COMPACT (pc_p2b_shrinkcl.ml). *)

let P2BLD_CYL_NOT_COMPACT = prove
 (`!top atlas (g:real->B->real^3^3). p2b_cyl_model (top,atlas) g ==> ~compact_space top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "im")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj") ASSUME_TAC)))))) THEN
  ABBREV_TAC `U = \n. IMAGE (p:real^3->B) (annulus (inv(&n + &1)) (&n + &1))` THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` (LABEL_TAC "ip") THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LT_INV THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. open_in top ((U:num->B->bool) n)` (LABEL_TAC "op") THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "U" THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (inv(&n + &1)) (&n + &1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN
      USE_THEN "ip" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (p:real^3->B) (ball(y,r) INTER annulus (inv(&n + &1)) (&n + &1))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `ball(y:real^3,r)`] THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_ANNULUS; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (U:num->B->bool) m SUBSET U n` (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&m + &1) /\ &m + &1 <= &n + &1` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN
      MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[compact_space; compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:num->B->bool) (:num)` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "im" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `max (norm(y:real^3)) (inv(norm y))` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `VV:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:num->B->bool`; `(:num)`; `VV:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:num->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `FINITE (S:num->bool)` THEN REWRITE_TAC[num_FINITE] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `topspace top SUBSET (U:num->B->bool) N` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (VV:(B->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ys = (&N + &2) % (basis 1:real^3)` THEN
  SUBGOAL_THEN `norm(ys:real^3) = &N + &2 /\ ~(ys = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ys" THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; GSYM NORM_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) ys IN (U:num->B->bool) N` MP_TAC THENL
   [UNDISCH_TAC `topspace top SUBSET (U:num->B->bool) N` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "im" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  EXPAND_TAC "U" THEN REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN USE_THEN "ip" (MP_TAC o SPEC `N:num`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = ys)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(z:real^3) < &N + &1` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z = rfs_twist (ys:real^3))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `inv(&N + &1) < norm(z:real^3)` THEN
    ASM_SIMP_TAC[P2BLD_TWIST_NORM] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "inj" (DISJ_CASES_THEN (MP_TAC o SPECL [`ys:real^3`; `z:real^3`])) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* One slice of a kappa-solution (complete, Riemannian, a point of positive  *)
(* R), far points of a complete noncompact connected manifold, and the final *)
(* arithmetic.                                                               *)
(* ========================================================================= *)

let P2BLD_SLICE_FACTS = prove
 (`!kappa top atlas (g:real->B->real^3^3) s.
     p2b_kappa_solution kappa (top,atlas) g /\ s <= &0
     ==> hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
         riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
         ?z. z IN topspace top /\ &0 < mfd_scalar atlas (g s) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] P2BLD_KSOL_METRICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    let tm = concl th in
    is_forall tm &&
    (let b = snd(dest_forall tm) in
     is_imp b &&
     (let c = snd(dest_imp b) in
      is_exists c && is_conj(snd(dest_exists c)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) c)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `z:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]);;

(* A complete connected manifold that is not compact has far points. *)

let P2BLD_FAR_POINT = prove
 (`!top atlas (g:B->real^3^3) z B.
     connected_space top /\ smooth_manifold_atlas top atlas /\
     mfd_complete (top,atlas) g /\ ~compact_space top /\ z IN topspace top
     ==> ?p. p IN topspace top /\ mfd_joinable (top,atlas) z p /\
             B < mfd_dist (top,atlas) g z p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  UNDISCH_TAC `~compact_space (top:B topology)` THEN REWRITE_TAC[compact_space] THEN
  SUBGOAL_THEN `topspace top = mfd_cball (top,atlas) (g:B->real^3^3) z B` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (z:B) y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_complete (top,atlas) (g:B->real^3^3)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The final inequality. *)

let P2BLD_ARITH = prove
 (`!a b c r d. &1 <= c /\ c < a /\ r / &2 < b /\ &0 < r /\ r / &2 * c = d + &1 + r / &2
               ==> d < a pow 2 * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= a pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * &1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (r / &2) <= a pow 2 * b` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2BLD_DIV_LZERO = prove
 (`!x. &0 / x = &0`,
  REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

(* ========================================================================= *)
(* The route theorem.  The asymptotic soliton (top',g') of the compact       *)
(* non-round g is not compact (MT Cor 9.44 at t0 = 0 excludes the compact    *)
(* round limit; the cylinder model is not compact).  At limit time 0 (time   *)
(* -1/2 of the shifted kappa-solution) g'(0) is complete with a point z0 of  *)
(* positive R and far points p0; LIM_DIST and LIM_CURV move d(z0,p0) and     *)
(* R(z0) to the slices g(-tau_k), rescaled by inv(tau_k), and d^2 R does not *)
(* see the scale.                                                            *)
(* ========================================================================= *)

let P2BLD_LARGE_DR_ROUTE = prove
 (`!w:B->bool. P2KC_LARGE_DR_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2KC_LARGE_DR_ROUTE_STATEMENT; P2KC_LARGE_DR_STATEMENT;
                           P2B_ASYM_SOLITON_STATEMENT; P2B_COR_9_44_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "as") (LABEL_TAC "c44")) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `D:real`] THEN
  STRIP_TAC THEN
  USE_THEN "as" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `f:B->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "alt"))))))))))))))) THEN
  (* the limit slice at time 0 (before the compactness step: COR_9_44 needs *)
  (* its metric) *)
  MP_TAC(ISPECL [`kappa:real`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `\t. (g':real->B->real^3^3)(t + &1 / &2)`; `--(&1 / &2)`]
                P2BLD_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[REAL_ARITH `--(&1 / &2) + &1 / &2 = &0`] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z0:B` STRIP_ASSUME_TAC)))))) THEN
  (* the limit is not compact *)
  SUBGOAL_THEN `~compact_space (top':B topology)` ASSUME_TAC THENL
   [USE_THEN "alt" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `~p2b_round (top,atlas) ((g:real->B->real^3^3) (&0))`)) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      USE_THEN "c44" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `&0`; `tau:num->real`; `q:num->B`;
        `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
        `g':real->B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID; ETA_AX];
      MATCH_MP_TAC P2BLD_CYL_NOT_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas':((B->bool)#(B->real^3))->bool`;
                            `\t. (g':real->B->real^3^3)(t + &1 / &2)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Rz = mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z0` THEN
  ABBREV_TAC `c = &2 * (D pow 2 + &1) / Rz + &1` THEN
  SUBGOAL_THEN `&1 <= c /\ Rz / &2 * c = D pow 2 + &1 + Rz / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SUBGOAL_THEN `&0 <= (D pow 2 + &1) / Rz` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC(SPEC `D:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; UNDISCH_TAC `&0 < Rz` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* a far point *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `z0:B`; `c + &1 / &2`] P2BLD_FAR_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p0:B` STRIP_ASSUME_TAC) THEN
  (* the limit with its exhaustion and maps *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2C_FLOW_LIMIT_ON_WITH] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p3_flow_limit_on")) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  (* the slices of the view *)
  SUBGOAL_THEN
   `!tt. ~(topspace(rfs_vtop (p2b_kview (top,atlas) (g:real->B->real^3^3)) tt) = {})
         ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top,atlas) g) tt)
                                   (rfs_vatlas (p2b_kview (top,atlas) g) tt) /\
             riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) tt)
                               (rfs_vmetric (p2b_kview (top,atlas) g) tt)`
  (LABEL_TAC "vw") THENL
   [GEN_TAC THEN
    REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`] P2BLD_KSOL_METRICS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. rfs_vtop (p2b_kview (top,atlas) (g:real->B->real^3^3)) (--((tau:num->real) k)) = top /\
                    rfs_vatlas (p2b_kview (top,atlas) g) (--(tau k)) = atlas /\
                    rfs_vmetric (p2b_kview (top,atlas) g) (--(tau k)) = g (--(tau k))`
  (LABEL_TAC "sl") THENL
   [GEN_TAC THEN
    REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    SUBGOAL_THEN `--((tau:num->real) k) <= &0` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (term_match [] `!k:num. &0 < (tau:num->real) k`) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  (* distances *)
  MP_TAC(REWRITE_RULE[LIM_DIST_STATEMENT] (ISPECL [`UNIV:B->bool`; `UNIV:B->bool`] LIM_DIST)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`; `{s:real | s < &1}`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->B`; `&0`; `{z0:B, p0}`; `&1 / &2`]) THEN
  BETA_TAC THEN REWRITE_TAC[P2BLD_DIV_LZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET] THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_TAC `k0:num`)] THEN
  (* the scalar curvature *)
  MP_TAC(REWRITE_RULE[LIM_CURV_STATEMENT] (ISPECL [`UNIV:B->bool`; `UNIV:B->bool`] LIM_CURV)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`; `{s:real | s < &1}`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->B`; `&0`; `z0:B`]) THEN
  BETA_TAC THEN REWRITE_TAC[P2BLD_DIV_LZERO; REAL_ADD_RID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `Rz / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
  (* the time and the points *)
  ABBREV_TAC `k = MAX k0 N1` THEN
  SUBGOAL_THEN `(k0:num) <= k /\ (N1:num) <= k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `--((tau:num->real) k)` THEN
  MAP_EVERY EXISTS_TAC [`(phi:num->B->B) k z0`; `(phi:num->B->B) k p0`;
                        `(phi:num->B->B) k z0`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (term_match [] `!n:num. N1 <= n ==> P n`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `z0:B`; `p0:B`] o check (fun th ->
    can (find_term ((=) `k0:num`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (tau:num->real) k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dk = mfd_dist (top,atlas) ((g:real->B->real^3^3) (--((tau:num->real) k)))
                            ((phi:num->B->B) k z0) (phi k p0)` THEN
  ABBREV_TAC `Rk = mfd_scalar atlas ((g:real->B->real^3^3) (--((tau:num->real) k)))
                              ((phi:num->B->B) k z0)` THEN
  SUBGOAL_THEN `dk pow 2 * Rk = (sqrt(inv((tau:num->real) k)) * dk) pow 2 * (Rk / inv(tau k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `&0 < inv((tau:num->real) k)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < inv((tau:num->real) k)` THEN UNDISCH_TAC `&0 < (tau:num->real) k` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC P2BLD_ARITH THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `Rz:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

