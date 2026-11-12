(* ========================================================================= *)
(* pc_p2b_shrinkcl: the shrink chain of Part 2B in route form (the           *)
(* statements are in pc_p2b_chainstmts).                                     *)
(*   P2B_SOLITON_CLASS_ROUTE  COR_9_53 /\ THM_9_42F ==> SOLITON_CLASS;      *)
(*   P2B_THM_9_42F_ROUTE      PROP_9_46 /\ SHRINKER_ROUND /\ X1 /\          *)
(*                            UNIQ_COMPLETE ==> THM_9_42F;                   *)
(*   P2B_COR_9_53_ROUTE       X1 /\ X2 /\ PROP_2_19_SEP ==> COR_9_53.        *)
(* THM_9_42F needs no uniqueness argument.  A zero plane at time 1/2 gives   *)
(* the cylinder disjunct by X1 at s0 = 1/2; otherwise Prop 9.46 on the       *)
(* shrinker slice 2 g(1/2) gives compactness, a zero plane at time 0 would   *)
(* put a cylinder model (X1 at s0 = 0) on a compact space, so the sectional  *)
(* curvature at time 0 is positive and SHRINKER_ROUND applies.  The          *)
(* hypothesis UNIQ_COMPLETE (P2C_REQ_UNIQ_COMPLETE) of the route is not      *)
(* used; COR_9_53 does not use X1 either (Prop 2.19 needs only sec >= 0).    *)
(* Its core P2BSK_COR_9_53_CORE takes X2, whose statement                    *)
(* P2B_CYL_AT_INFINITY_STATEMENT includes the conjunct                       *)
(* (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g'),                   *)
(* and gives P2B_COR_9_53_ROUTE.                                             *)
(* ========================================================================= *)

needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_p2b_x0.ml";;
needs "src/pc_p2a_flow.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_rfa_shiscale.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_smt_product.ml";;
needs "src/pc_apx_chain.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The kappa-solution bookkeeping.  A class flow on s < b with               *)
(* bounded slices, shifted by s0 < b, is a p2b_kappa_solution: the fields of *)
(* p2c_kappa_sol by the time shift, and |Rm| uniformly bounded on [a,0] by   *)
(* |Rm(t)| <= R(t)/2 <= R(s0)/2 <= 3 |Rm(s0)| (sec >= 0, dR/ds >= 0).       *)
(* ------------------------------------------------------------------------- *)

let P2BSK_KNC_SHIFT = prove
 (`!top atlas (g:real->B->real^3^3) b s0 kappa r0.
     s0 < b /\ rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {s | s < b} g) kappa r0
     ==> rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g(t + s0)))
                                kappa r0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_parabolic_exists; rfs_persists;
              rfs_vball; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kn")) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
  ASM_CASES_TAC `t <= &0` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  REMOVE_THEN "kn" (MP_TAC o SPECL [`t + s0:real`; `x:B`; `r:real`]) THEN
  SUBGOAL_THEN `t + s0 < b` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - s0:real` o
      check (fun th -> can (find_term (fun t -> is_const t &&
                            fst(dest_const t) = "smooth_manifold_atlas")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s - s0 <= &0 /\ s < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s - s0:real`; `y:B`] o
      check (fun th -> can (find_term (fun t -> is_const t &&
                            fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_ADD]]);;

let P2BSK_KSOL_SHIFT = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0.
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\
     (!s. s < b ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g s) x <= K)
     ==> p2b_kappa_solution kappa (top,atlas) (\t. g(t + s0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn"))))))))))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o SPEC `s0 - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. (g:real->B->real^3^3)(t + s0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\t. (g:real->B->real^3^3)(t + s0)) = (\t. g(s0 + t))` SUBST1_TAC THENL
     [ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BX0_FLOW_UPTO_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`s0 + a - &1`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a <= &0
        ==> ?K. !t x. a <= t /\ t <= &0 /\ x IN topspace top
                      ==> mfd_rm_norm atlas ((g:real->B->real^3^3)(t + s0)) x <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `s0:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `K0:real`)] THEN
    EXISTS_TAC `&3 * K0` THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN
    USE_THEN "rf" (MP_TAC o SPEC `t + s0 - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(t + s0)) /\
                  riemannian_metric atlas (g s0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ricci_flow_on (top,atlas) (t + s0 - &1) b (g:real->B->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(t + s0)`; `x:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `t + s0 - &1`;
                   `b:real`; `g:real->B->real^3^3`; `x:B`; `t + s0`; `s0:real`]
                  P2BX0_SCALAR_MONO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MAP_EVERY X_GEN_TAC [`sd:real`; `dR:real`] THEN STRIP_TAC THEN
      USE_THEN "dr" (MP_TAC o SPECL [`sd:real`; `x:B`; `dR:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s0`; `x:B`] P2AU_MFD_SCALAR_ABS_3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "cp" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "nf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC P2BSK_KNC_SHIFT THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The route P2B_SOLITON_CLASS_ROUTE.                                        *)
(* ------------------------------------------------------------------------- *)

let P2B_SOLITON_CLASS_ROUTE = prove
 (`!w:B->bool. P2B_SOLITON_CLASS_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SOLITON_CLASS_ROUTE_STATEMENT; P2B_SOLITON_CLASS_STATEMENT;
              P2B_COR_9_53_STATEMENT; P2B_THM_9_42F_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c953") (LABEL_TAC "t942")) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `f:real->B->real`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p2b_ancflow kappa (top,atlas) (g:real->B->real^3^3) (&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2b_sflow]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s < &1 ==> ?K. !x. x IN topspace top
                                       ==> mfd_rm_norm atlas ((g:real->B->real^3^3) s) x <= K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "c953" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BSK_KSOL_SHIFT THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[p2b_ancflow]; REAL_ARITH_TAC];
    USE_THEN "t942" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `f:real->B->real`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Slice noncollapsing (MT Cor 9.54 for a class flow: radius               *)
(* r/2 parabolic balls, |Rm(s)| <= R(s)/2 <= R(s1)/2 <= 3 |Rm(s1)|), its     *)
(* invariance under constant rescaling, and the cylinder model is never     *)
(* compact.                                                                  *)
(* ------------------------------------------------------------------------- *)

let P2BSK_SLICE_NONCOLL = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s1.
     p2b_ancflow0 kappa (top,atlas) g b /\ s1 < b
     ==> p2b_rm_noncoll (kappa / &8) (top,atlas) (g s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn"))))))))))
    ASSUME_TAC) THEN
  REWRITE_TAC[p2b_rm_noncoll; DIMINDEX_3] THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))) THEN
  SUBGOAL_THEN `!s. s < b ==> smooth_manifold_atlas (top:B topology) atlas /\
                              riemannian_metric atlas ((g:real->B->real^3^3) s) /\
                              ricci_flow_on (top,atlas) (s - &1) b g`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "rf" (MP_TAC o SPEC `s - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[ricci_flow_on] th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPEC `s1:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < r / &2 /\ inv((r / &2) pow 2) = &4 * inv(r pow 2) /\
                &0 <= inv(r pow 2) /\ (r / &2) pow 3 = r pow 3 / &8`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  USE_THEN "kn" (MP_TAC o SPEC `r / &2`) THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_parabolic_exists; rfs_persists;
              rfs_vball; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:real`; `p:B`; `r / &2`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s < b` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[MFD_BALL_OPEN]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top /\
                  y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s1) p r`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `(g:real->B->real^3^3) s1`; `p:B`; `r / &2`] MFD_BALL_OPEN) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        ASM SET_TAC[];
        UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s1) p (r / &2)` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "sl" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `y:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s - &1`;
                   `b:real`; `g:real->B->real^3^3`; `y:B`; `s:real`; `s1:real`]
                  P2BX0_SCALAR_MONO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MAP_EVERY X_GEN_TAC [`sd:real`; `dR:real`] THEN STRIP_TAC THEN
      USE_THEN "dr" (MP_TAC o SPECL [`sd:real`; `y:B`; `dR:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s1`; `y:B`] P2AU_MFD_SCALAR_ABS_3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "rb" (MP_TAC o SPEC `y:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s1`; `p:B`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "cp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) s1)
                (mfd_ball (top,atlas) (g s1) p r)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s1`; `mfd_ball (top,atlas) ((g:real->B->real^3^3) s1) p (r / &2)`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) s1) p r`; `v1:real`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) s1)
                    (mfd_ball (top,atlas) (g s1) p r)`] MFD_HAS_VOLUME_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BSK_NONCOLL_SCALE = prove
 (`!kappa top atlas (g:B->real^3^3) c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     p2b_rm_noncoll kappa (top,atlas) g
     ==> p2b_rm_noncoll kappa (top,atlas) (\z. c %% g z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_rm_noncoll; DIMINDEX_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc")))) THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `r:real`] THEN
  ASM_SIMP_TAC[MFD_BALL_SCALE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))) THEN
  ABBREV_TAC `sc = sqrt c` THEN
  SUBGOAL_THEN `&0 < sc /\ sc pow 2 = c /\ sqrt(c pow 3) = sc pow 3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sc" THEN UNDISCH_TAC `&0 < c` THEN
    SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `x pow 3 = x * x * x`; SQRT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. c %% (g:B->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  USE_THEN "nc" (MP_TAC o SPECL [`p:B`; `r / sc`]) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `p:B`; `r / sc`] MFD_BALL_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "rb" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\z. c %% (g:B->real^3^3) z`; `inv c`; `y:B`; `inv(r pow 2)`]
                  RFA_MFD_RM_NORM_CMUL_LE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    UNDISCH_TAC `sc pow 2 = c` THEN UNDISCH_TAC `&0 < sc` THEN UNDISCH_TAC `&0 < r` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sqrt(c pow 3) * v` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `mfd_ball (top,atlas) (g:B->real^3^3) p (r / sc)`;
                   `v:real`; `c:real`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `kappa * r pow 3 = sc pow 3 * (kappa * (r / sc) pow 3)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sc` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

let P2BSK_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let P2BSK_CYL_NOT_COMPACT = prove
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
    ASM_SIMP_TAC[P2BSK_TWIST_NORM] THEN
    REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "inj" (DISJ_CASES_THEN (MP_TAC o SPECL [`ys:real^3`; `z:real^3`])) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P2B_THM_9_42F_ROUTE by the route described in the header.                *)
(* ------------------------------------------------------------------------- *)

let P2B_THM_9_42F_ROUTE = prove
 (`!w:B->bool. P2B_THM_9_42F_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_THM_9_42F_ROUTE_STATEMENT; P2B_THM_9_42F_STATEMENT; P2B_PROP_9_46_STATEMENT;
              P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT; P2B_SPLIT_CYL_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p946") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "rnd") ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "x1") ASSUME_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `f:real->B->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "bd")) THEN
  REWRITE_TAC[p2b_sflow] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shr")) THEN
  MP_TAC(REWRITE_RULE[p2b_ancflow; p2b_ancflow0] (ASSUME
    `p2b_ancflow kappa (top,atlas) (g:real->B->real^3^3) (&1)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn"))))))))))
    ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. s < &1 ==> smooth_manifold_atlas (top:B topology) atlas /\
                   riemannian_metric atlas ((g:real->B->real^3^3) s)`
  (LABEL_TAC "sm") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "rf" (MP_TAC o SPEC `s - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[ricci_flow_on]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a zero plane at time 1/2: the cylinder *)
  ASM_CASES_TAC `?x u v. x IN topspace top /\ ~collinear {vec 0:real^3,u,v} /\
                         mfd_sectional atlas ((g:real->B->real^3^3)(&1 / &2)) x u v = &0` THENL
   [DISJ2_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x0:B` (X_CHOOSE_THEN `u:real^3`
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
    USE_THEN "x1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `&1`; `x0:B`; `u:real^3`; `v:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u v. x IN topspace top /\ ~collinear {vec 0:real^3,u,v}
            ==> &0 < mfd_sectional atlas ((g:real->B->real^3^3)(&1 / &2)) x u v`
  (LABEL_TAC "pos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    CONJ_TAC THENL
     [USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* Prop 9.46 on the shrinker slice 2 g(1/2): compactness *)
  USE_THEN "sm" (MP_TAC o SPEC `&1 / &2`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&1 - &1 / &2)` ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_complete (top,atlas) (\x. inv(&1 - &1 / &2) %% (g:real->B->real^3^3)(&1 / &2) x) /\
    (?K. !x. x IN topspace top
             ==> mfd_rm_norm atlas (\x. inv(&1 - &1 / &2) %% g(&1 / &2) x) x <= K) /\
    (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
             ==> &0 < mfd_sectional atlas (\x. inv(&1 - &1 / &2) %% g(&1 / &2) x) x u v) /\
    p2b_rm_noncoll (kappa / &8) (top,atlas) (\x. inv(&1 - &1 / &2) %% g(&1 / &2) x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                      `(g:real->B->real^3^3)(&1 / &2)`; `inv(&1 - &1 / &2)`]
                     MFD_COMPLETE_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "cp" MATCH_MP_TAC THEN
      REAL_ARITH_TAC;
      USE_THEN "bd" (MP_TAC o SPEC `&1 / &2`) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `K0:real`)] THEN
      EXISTS_TAC `K0 / inv(&1 - &1 / &2)` THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:B topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3)(&1 / &2)`; `inv(&1 - &1 / &2)`; `x:B`;
                     `u:real^3`; `v:real^3`] RFA_MFD_SECTIONAL_CMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BSK_NONCOLL_SCALE THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BSK_SLICE_NONCOLL THEN EXISTS_TAC `&1` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[p2b_ancflow]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_space (top:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    REMOVE_THEN "p946" (MP_TAC o SPECL [`kappa / &8`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`;
                          `\x. inv(&1 - &1 / &2) %% (g:real->B->real^3^3)(&1 / &2) x`;
                          `(f:real->B->real)(&1 / &2)`]) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "shr" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
  (* a zero plane at time 0 would put a cylinder on a compact space *)
  ASM_CASES_TAC `?x u v. x IN topspace top /\ ~collinear {vec 0:real^3,u,v} /\
                         mfd_sectional atlas ((g:real->B->real^3^3)(&0)) x u v = &0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x0:B` (X_CHOOSE_THEN `u:real^3`
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `p2b_cyl_model (top,atlas) (\t. (g:real->B->real^3^3)(t + &0))` MP_TAC THENL
     [USE_THEN "x1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `&1`; `x0:B`; `u:real^3`; `v:real^3`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP P2BSK_CYL_NOT_COMPACT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* positive curvature at time 0: SHRINKER_ROUND *)
  USE_THEN "rnd" MATCH_MP_TAC THEN EXISTS_TAC `(f:real->B->real)(&0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "shr" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    CONJ_TAC THENL
     [USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Static necks pass from a flow limit at time 0                            *)
(* to the approximants.  If the limit slice g(0) has an eps-neck e at xn     *)
(* whose image has compact closure, then for large k the map phi k o e is an *)
(* eps-neck of the k-th slice at phi k xn: the chart closeness of the limit *)
(* becomes closeness of the pullbacks through e (P2B9_LCK_PARAM_DIFFEO,      *)
(* P2BL_LCK_CHART_CONVERT), one base change against the cylinder            *)
(* (P2B9S_CLOSE_TRIANGLE) and the rescaling by R(phi k xn) / (Q k R(xn))    *)
(* (LIM_CURV_KEY, LCK_DIST_RESCALE).                                         *)
(* ------------------------------------------------------------------------- *)

let P2BSK_LN_POINT = prove
 (`!m M1 D (Lc:real^3->real^3^3) Lg Lp R1 c y d1 d2.
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 m G0 G1 y <= &1 / &4
         ==> lck_dist2 m G0 (\z. G0 z + G2 z - G1 z) y <= M1 * lck_dist2 m G1 G2 y) /\
     &0 <= M1 /\ metric_field D Lc /\ metric_field D Lg /\ metric_field D Lp /\ y IN D /\
     &0 < R1 /\ &0 < c /\
     lck_dist2 m Lc (\w. R1 %% Lg w) y <= d1 /\ d1 <= &1 / &4 /\
     lck_dist2 m (\w. R1 %% Lg w) (\w. R1 %% Lp w) y <= d2
     ==> sqrt(lck_dist2 m Lc (\z. (c * R1) %% Lp z) y)
         <= c * (sqrt d1 + sqrt(M1 * &2 pow m * d2)) + abs(c - &1) * sqrt(&3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`M1:real`; `m:num`; `m:num`; `D:real^3->bool`; `Lc:real^3->real^3^3`;
                 `Lg:real^3->real^3^3`; `Lp:real^3->real^3^3`; `R1:real`; `R1:real`;
                 `y:real^3`; `d1:real`; `d2:real`] P2B9S_CLOSE_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + R1 / R1) pow m = &2 pow m` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < R1` THEN CONV_TAC REAL_FIELD;
    DISCH_TAC] THEN
  SUBGOAL_THEN `metric_field D (\w. R1 %% (Lp:real^3->real^3^3) w)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `D:real^3->bool`; `Lc:real^3->real^3^3`;
                 `\w. R1 %% (Lp:real^3->real^3^3) w`; `c:real`; `y:real^3`]
                LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; MATRIX_CMUL_ASSOC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(lck_dist2 m Lc (\w. R1 %% (Lp:real^3->real^3^3) w) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * sqrt(lck_dist2 m Lc (\w. R1 %% (Lp:real^3->real^3^3) w) y) <=
    c * (sqrt d1 + sqrt(M1 * &2 pow m * d2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2BSK_LN_CHART = prove
 (`!top atlas (top':A topology) atlas' (g0:B->real^3^3) (G:A->real^3^3) W W'
    (f:B->A) f' (e:real^3->B) D R1 Q m eta z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g0 /\ riemannian_metric atlas' G /\
     mfd_diffeo top atlas W top' atlas' W' f f' /\
     mfd_param top atlas D e /\ IMAGE e D SUBSET W /\ z IN D /\ &0 < R1 /\ &0 < Q /\
     lck_dist2 m (metric_local atlas (chart_at atlas (e z)) g0)
                 (\w. Q %% rfs_pullback atlas' (f o chart_inv (chart_at atlas (e z))) G w)
                 (SND(chart_at atlas (e z)) (e z)) < eta
     ==> lck_dist2 m (\w. R1 %% rfs_pullback atlas e g0 w)
                     (\w. (R1 * Q) %% rfs_pullback atlas' (f o e) G w) z
         <= (&1 + inv R1) pow m * eta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (\x. R1 %% (g0:B->real^3^3) x) /\
                riemannian_metric atlas' (\x. (R1 * Q) %% (G:A->real^3^3) x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_SIMP_TAC[ETA_AX; REAL_LT_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `D:real^3->bool`; `e:real^3->B`; `W:B->bool`; `W':A->bool`;
                 `f:B->A`; `f':A->B`; `\x. R1 %% (g0:B->real^3^3) x`;
                 `\x. (R1 * Q) %% (G:A->real^3^3) x`; `m:num`; `z:real^3`]
                P2B9_LCK_PARAM_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `mfd_pullback_metric atlas atlas' (f:B->A) (\x. (R1 * Q) %% (G:A->real^3^3) x) =
    (\x. (R1 * Q) %% mfd_pullback_metric atlas atlas' f G x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P2B9S_PB_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                 `W:B->bool`; `W':A->bool`; `f:B->A`; `f':A->B`;
                 `g0:B->real^3^3`; `G:A->real^3^3`; `R1:real`; `Q:real`; `m:num`;
                 `(e:real^3->B) z`] P2BL_LCK_CHART_CONVERT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `IMAGE (e:real^3->B) D SUBSET W` THEN
    UNDISCH_TAC `(z:real^3) IN D` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv R1) pow m *
              lck_dist2 m (metric_local atlas (chart_at atlas ((e:real^3->B) z)) g0)
                (\w. Q %% rfs_pullback atlas' ((f:B->A) o chart_inv (chart_at atlas (e z)))
                                       (G:A->real^3^3) w)
                (SND(chart_at atlas (e z)) (e z))` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BSK_LN_ARITH = prove
 (`!eps sd1 gap X c al.
     &0 <= sd1 /\ gap = eps - sd1 /\ &0 < gap /\ &0 <= X /\ X <= gap / &4 /\
     &0 < c /\ abs(c - &1) <= al /\ &0 <= al /\ al * (eps + &2) <= gap / &4
     ==> c * (sd1 + X) + abs(c - &1) * sqrt(&3) <= eps - gap / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `c * (sd1 + X) <= (sd1 + X) + abs(c - &1) * (sd1 + X)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(c - &1) * y <= abs(c - &1) * y ==> c * y <= y + abs(c - &1) * y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) * ((sd1 + X) + sqrt(&3)) <= al * (eps + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LE_ADD] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BSK_LIMIT_NECK = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J (top:B topology) atlas g xl W phi eps xn e.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     &0 IN J /\ riemannian_metric atlas (g (&0)) /\ eps <= &1 / &2 /\
     rfs_neck (top,atlas) (g (&0)) eps xn e /\
     compact_in top (top closure_of IMAGE e (rfs_neck_dom eps))
     ==> ?N. !k. N <= k
               ==> rfs_neck (rfs_vtop (V k) (t k),rfs_vatlas (V k) (t k))
                            (rfs_vmetric (V k) (t k)) eps (phi k xn) (phi k o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 (LABEL_TAC "vs")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))))) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0")))))))) THEN
  ABBREV_TAC `R1 = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xn` THEN
  ABBREV_TAC `m = rfs_kreg eps` THEN
  ABBREV_TAC `K = top closure_of IMAGE (e:real^3->B) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `IMAGE (e:real^3->B) (rfs_neck_dom eps) SUBSET K /\ (xn:B) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^3->B) (rfs_neck_dom eps) SUBSET topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "K" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` MP_TAC THENL
       [REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
        GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
          ALL_TAC] THEN
        ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* constants *)
  MP_TAC(SPEC `m:num` LRG_CK_BASE_CHANGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1"))) THEN
  ABBREV_TAC `d1 = max (&0) d0` THEN
  SUBGOAL_THEN `&0 <= d1 /\ d0 <= d1 /\ d1 < eps pow 2 /\ d1 <= &1 / &4 /\ sqrt d1 < eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps pow 2 /\ eps pow 2 <= &1 / &4` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    EXPAND_TAC "d1" THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `gap = eps - sqrt d1` THEN
  SUBGOAL_THEN `&0 < gap /\ &0 <= sqrt d1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `AA = M1 * &2 pow m * (&1 + inv R1) pow m` THEN
  SUBGOAL_THEN `&0 <= AA` ASSUME_TAC THENL
   [EXPAND_TAC "AA" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = (gap / &4) pow 2 / (AA + &1)` THEN
  SUBGOAL_THEN `&0 < eta /\ sqrt(AA * eta) <= gap / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = b * (a * c)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < AA + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `al = min (&1 / &2) (gap / (&4 * (eps + &2)))` THEN
  SUBGOAL_THEN `&0 < al /\ al <= &1 / &2 /\ al * (eps + &2) <= gap / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * (eps + &2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "al" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `gap / (&4 * (eps + &2)) * (eps + &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
        UNDISCH_TAC `&0 < &4 * (eps + &2)` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  (* the limit on K at time 0 and the curvature at the centre *)
  USE_THEN "lim" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `&0`; `K:B->bool`; `m:num`; `eta:real`] o
             last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `&0`;
                 `xn:B`] LIM_CURV_KEY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `al * R1`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!t q. t + &0 / q = t`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
  EXISTS_TAC `MAX k0 k1` THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= k <=> a <= k /\ b <= k`] THEN STRIP_TAC THEN
  USE_THEN "lim" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 1 (CONJUNCTS th)) THEN
                       LABEL_TAC "qpos" (el 4 (CONJUNCTS th))) THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPEC `&0`) (LABEL_TAC "cl0"))) THEN
  REWRITE_TAC[REAL_LE_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN
   `!y. y IN K
        ==> lck_dist2 m (metric_local atlas (chart_at atlas y) ((g:real->B->real^3^3) (&0)))
              (\z. (Q:num->real) k %%
                   rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#
                                   (real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) k) (t k))
                                ((phi:num->B->A) k o chart_inv (chart_at atlas y))
                                (rfs_vmetric (V k) (t k)) z)
              (SND(chart_at atlas y) y) < eta`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "cl0" (MP_TAC o SPECL [`&0`; `y:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  USE_THEN "k1" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `TMk = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k)` THEN
  ABBREV_TAC `ATk = rfs_vatlas ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)` THEN
  ABBREV_TAC `Gk = rfs_vmetric ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)` THEN
  ABBREV_TAC `Rk = mfd_scalar ATk (Gk:A->real^3^3) ((phi:num->B->A) k xn)` THEN
  ABBREV_TAC `Qk = (Q:num->real) k` THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [EXPAND_TAC "Qk" THEN USE_THEN "qpos" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas TMk (ATk:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric ATk (Gk:A->real^3^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["TMk"; "ATk"; "Gk"] THEN USE_THEN "vs" MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) k xn` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = Rk / (Qk * R1)` THEN
  SUBGOAL_THEN `&0 < Rk /\ &0 < c /\ abs(c - &1) <= al /\ (c * R1) * Qk = Rk`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(Rk / Qk - R1) <= al * R1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `R1 / &2 <= Rk / Qk` ASSUME_TAC THENL
     [SUBGOAL_THEN `al * R1 <= R1 / &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * R1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Rk` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < Rk / Qk` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL];
      SUBGOAL_THEN `Rk / (Qk * R1) - &1 = (Rk / Qk - R1) / R1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Qk` THEN UNDISCH_TAC `&0 < R1` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ];
      UNDISCH_TAC `&0 < Qk` THEN UNDISCH_TAC `&0 < R1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param TMk ATk (rfs_neck_dom eps) ((phi:num->B->A) k o (e:real^3->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                          `psi:A->B`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(eps - gap / &2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  (* (a) closeness of the pullbacks through e *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `TMk:A topology`; `ATk:((A->bool)#(A->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `Gk:A->real^3^3`; `(W:num->B->bool) k`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `e:real^3->B`; `rfs_neck_dom eps`; `R1:real`; `Qk:real`; `m:num`;
                 `eta:real`; `y:real^3`] P2BSK_LN_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "cl" MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  (* (b) one base change and the rescaling *)
  MP_TAC(ISPECL [`m:num`; `M1:real`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
                 `rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (&0))`;
                 `\w. Qk %% rfs_pullback ATk ((phi:num->B->A) k o (e:real^3->B))
                                         (Gk:A->real^3^3) w`;
                 `R1:real`; `c:real`; `y:real^3`; `d1:real`;
                 `(&1 + inv R1) pow m * eta`] P2BSK_LN_POINT) THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `TMk:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* (c) the arithmetic *)
  SUBGOAL_THEN `sqrt(M1 * &2 pow m * (&1 + inv R1) pow m * eta) <= gap / &4 /\
                &0 <= sqrt(M1 * &2 pow m * (&1 + inv R1) pow m * eta)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `M1 * &2 pow m * (&1 + inv R1) pow m * eta = AA * eta` SUBST1_TAC THENL
     [EXPAND_TAC "AA" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `sqrt d1`; `gap:real`;
                 `sqrt(M1 * &2 pow m * (&1 + inv R1) pow m * eta)`; `c:real`; `al:real`]
                P2BSK_LN_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `L = lck_dist2 m (cylinder_flow (&0))
                    (\z. Rk %% rfs_pullback ATk ((phi:num->B->A) k o (e:real^3->B))
                                            (Gk:A->real^3^3) z) y` THEN
  SUBGOAL_THEN `&0 <= L /\ sqrt L <= eps - gap / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `TMk:A topology` THEN
        ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `L = sqrt L pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Eps-necks of the cylinder model far out on the                           *)
(* end.  For rho = 2 exp(L), L = 1/(sqrt 2 eps), the map z -> p(rho z) is    *)
(* injective on rfs_neck_dom eps also in the twisted case (the twist maps    *)
(* |y| > 1 into |y| < 1), its pullback of g(0) is lam cyl(0) (dilation      *)
(* invariance), and the scalar curvature is 1/lam: an exact eps-neck whose  *)
(* image has compact closure.                                               *)
(* ------------------------------------------------------------------------- *)

let P2BSK_MODEL_NECK = prove
 (`!top atlas (g:real->B->real^3^3) eps.
     p2b_cyl_model (top,atlas) g /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas (g (&0)) /\ &0 < eps
     ==> ?xn e. rfs_neck (top,atlas) (g (&0)) eps xn e /\
                compact_in top (top closure_of IMAGE e (rfs_neck_dom eps))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "im")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "pb")))))))
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (exp(--L)) (exp L):real^3->bool` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  ABBREV_TAC `rho = &2 * exp L` THEN
  SUBGOAL_THEN `&0 < rho /\ rho * exp(--L) = &2 /\ rho * exp L = &2 * exp(&2 * L)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_EXP_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
    REWRITE_TAC[REAL_ARITH `L + --L = &0 /\ L + L = &2 * L`; REAL_EXP_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN rfs_neck_dom eps
                           ==> &2 < norm(rho % x) /\ norm(rho % x) < &2 * exp(&2 * L)`
  (LABEL_TAC "rx") THENL
   [X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `rho * exp(--L) < rho * norm(x:real^3) /\ rho * norm x < rho * exp L`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN rfs_neck_dom eps /\
                (basis 1:real^3) IN sphere(vec 0,&1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `rfs_neck_dom eps = annulus (exp(--L)) (exp L):real^3->bool` (K ALL_TAC) THEN
  ABBREV_TAC `A2 = annulus (&1) (&4 * exp(&2 * L)):real^3->bool` THEN
  (* p is a parametrization of A2 *)
  SUBGOAL_THEN `open (A2:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A2" THEN REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas A2 (p:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFP_PARAM_LOCAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN
      EXPAND_TAC "A2" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(z = rfs_twist (y:real^3))` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(z:real^3)` THEN
        ASM_SIMP_TAC[P2BSK_TWIST_NORM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `z = y \/ z = rfs_twist (y:real^3)` MP_TAC THENL
       [USE_THEN "inj" (DISJ_CASES_THEN (MP_TAC o SPECL [`y:real^3`; `z:real^3`])) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN A2` THEN EXPAND_TAC "A2" THEN
        REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(y:real^3,r) INTER A2` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL; INTER_SUBSET] THEN
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET]];
    ALL_TAC] THEN
  (* the dilation *)
  SUBGOAL_THEN `diffeomorphism_on (rfs_neck_dom eps)
                  (IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps))
                  (\x. rho % x) (\y. inv rho % y)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFP_SCALE_DIFFEO THEN ASM_REWRITE_TAC[APX_NECK_DOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps) SUBSET A2 /\
                open(IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "rx" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "A2" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      SUBGOAL_THEN `&0 < exp(&2 * L)` MP_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_SCALING THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ; APX_NECK_DOM_OPEN]];
    ALL_TAC] THEN
  ABBREV_TAC `e = (p:real^3->B) o (\x:real^3. rho % x)` THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->B)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`A2:real^3->bool`; `IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps)`;
                          `\y:real^3. inv rho % y`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pullback of g(0) is lam cyl(0) *)
  SUBGOAL_THEN `!z. z IN rfs_neck_dom eps
                    ==> rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (&0)) z =
                        lam %% cylinder_flow (&0) z`
  (LABEL_TAC "epb") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "e" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`;
                   `IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps)`; `p:real^3->B`;
                   `rfs_neck_dom eps`; `\x:real^3. rho % x`; `\y:real^3. inv rho % y`;
                   `z:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `A2:real^3->bool` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[APX_MPULLBACK_DILATE] THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0) /\ ~(rho % z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` P2BL_NECK_DOM_NZ) THEN
      ASM_SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    USE_THEN "pb" (MP_TAC o SPECL [`&0`; `rho % z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; cylinder_flow; REAL_SUB_RZERO; MATRIX_CMUL_LID;
                MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_ASSOC; NORM_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `lscalar (cylinder_flow (&0)) (basis 1:real^3) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `cylinder_flow (&0) = (\z:real^3. (&2 / norm z pow 2) %% mat 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cylinder_flow; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO;
                  MATRIX_CMUL_LID; MATRIX_CMUL_LZERO; MATRIX_ADD_RID];
      MATCH_MP_TAC LSCALAR_ROUND_CYLINDER THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((e:real^3->B) (basis 1)) =
                inv lam` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `rfs_neck_dom eps`; `e:real^3->B`;
                   `&1`; `basis 1:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_DIV_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `lscalar (\z. &1 %% rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (&0)) z)
              (basis 1) =
      lscalar (\z. lam %% cylinder_flow (&0) z) (basis 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; MATRIX_CMUL_LID] THEN
      REPEAT STRIP_TAC THEN USE_THEN "epb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`; `lam:real`; `basis 1:real^3`]
                  LSCALAR_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(e:real^3->B) (basis 1)`; `e:real^3->B`] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_neck; rfs_close_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
          (\y. inv lam %% rfs_pullback atlas (e:real^3->B) ((g:real->B->real^3^3) (&0)) y) y =
        lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (cylinder_flow (&0)) y`
      SUBST1_TAC THENL
       [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
        ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN USE_THEN "epb" (fun th -> ASM_SIMP_TAC[th]) THEN
        REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID];
        REWRITE_TAC[P2BL_LCK_DIST2_REFL; REAL_LE_REFL]]];
    ALL_TAC] THEN
  (* the closure of the image is compact *)
  ABBREV_TAC `sh = cball(vec 0:real^3,&2 * exp(&2 * L)) DIFF ball(vec 0,&2)` THEN
  SUBGOAL_THEN `compact (sh:real^3->bool) /\ sh SUBSET A2 /\
                IMAGE (\x:real^3. rho % x) (rfs_neck_dom eps) SUBSET sh`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sh" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      EXPAND_TAC "A2" THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      SUBGOAL_THEN `&0 < exp(&2 * L)` MP_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "rx" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->B) sh)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `A2:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE (p:real^3->B) sh` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXPAND_TAC "e" THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The core of Cor 9.53.  The hypothesis "x2p" is X2                         *)
(* (P2B_CYL_AT_INFINITY_STATEMENT, with its conjunct                         *)
(* (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g')).                  *)
(* Unbounded |Rm| on a slice gives points pp k with                          *)
(* R(pp k) d(p,pp k)^2 -> infinity, X2 a cylinder limit along q k with       *)
(* R(q k) -> infinity, model necks far out in the limit become eps-necks of *)
(* the slice centred at phi k xn with R(phi k xn) -> infinity, against      *)
(* Prop 2.19 (sep).                                                          *)
(* ------------------------------------------------------------------------- *)

let P2BSK_COR_9_53_CORE = prove
 (`!w:B->bool.
     (!kappa top atlas (g:real->B->real^3^3) b s0 p pp.
        p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\ p IN topspace top /\
        (!k. pp k IN topspace top) /\
        (!M. ?N. !k. N <= k
                     ==> M < mfd_scalar atlas (g s0) (pp k) *
                             mfd_dist (top,atlas) (g s0) p (pp k) pow 2)
        ==> ?sub q (top':B topology) atlas' g' xl W phi.
               p3_subseq sub /\
               (!k. q k IN topspace top /\
                    mfd_scalar atlas (g s0) (pp (sub k)) <= mfd_scalar atlas (g s0) (q k)) /\
               (!M. ?N. !k. N <= k
                            ==> M < mfd_scalar atlas (g s0) (q k) *
                                    mfd_dist (top,atlas) (g s0) p (q k) pow 2) /\
               p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) q (\k. s0)
                                   (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                                   (top',atlas') g' xl W phi /\
               (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
               p2b_cyl_model (top',atlas') g') /\
     P2_PROP_2_19_SEP_STATEMENT w
     ==> P2B_COR_9_53_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_53_STATEMENT; P2_PROP_2_19_SEP_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x2p")
    (X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p219")))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s:real`] THEN
  STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[p2b_ancflow; p2b_ancflow0; p2b_ksep] (ASSUME
    `p2b_ancflow kappa (top,atlas) (g:real->B->real^3^3) b`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn"))))))))))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!tau. tau < b ==> smooth_manifold_atlas (top:B topology) atlas /\
                      riemannian_metric atlas ((g:real->B->real^3^3) tau)`
  (LABEL_TAC "sm") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN USE_THEN "rf" (MP_TAC o SPEC `tau - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[ricci_flow_on]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sm" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [USE_THEN "cp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* by contradiction: unbounded curvature *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "unb" o
             REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  SUBGOAL_THEN `!K. ?x. x IN topspace top /\ K < mfd_scalar atlas ((g:real->B->real^3^3) s) x`
  (LABEL_TAC "runb") THENL
   [X_GEN_TAC `K:real` THEN USE_THEN "unb" (MP_TAC o SPEC `K / &2`) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `x:B` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `x:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a base point and the bound of R on the unit ball *)
  FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `~(topspace (top:B topology) = {})`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `?R1. !y. y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s) p (&1)
                         ==> mfd_scalar atlas (g s) y <= R1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `p:B`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3) s) p (&1)`; `&1`]
                  P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `euclideanreal`;
                   `mfd_scalar atlas ((g:real->B->real^3^3) s)`;
                   `top closure_of mfd_ball (top,atlas) ((g:real->B->real^3^3) s) p (&1)`]
                  IMAGE_COMPACT_IN) THEN
    ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B0:real` o CONJUNCT1) THEN EXISTS_TAC `B0:real` THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN top closure_of mfd_ball (top,atlas) ((g:real->B->real^3^3) s) p (&1)`
    MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t (y:B). s SUBSET t /\ y IN s ==> y IN t`) THEN
      EXISTS_TAC `mfd_ball (top,atlas) ((g:real->B->real^3^3) s) p (&1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `p:B`; `&1`] MFD_BALL_OPEN) THEN
      ASM_SIMP_TAC[OPEN_IN_SUBSET];
      ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  (* the points pp k *)
  SUBGOAL_THEN `?pp. (!k. pp k IN topspace top) /\
                     (!k. max R1 (&k) < mfd_scalar atlas ((g:real->B->real^3^3) s) (pp k))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FORALL_AND_THM; GSYM SKOLEM_THM] THEN GEN_TAC THEN
    USE_THEN "runb" (MP_TAC o SPEC `max R1 (&k)`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &k < mfd_scalar atlas ((g:real->B->real^3^3) s) (pp k) *
                         mfd_dist (top,atlas) (g s) p (pp k) pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&1 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) s) p ((pp:num->B) k)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(pp:num->B) k` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
      ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (p:B) ((pp:num->B) k)` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "real_max")) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_max")) (concl th))) THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) (pp(k:num)) * &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* X2 with the flow facts of the limit *)
  USE_THEN "x2p" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                  `atlas:((B->bool)#(B->real^3))->bool`;
                                  `g:real->B->real^3^3`; `b:real`; `s:real`; `p:B`;
                                  `pp:num->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `M:real` THEN
    MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&k` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "qk")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim")
      (CONJUNCTS_THEN2 (LABEL_TAC "fu") ASSUME_TAC))))))))))))) THEN
  SUBGOAL_THEN `hausdorff_space (top':B topology) /\ smooth_manifold_atlas top' atlas' /\
                riemannian_metric atlas' ((g':real->B->real^3^3) (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[el 0 (CONJUNCTS th); el 1 (CONJUNCTS th)]) THEN
    USE_THEN "fu" (MP_TAC o SPEC `--(&1)`) THEN
    REWRITE_TAC[rfs_flow_upto; REAL_ARITH `--(&1) < &0`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* a model neck in the limit and its transfer *)
  ABBREV_TAC `eps = min eps1 (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= eps1 /\ eps <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `eps:real`] P2BSK_MODEL_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xn:B` (X_CHOOSE_THEN `e:real^3->B` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `(xn:B) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`; `sphere(vec 0:real^3,&1)`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n tau. ~(topspace(rfs_vtop ((\k:num. rfs_flow_view (top,atlas) {s | s < b}
                                   (g:real->B->real^3^3)) n) tau) = {})
            ==> smooth_manifold_atlas (rfs_vtop ((\k:num. rfs_flow_view (top,atlas)
                                                 {s | s < b} g) n) tau)
                                      (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas)
                                                 {s | s < b} g) n) tau) /\
                riemannian_metric (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas)
                                                 {s | s < b} g) n) tau)
                                  (rfs_vmetric ((\k:num. rfs_flow_view (top,atlas)
                                                 {s | s < b} g) n) tau)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `tau:real`] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN DISCH_TAC THEN
    USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
                 `q:num->B`; `\k:num. (s:real)`; `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) s) ((q:num->B) k)`;
                 `{s:real | s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `eps:real`; `xn:B`; `e:real^3->B`]
                P2BSK_LIMIT_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "necks")) THEN
  (* Prop 2.19 bounds R at neck centres *)
  USE_THEN "p219" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `(g:real->B->real^3^3) s`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `BB:real` (LABEL_TAC "bnd"))] THEN
  (* the curvature at the centres grows like R(q k) *)
  ABBREV_TAC `R2 = mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) xn` THEN
  MP_TAC(ISPECL [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
                 `q:num->B`; `\k:num. (s:real)`; `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) s) ((q:num->B) k)`;
                 `{s:real | s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `&0`; `xn:B`] LIM_CURV_KEY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `R2 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM;
              REAL_ARITH `!t q. t + &0 / q = t`] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "curv")) THEN
  MP_TAC(SPEC `&2 * max (&0) BB / R2` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  ABBREV_TAC `k = MAX (MAX N1 N2) (N3 + 1)` THEN
  SUBGOAL_THEN `N1 <= k /\ N2 <= k /\ N3 + 1 <= k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "necks" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "bnd" (MP_TAC o C MATCH_MP th)) THEN DISCH_TAC THEN
  USE_THEN "curv" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s) ((q:num->B) k)` THEN
  ABBREV_TAC `X = mfd_scalar atlas ((g:real->B->real^3^3) s) ((phi:num->B->B) k xn)` THEN
  SUBGOAL_THEN `&k <= Qk` ASSUME_TAC THENL
   [USE_THEN "qk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(ASSUME_TAC o SPEC `(sub:num->num) k` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_max")) (concl th))) THEN
    MP_TAC(SPEC `sub:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * max (&0) BB / R2 < Qk` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&k` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * max (&0) BB / R2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `R2 / &2 * Qk <= X` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `max (&0) BB < R2 / &2 * Qk` ASSUME_TAC THENL
   [SUBGOAL_THEN `R2 / &2 * (&2 * max (&0) BB / R2) = max (&0) BB` (SUBST1_TAC o SYM) THENL
     [UNDISCH_TAC `&0 < R2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* P2B_COR_9_53_ROUTE.  The unfolded X2 is literally the first hypothesis of *)
(* P2BSK_COR_9_53_CORE.                                                      *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_53_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_53_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_53_ROUTE_STATEMENT; P2B_CYL_AT_INFINITY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC P2BSK_COR_9_53_CORE THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

