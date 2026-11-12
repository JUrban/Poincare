(* ========================================================================= *)
(* pc_p2b_shrinkfin: the final-slice routes (MT p. 229 applies Cor 9.53, a   *)
(* statement for t < 0, to the final slice t = 0 of the Thm 9.64 limit; the  *)
(* statements are in pc_p2b_chainstmts).                                     *)
(*   P2B_CYL_AT_INFINITY_FINAL_ROUTE  X0_FINAL /\ SPLIT_ROUND /\ FLAT_FORWARD *)
(*                                    ==> X2_FINAL (FLAT_FORWARD unused);    *)
(*   P2B_COR_9_53_FINAL_ROUTE         X2_FINAL /\ PROP_2_19_SEP              *)
(*                                    ==> COR_9_53_FINAL.                    *)
(* X2_FINAL is the P2BX2_CYL_BODY argument (pc_p2b_x2) with X0_FINAL: the  *)
(* limit is in the class on s < 0 (P2BX2_LIMIT_CLASS), p2b_lorient passes  *)
(* to it along p2b_kview with base times 0, SPLIT_ROUND and                *)
(* P2BX2_MODEL_AT_ZERO give the model.  COR_9_53_FINAL is the argument of    *)
(* P2BSK_COR_9_53_CORE (pc_p2b_shrinkcl) with the picking slice 0            *)
(* (P2BSK_LIMIT_NECK, P2BSK_MODEL_NECK reused); the non-flatness hypothesis  *)
(* at (x0,0) is unused.                                                      *)
(* ========================================================================= *)

needs "src/pc_p2b_shrinkcl.ml";;
needs "src/pc_p2b_x2.ml";;
needs "src/pc_p2b_lim.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* X2 at the final slice.  The P2BX2_CYL_BODY argument with                 *)
(* X0_FINAL: the X0_FINAL limit is in the class on s < 0                    *)
(* (P2BX2_LIMIT_CLASS), p2b_lorient passes to it along p2b_kview with base  *)
(* times 0, and SPLIT_ROUND with P2BX2_MODEL_AT_ZERO gives the model.       *)
(* ------------------------------------------------------------------------- *)

let P2BSK_LIMIT_LORIENT_FINAL = prove
 (`!top atlas (g:real->B->real^3^3) q Q (top':B topology) atlas' g' xl W phi.
     hausdorff_space top /\ p2b_ksep top atlas /\ smooth_manifold_atlas top atlas /\
     p2c_flow_limit_with (\k. p2b_kview (top,atlas) g) q (\k. &0) Q
                         {s | s <= &0} (top',atlas') g' xl W phi
     ==> p2b_lorient top' atlas'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2b_ksep (top':B topology) atlas'` MP_TAC THENL
   [MATCH_MP_TAC P2B_KSEP_LIMIT_DIRECT THEN
    MAP_EVERY EXISTS_TAC [`\k:num. top:B topology`;
                          `\k:num. atlas:((B->bool)#(B->real^3))->bool`;
                          `\k:num. (g:real->B->real^3^3)`; `q:num->B`;
                          `\k:num. &0`; `Q:num->real`; `g':real->B->real^3^3`; `xl:B`;
                          `{s:real | s <= &0}`] THEN
    ASM_REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
    MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->B`] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[p2b_ksep]]);;

let P2BSK_CYL_FINAL_BODY = prove
 (`!w:B->bool.
     P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w ==> P2B_CYL_AT_INFINITY_FINAL_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT; P2B_SPLIT_ROUND_STATEMENT; P2B_CYL_AT_INFINITY_FINAL_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x0") (LABEL_TAC "sr")) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`; `pp:num->B`] THEN
  STRIP_TAC THEN
  USE_THEN "x0" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                                 `p:B`; `pp:num->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC))))))))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(REWRITE_RULE[p2b_ancflow0c] (ASSUME
    `p2b_ancflow0c kappa (top,atlas) (g:real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_flow_upto")) (concl th) &&
      can (find_term (fun t -> t = `g:real->B->real^3^3`)) (concl th))) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top':B topology,atlas') g' (&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] P2BX2_LIMIT_CLASS) THEN
    MAP_EVERY EXISTS_TAC [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`;
                          `q:num->B`; `\k:num. &0`;
                          `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((q:num->B) k)`;
                          `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[GSYM p2b_kview] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_lorient (top':B topology) atlas'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSK_LIMIT_LORIENT_FINAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `q:num->B`;
                          `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((q:num->B) k)`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                          `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_gsplit (top':B topology,atlas') g' {s | s < &0} X` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_gsplit (top':B topology,atlas') g' {s | s <= &0} X` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX2_MODEL_AT_ZERO THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "sr" (MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                                 `atlas':((B->bool)#(B->real^3))->bool`;
                                 `g':real->B->real^3^3`; `&0`; `X:B->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* The X2_FINAL route; P2B_REQ_FLAT_FORWARD_STATEMENT is not used. *)

let P2B_CYL_AT_INFINITY_FINAL_ROUTE = prove
 (`!w:B->bool. P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2BSK_CYL_FINAL_BODY THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Cor 9.53 core at the final slice t = 0.  The argument of              *)
(* P2BSK_COR_9_53_CORE (pc_p2b_shrinkcl) with the picking slice 0, the view  *)
(* p2b_kview and base times 0; slice facts from rfs_flow_upto.               *)
(* ------------------------------------------------------------------------- *)

let P2BSK_COR_9_53_FINAL_CORE = prove
 (`!w:B->bool. P2B_CYL_AT_INFINITY_FINAL_STATEMENT w /\ P2_PROP_2_19_SEP_STATEMENT w
               ==> P2B_COR_9_53_FINAL_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_CYL_AT_INFINITY_FINAL_STATEMENT; P2B_COR_9_53_FINAL_STATEMENT; P2_PROP_2_19_SEP_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x2p")
    (X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p219")))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x0:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (CONJUNCTS_THEN2 (LABEL_TAC "cp") (CONJUNCTS_THEN2 (LABEL_TAC "sec")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (CONJUNCTS_THEN2 (LABEL_TAC "kn")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `~(topspace (top:B topology) = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sphere_sep (top:B topology) atlas` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2b_ksep]; ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ancflow0c kappa (top,atlas) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p2b_ancflow0c] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. tau <= &0 ==> smooth_manifold_atlas (top:B topology) atlas /\
                        riemannian_metric atlas ((g:real->B->real^3^3) tau)`
  (LABEL_TAC "sm") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN USE_THEN "upto" (MP_TAC o SPEC `tau - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `tau = &0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sm" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [USE_THEN "cp" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* by contradiction: unbounded curvature *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "unb" o
             REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  SUBGOAL_THEN `!K. ?x. x IN topspace top /\ K < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x`
  (LABEL_TAC "runb") THENL
   [X_GEN_TAC `K:real` THEN USE_THEN "unb" (MP_TAC o SPEC `K / &2`) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `x:B` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `x:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a base point and the bound of R on the unit ball *)
  FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `~(topspace (top:B topology) = {})`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `?R1. !y. y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&1)
                         ==> mfd_scalar atlas (g (&0)) y <= R1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&1)`; `&1`]
                  P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `euclideanreal`;
                   `mfd_scalar atlas ((g:real->B->real^3^3) (&0))`;
                   `top closure_of mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&1)`]
                  IMAGE_COMPACT_IN) THEN
    ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B0:real` o CONJUNCT1) THEN EXISTS_TAC `B0:real` THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN top closure_of mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&1)`
    MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t (y:B). s SUBSET t /\ y IN s ==> y IN t`) THEN
      EXISTS_TAC `mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) p (&1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (&0)`; `p:B`; `&1`] MFD_BALL_OPEN) THEN
      ASM_SIMP_TAC[OPEN_IN_SUBSET];
      ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  (* the points pp k *)
  SUBGOAL_THEN `?pp. (!k. pp k IN topspace top) /\
                     (!k. max R1 (&k) < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) (pp k))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FORALL_AND_THM; GSYM SKOLEM_THM] THEN GEN_TAC THEN
    USE_THEN "runb" (MP_TAC o SPEC `max R1 (&k)`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &k < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) (pp k) *
                         mfd_dist (top,atlas) (g (&0)) p (pp k) pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&1 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p ((pp:num->B) k)`
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
    EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) (pp(k:num)) * &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* X2 with the flow facts of the limit *)
  USE_THEN "x2p" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                  `atlas:((B->bool)#(B->real^3))->bool`;
                                  `g:real->B->real^3^3`; `p:B`; `pp:num->B`]) THEN
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
   `!n tau. ~(topspace(rfs_vtop ((\k:num. p2b_kview (top,atlas)
                                   (g:real->B->real^3^3)) n) tau) = {})
            ==> smooth_manifold_atlas (rfs_vtop ((\k:num. p2b_kview (top,atlas) g) n) tau)
                                      (rfs_vatlas ((\k:num. p2b_kview (top,atlas) g) n) tau) /\
                riemannian_metric (rfs_vatlas ((\k:num. p2b_kview (top,atlas) g) n) tau)
                                  (rfs_vmetric ((\k:num. p2b_kview (top,atlas) g) n) tau)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `tau:real`] THEN
    REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM;
              REAL_LE_REFL] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN DISCH_TAC THEN
    USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`;
                 `q:num->B`; `\k:num. &0`; `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((q:num->B) k)`;
                 `{s:real | s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `eps:real`; `xn:B`; `e:real^3->B`]
                P2BSK_LIMIT_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM;
              REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "necks")) THEN
  (* Prop 2.19 bounds R at neck centres *)
  USE_THEN "p219" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `(g:real->B->real^3^3) (&0)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_THEN(X_CHOOSE_THEN `BB:real` (LABEL_TAC "bnd"))] THEN
  (* the curvature at the centres grows like R(q k) *)
  ABBREV_TAC `R2 = mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) xn` THEN
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`;
                 `q:num->B`; `\k:num. &0`; `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((q:num->B) k)`;
                 `{s:real | s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `&0`; `xn:B`] LIM_CURV_KEY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `R2 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM;
              REAL_LE_REFL; REAL_ARITH `!t q. t + &0 / q = t`] THEN
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
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((q:num->B) k)` THEN
  ABBREV_TAC `X = mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((phi:num->B->B) k xn)` THEN
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

(* The COR_9_53_FINAL route. *)

let P2B_COR_9_53_FINAL_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_53_FINAL_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_53_FINAL_ROUTE_STATEMENT; P2BSK_COR_9_53_FINAL_CORE]);;

