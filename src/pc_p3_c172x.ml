(* ========================================================================= *)
(* Unit pc_p3_c172x: assembly of MT Lemma 17.2 from part A                  *)
(* (the first bad time, pc_p3_c172a), part B (caps and components,          *)
(* pc_p3_c172b), part C (strong necks, subcase (i), pc_p3_c172c) and the     *)
(* statement of part D (subcase (ii) of MT p. 397: the sub-neck does not    *)
(* persist before ts - 1/Q, and x lies in the core of a (C,eps)-cap).        *)
(*                                                                         *)
(* The part D statement and the openness property at the                    *)
(* first bad time.                                                           *)
(* ========================================================================= *)

needs "src/pc_p3_c172c.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_PART_D_STATEMENT = new_definition
 `P3H_PART_D_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !eps g0 A0. &0 < eps /\ eps <= eps1 /\ p3_std_initial g0 A0
        ==> ?C1. &1 < C1 /\
              !C hf md.
                 C1 <= C /\ p3_hfun C hf /\ p3_modulus md
                 ==> !i rs ks ds r'.
                       1 <= i /\ rs 0 = eps /\
                       p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
                       &0 < r' /\ r' <= rs i
                       ==> ?dlt. &0 < dlt /\
                             !rs' ks' dd (hs:(A)rfs_history) ts x e p1.
                                rs' (SUC i) = r' /\
                                p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt
                                            (rs',ks',dd) hs /\
                                p3_T i <= ts /\ ts < rfs_horizon hs /\
                                rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts)
                                  C eps (p3_stepf rs') /\
                                inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                                rfs_strong_neck (rfs_view hs) eps x ts e /\
                                &0 < p1 /\ p1 < &1 /\
                                ~(?eta0. &0 < eta0 /\
                                         rfs_persists (rfs_view hs)
                                           (IMAGE e (rfs_neck_dom (eps / p1)))
                                           (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0)
                                           ts)
                                ==> ?U Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                                  (rfs_metric_at hs ts) C eps U Y /\
                                          x IN Y`;;

(* Openness at a time ts of a canonical neighbourhood at x, given the part D *)
(* conclusion for strong necks at x: all (y,s) near (x,ts), s >= ts, have    *)
(* strong canonical neighbourhoods.                                          *)

let P3H_OPEN_HIST = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps ts x.
       rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 <= ts /\ ts < rfs_horizon hs /\ x IN topspace(rfs_top_at hs ts) /\
       &0 < rfs_vscalar (rfs_view hs) ts x /\
       p3_canon_at (rfs_view hs) C eps x ts /\
       (!e p1. rfs_strong_neck (rfs_view hs) eps x ts e /\ &0 < p1 /\ p1 < &1 /\
               ~(?eta0. &0 < eta0 /\
                        rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom (eps / p1)))
                          (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts)
               ==> ?U Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                 (rfs_metric_at hs ts) C eps U Y /\ x IN Y)
       ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                 !s y. ts <= s /\ s < ts + d /\ y IN N
                       ==> p3_canon_at (rfs_view hs) C eps y s`,
  MP_TAC(INST_TYPE [`:A`,`:A`] P3H_OPEN_STATIC_HIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  EXISTS_TAC `min e0 (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))))))))))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k ts) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
    ASM_REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U. ((?Y. rfs_cap (rfs_top_at hs ts,rfs_atlas_at hs ts)
                       (rfs_metric_at (hs:(A)rfs_history) ts) C eps U Y /\ x IN Y) \/
         (x IN U /\ rfs_c_component (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                    (rfs_metric_at hs ts) C U) \/
         (x IN U /\ rfs_round_component (rfs_top_at hs ts,rfs_atlas_at hs ts)
                                        (rfs_metric_at hs ts) eps U))
        ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                  !s y. ts <= s /\ s < ts + d /\ y IN N
                        ==> p3_canon_at (rfs_view hs) C eps y s`
  (LABEL_TAC "stat") THENL
   [X_GEN_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "st" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `k:num`;
                                   `ts:real`; `x:A`; `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N:A->bool`; `min d (hs_time (hs:(A)rfs_history) (k + 1) - ts)`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `U:A->bool` o REWRITE_RULE[p3_canon_at] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canon_at")) (concl th) &&
    not (is_forall (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rfs_view] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_canonical"))
      (concl th))) THEN
  REWRITE_TAC[rfs_strong_canonical] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_MESON_TAC[];
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `rfs_strong_neck (rfs_view (hs:(A)rfs_history)) eps x ts e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_view]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `eps:real`; `ts:real`; `x:A`; `e:real^3->A`]
                P3H_NECK_OPEN_HIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")))) THEN
  ASM_CASES_TAC
   `?eta0. &0 < eta0 /\
           rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE e (rfs_neck_dom (eps / p1)))
             (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts` THENL
   [USE_THEN "nk" (MP_TAC o C MP (ASSUME
      `?eta0. &0 < eta0 /\
              rfs_persists (rfs_view (hs:(A)rfs_history)) (IMAGE e (rfs_neck_dom (eps / p1)))
                (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:A->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
        (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `e':real^3->A` o CONJUNCT2) THEN
    REWRITE_TAC[p3_canon_at] THEN EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `rfs_strong_neck (rfs_view (hs:(A)rfs_history)) eps y s e'` THEN
    REWRITE_TAC[rfs_view; rfs_strong_canonical] THEN DISCH_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `e':real^3->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`e:real^3->A`; `p1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)) THEN
  USE_THEN "stat" MATCH_MP_TAC THEN EXISTS_TAC `U':A->bool` THEN DISJ1_TAC THEN
  EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[]);;

