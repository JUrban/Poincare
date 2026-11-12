(* ========================================================================= *)
(* pc_p2a_defs4: admissible curves with singular corners.  The history       *)
(* bridge clause rfs_L_adm ==> p2a_adm (clause 5 of                          *)
(* P2A_HIST_VIEW_STATEMENT) is false: at a trivial event (no necks, nothing  *)
(* discarded) the old and new stages have the same atlas, so p2a_pc1 asks    *)
(* for a one-sided derivative at the event time from the old side, which     *)
(* rfs_st_curve does not give (teeth theorem P2AX_TEETH_PC1 at the end of    *)
(* this file).  Here: p2a_pc1x (C^1 off a finite set P, nothing at P),       *)
(* p2a_admx, p2a_minx; P2A_HIST_VIEW_X with clause 5 concluding p2a_admx     *)
(* (all other clauses unchanged); the x-form of the Lemma 7.2 view statement *)
(* (sequences of p2a_admx curves); the bridges to the Part 3 statements      *)
(* against these forms.                                                      *)
(* The first part: definitions and the inclusions between the curve classes. *)
(* ========================================================================= *)

needs "src/pc_p2a_defs3.ml";;

prioritize_real();;
type_invention_error := true;;

let p2a_pc1x = new_definition
 `p2a_pc1x (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (gamma:real->A) (a:real) (b:real)
           (P:real->bool) <=>
    FINITE P /\
    !s0 c. a < s0 /\ s0 <= b /\ ~(s0 IN P) /\ c IN p2a_vatlas V (tt - s0) /\
           gamma s0 IN FST c
           ==> ?d. &0 < d /\
                   continuously_differentiable 1
                     {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                          a < drop s /\ drop s <= b /\
                          p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                          gamma(drop s) IN FST c}
                     (\s. SND c (gamma(drop s)))`;;

let p2a_admx = new_definition
 `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    &0 < b /\ gamma(&0) = x /\
    (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
    (!tau0 O. &0 <= tau0 /\ tau0 <= b /\ open_in (p2a_vtop V (tt - tau0)) O /\
              gamma tau0 IN O
              ==> ?d. &0 < d /\
                      !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d
                            ==> gamma tau IN O) /\
    (?P. p2a_pc1x V tt gamma (&0) b P) /\
    (!tau. &0 < tau /\ tau <= b ==> p2a_smooth V (gamma tau) (tt - tau)) /\
    p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b]`;;

let p2a_minx = new_definition
 `p2a_minx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    p2a_admx V tt x b gamma /\
    !gamma'. p2a_admx V tt x b gamma' /\ gamma' b = gamma b
             ==> p2a_L_length V tt gamma b <= p2a_L_length V tt gamma' b`;;

let P2AX_PC1_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma a b P.
     p2a_pc1 V tt gamma a b P ==> p2a_pc1x V tt gamma a b P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1; p2a_pc1x] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let P2AX_ADM_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma.
     p2a_adm V tt x b gamma ==> p2a_admx V tt x b gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm; p2a_admx] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `P:real->bool` THEN
  MATCH_MP_TAC P2AX_PC1_IMP THEN ASM_REWRITE_TAC[]);;

let P2AX_ADM1_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma.
     p2a_adm1 V tt x b gamma ==> p2a_admx V tt x b gamma`,
  SIMP_TAC[p2a_adm1; P2AX_ADM_IMP]);;

(* An admx curve satisfying the corner conditions of p2a_pc1 is p2a_adm.    *)

let P2AX_ADMX_ADM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma P.
     p2a_admx V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b P
     ==> p2a_adm V tt x b gamma`,
  REWRITE_TAC[p2a_admx; p2a_adm] THEN MESON_TAC[]);;

(* A minimizer among admx curves that is p2a_adm is a minimizer.            *)

let P2AX_MINX_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b gamma.
     p2a_minx V tt x b gamma /\ p2a_adm V tt x b gamma
     ==> p2a_min V tt x b gamma`,
  REWRITE_TAC[p2a_minx; p2a_min] THEN MESON_TAC[P2AX_ADM_IMP]);;

(* ------------------------------------------------------------------------- *)
(* P2A_HIST_VIEW_X (clause 5 concludes p2a_admx; the other 12 clauses are    *)
(* those of P2A_HIST_VIEW_STATEMENT), the x-form of the Lemma 7.2 view       *)
(* statement (the sequence may consist of p2a_admx curves), the route        *)
(* obligations against them, and the bridges to the Part 3 statements (the   *)
(* proofs of P2A_T1_FIX, P2A_T2_FIX, P2A_T3_FIX with these forms).           *)
(* ------------------------------------------------------------------------- *)

let P2A_HIST_VIEW_X_STATEMENT = new_definition
 `P2A_HIST_VIEW_X_STATEMENT (u:A->bool) <=>
    !hs:(A)rfs_history.
       rfs_history_ok hs
       ==> p2a_svs (rfs_view hs) /\
           (!t. compact_space (rfs_top_at hs t)) /\
           (!W a b. &0 <= a /\ a < b /\ b < rfs_horizon hs /\
                    rfs_persists (rfs_view hs) W a b
                    ==> p2a_region (rfs_view hs) W a b) /\
           (!y t. &0 < t /\ rfs_smooth_pt hs y t ==> p2a_smooth (rfs_view hs) y t) /\
           (!tt x b gamma. b < tt /\ rfs_L_adm hs tt x b gamma
                           ==> p2a_admx (rfs_view hs) tt x b gamma) /\
           (!tt x b gamma K. b < tt /\ rfs_L_adm hs tt x b gamma /\
                             p3_st_compact hs K /\
                             (!tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau))
                             ==> p2a_bsmooth (rfs_view hs) x tt) /\
           (!tt x b gamma. b < tt /\ p2a_adm (rfs_view hs) tt x b gamma
                           ==> p2a_Lx (rfs_view hs) tt x b (gamma b) <=
                               p2a_L_length (rfs_view hs) tt gamma b) /\
           (!tt x b gamma. b < tt /\ p2a_adm1 (rfs_view hs) tt x b gamma
                           ==> rfs_L_adm hs tt x b gamma) /\
           (!tt x b gamma. b < tt /\ rfs_min_Lgeod hs tt x b gamma
                           ==> p2a_min (rfs_view hs) tt x b gamma) /\
           (!tt x b gamma. b < tt /\ p2a_min (rfs_view hs) tt x b gamma /\
                           p2a_pc1 (rfs_view hs) tt gamma (&0) b {}
                           ==> rfs_min_Lgeod hs tt x b gamma) /\
           (!tt x b q. b < tt /\ (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q)
                       ==> rfs_Lx hs tt x b q = p2a_Lx (rfs_view hs) tt x b q) /\
           (!K. p3_st_compact hs K ==> p2a_cbox (rfs_view hs) K) /\
           (!U a b. p3_st_open hs U a b ==> p2a_st_open (rfs_view hs) U a b)`;;

(* Clause (c) also gives the end point gamma tau0 = q, as                 *)
(* P2_LEMMA_7_2_STATEMENT does.                                           *)
let P2A_LEMMA_7_2_VIEW_X_STATEMENT = new_definition
 `P2A_LEMMA_7_2_VIEW_X_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     x tt tau0 K gs Lb.
       p2a_svs V /\ p2a_atlas_lc V /\
       &0 < tau0 /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
       p2a_cbox V K /\
       (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
            !tau. &0 < tau /\ tau <= tau0 ==> gs n tau IN K (tt - tau))
       ==> ?sub gamma K'.
              p3_subseq sub /\ p2a_cbox V K' /\ gamma (&0) = x /\
              (!tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K' (tt - tau)) /\
              (!eta. &0 < eta
                     ==> (?gamma'. p2a_adm1 V tt x tau0 gamma' /\ gamma' tau0 = gamma tau0 /\
                                   (!tau. &0 < tau /\ tau <= tau0
                                          ==> gamma' tau IN K' (tt - tau)) /\
                                   ?N. !n. N <= n
                                       ==> p2a_L_length V tt gamma' tau0 <=
                                           p2a_L_length V tt (gs (sub n)) tau0 + eta) /\
                         (?N. !n. N <= n
                              ==> !tau. &0 <= tau /\ tau <= tau0
                                        ==> mfd_dist (rfs_vtop V (tt - tau),
                                                      rfs_vatlas V (tt - tau))
                                                     (rfs_vmetric V (tt - tau))
                                                     (gs (sub n) tau) (gamma tau) < eta)) /\
              !q. (!n. gs n tau0 = q) /\
                  (!gamma' eta. p2a_adm V tt x tau0 gamma' /\ gamma' tau0 = q /\ &0 < eta
                                ==> ?N. !n. N <= n
                                        ==> p2a_L_length V tt (gs n) tau0 <=
                                            p2a_L_length V tt gamma' tau0 + eta)
                  ==> p2a_min V tt x tau0 gamma /\ p2a_pc1 V tt gamma (&0) tau0 {} /\
                      gamma tau0 = q`;;

let P2AX_LEMMA_7_2_VIEW_X_IMP_FIX = prove
 (`!u:A->bool. P2A_LEMMA_7_2_VIEW_X_STATEMENT u ==> P2A_LEMMA_7_2_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2A_LEMMA_7_2_VIEW_X_STATEMENT; P2A_LEMMA_7_2_VIEW_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`K:real->A->bool`; `Lb:real`] THEN
  ASM_SIMP_TAC[P2AX_ADM_IMP]);;

(* O3 against HIST_VIEW_X (P3_LEMMA_14_11 from pc_p3_s14glue; the corner    *)
(* smoothing and the regularity of p2a_minx curves from pc_p2a_smx and      *)
(* pc_p2a_rgx).                                                             *)
let P2A_ROUTE_BRIDGE_X_STATEMENT = new_definition
 `P2A_ROUTE_BRIDGE_X_STATEMENT (u:A->bool) <=>
    P2A_REQ_RLOWER_STATEMENT u ==> P2A_HIST_VIEW_X_STATEMENT u`;;

(* O10 against the x-form of the Lemma 7.2 view statement.                  *)
let P2A_ROUTE_LEMMA_7_2_X_STATEMENT = new_definition
 `P2A_ROUTE_LEMMA_7_2_X_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_SMOOTHING_FIX_STATEMENT u /\
    P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_LGEOD_FIX_STATEMENT u
    ==> P2A_LEMMA_7_2_VIEW_X_STATEMENT u`;;

let P2AX_T1 = prove
 (`!u:A->bool. P2A_THM_8_1_VIEW_FIX_STATEMENT u /\ P2A_HIST_VIEW_X_STATEMENT u
               ==> P2_THM_8_1_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_THM_8_1_VIEW_FIX_STATEMENT; P2_THM_8_1_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`taub:real`; `l0:real`; `V0:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`taub:real`; `l0:real`; `V0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kappa:real` THEN
  STRIP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`; `tau0:real`;
                       `B:A->bool`; `K:real->A->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `x:A`; `tt:real`;
                                `r:real`; `tau0:real`; `B:A->bool`]) THEN
  REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `P2A_HIST_VIEW_X_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2a_atlas_lc (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= tt /\ tt < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_TOPSPACE_LIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r (r pow 2)` THEN
    REWRITE_TAC[rfs_parabolic_exists] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ASM_MESON_TAC[];
    X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?gamma:real->A. rfs_min_Lgeod (hs:(A)rfs_history) tt x tau0 gamma /\
                                  gamma tau0 = q /\ rfs_lx hs tt x tau0 q <= l0`
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM P2A_L_LENGTH_VIEW] THEN
    UNDISCH_TAC `rfs_min_Lgeod (hs:(A)rfs_history) tt x tau0 gamma` THEN
    REWRITE_TAC[rfs_min_Lgeod] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_lx (hs:(A)rfs_history) tt x tau0 q <= l0` THEN
    REWRITE_TAC[rfs_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; SQRT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let P2AX_T3 = prove
 (`!u:A->bool. P2A_COR_7_12_VIEW_FIX_STATEMENT u /\ P2A_HIST_VIEW_X_STATEMENT u
               ==> P2_COR_7_12_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_COR_7_12_VIEW_FIX_STATEMENT; P2_COR_7_12_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "view") (LABEL_TAC "bridge")) THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `a:real`;
                       `U:real->A->bool`; `r:real`; `dt:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "minex") STRIP_ASSUME_TAC))))) THEN
  REMOVE_THEN "bridge" (MP_TAC o SPEC `hs:(A)rfs_history` o
                        REWRITE_RULE[P2A_HIST_VIEW_X_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_atlas_lc (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ATLAS_LC_HIST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t (y:A). y IN U t ==> a <= t /\ t < tt` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_st_open (hs:(A)rfs_history) U a tt` THEN
    REWRITE_TAC[p3_st_open] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < tt ==> ~(p3_Lmin_set (hs:(A)rfs_history) tt x U t = {})`
    (LABEL_TAC "ne") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `t:real`] o check (fun th ->
      can (find_term (fun t -> t = `p3_st_compact:(A)rfs_history->(real->A->bool)->bool`))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `p3_st_compact:(A)rfs_history->(real->A->bool)->bool`))
          (concl th) &&
      can (find_term (fun t -> t = `p3_Lmin_set:(A)rfs_history->real->A->(real->A->bool)->real->A->bool`))
          (concl th))) THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [USE_THEN "ne" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; p3_Lmin_set; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?gamma:real->A. rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - a) gamma`
      MP_TAC THENL
     [USE_THEN "minex" (MP_TAC o SPECL [`a:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` (MP_TAC o MATCH_MP P2A_MIN_LGEOD_LT)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t (y:A). y IN U t
                ==> rfs_Lx (hs:(A)rfs_history) tt x (tt - t) y =
                    p2a_Lx (rfs_view hs) tt x (tt - t) y`
    (LABEL_TAC "eqL") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?gamma:real->A. rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - t) gamma /\
                                  gamma (tt - t) = y`
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
     [USE_THEN "minex" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `rfs_Lx:(A)rfs_history->real->A->real->A->real`))
          (concl th) && is_forall(concl th))) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o MATCH_MP P2A_MIN_LGEOD_LT); ALL_TAC] THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - t) gamma` THEN
    SIMP_TAC[rfs_min_Lgeod];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t (y:A). y IN U t
                ==> rfs_lx (hs:(A)rfs_history) tt x (tt - t) y =
                    p2a_lx (rfs_view hs) tt x (tt - t) y`
    (LABEL_TAC "eql") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_lx; p2a_lx] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN USE_THEN "eqL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "view" (MP_TAC o SPECL
    [`rfs_view (hs:(A)rfs_history)`; `x:A`; `tt:real`; `a:real`; `U:real->A->bool`;
     `r:real`; `min dt tt`]) THEN
  REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `&0 <= tt /\ tt < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_TOPSPACE_LIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_PERSISTS_MONO THEN
    EXISTS_TAC `tt - dt` THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r dt` THEN
    REWRITE_TAC[rfs_parabolic_exists] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?gamma:real->A. rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - t) gamma /\
                                  gamma (tt - t) = y`
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `p2a_min:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->real->(real->A)->bool`))
          (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `p2a_pc1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->(real->A)->real->real->(real->bool)->bool`)) (concl th)))) THEN
    ASM_MESON_TAC[P2A_MIN_LGEOD_LT];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2a_Lmin_set (rfs_view (hs:(A)rfs_history)) tt x U t =
                  p3_Lmin_set hs tt x U t` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; p2a_Lmin_set; p3_Lmin_set; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `e:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `e:real`] o check (fun th ->
      can (find_term (fun t -> t = `rfs_lx:(A)rfs_history->real->A->real->A->real`))
          (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t':real`; `y':A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':real`; `y':A`]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let P2AX_T2 = prove
 (`!u:A->bool. P2A_LEMMA_7_2_VIEW_X_STATEMENT u /\ P2A_HIST_VIEW_X_STATEMENT u
               ==> P2_LEMMA_7_2_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LEMMA_7_2_VIEW_X_STATEMENT; P2_LEMMA_7_2_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "view") (LABEL_TAC "bridge")) THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `tau0:real`;
                       `K:real->A->bool`; `gs:num->real->A`; `Lb:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "bridge" (MP_TAC o SPEC `hs:(A)rfs_history` o
                        REWRITE_RULE[P2A_HIST_VIEW_X_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_atlas_lc (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_L_adm (hs:(A)rfs_history) tt x tau0 (gs 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_top_at (hs:(A)rfs_history) tt)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_L_adm (hs:(A)rfs_history) tt x tau0 (gs 0)` THEN
    REWRITE_TAC[rfs_L_adm; rfs_st_curve] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gs:num->real->A) 0 (&0) IN topspace(rfs_top_at hs (tt - &0))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_SUB_RZERO]];
    ALL_TAC] THEN
  REMOVE_THEN "view" (MP_TAC o SPECL
    [`rfs_view (hs:(A)rfs_history)`; `x:A`; `tt:real`; `tau0:real`;
     `K:real->A->bool`; `gs:num->real->A`; `Lb:real`]) THEN
  REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS; GSYM P2A_L_LENGTH_VIEW] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `p2a_bsmooth:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->A->real->bool`))
            (concl th) && is_forall(concl th))) THEN
      MAP_EVERY EXISTS_TAC [`tau0:real`; `(gs:num->real->A) 0`; `K:real->A->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sub:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gamma:real->A` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K':real->A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2A_CBOX_ST_COMPACT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eta:real` o check (fun th ->
      can (find_term (fun t -> t = `p2a_adm1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->real->(real->A)->bool`))
          (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `rfs_L_adm:(A)rfs_history->real->A->real->(real->A)->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a ==> c) /\ (b ==> d) ==> a /\ b ==> c /\ d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gamma':real->A` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[]];
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2a_min (rfs_view (hs:(A)rfs_history)) tt x tau0 gamma /\
                  p2a_pc1 (rfs_view hs) tt gamma (&0) tau0 {} /\
                  gamma tau0 = q` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `q:A` o check (fun th ->
        can (find_term (fun t -> t = `p2a_pc1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->(real->A)->real->real->(real->bool)->bool`))
            (concl th) && is_forall(concl th) &&
        not (can (find_term (fun t -> t = `rfs_min_Lgeod:(A)rfs_history->real->A->real->(real->A)->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`gamma':real->A`; `eta:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `eta:real` o check (fun th ->
        can (find_term (fun t -> t = `rfs_Lx:(A)rfs_history->real->A->real->A->real`))
            (concl th) && is_forall(concl th) &&
        not (can (find_term (fun t -> t = `p2a_Lx:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->real->A->real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `rfs_Lx (hs:(A)rfs_history) tt x tau0 q = p2a_Lx (rfs_view hs) tt x tau0 q`
        SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `rfs_Lx:(A)rfs_history->real->A->real->A->real`))
              (concl th) && is_forall(concl th) &&
          can (find_term (fun t -> t = `p2a_Lx:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->real->A->real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `(gs:num->real->A) 0` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `p2a_Lx (rfs_view (hs:(A)rfs_history)) tt x tau0 q <=
                    rfs_L_length hs tt gamma' tau0` MP_TAC THENL
       [SUBGOAL_THEN `(q:A) = (gamma':real->A) tau0` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `p2a_Lx:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)->real->A->real->A->real`)) (concl th) && is_forall(concl th) &&
          not (can (find_term (fun t -> t = `rfs_Lx:(A)rfs_history->real->A->real->A->real`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

(* The full chain against the FIX forms and the x-forms of O3 and O10.        *)

let P2AX_FULL_CHAIN = prove
 (`!u:A->bool.
     P2A_ROUTE_BRIDGE_X_STATEMENT u /\ P2A_ROUTE_8_1_FIX_STATEMENT u /\
     P2A_ROUTE_PARABOLIC_STATEMENT u /\ P2A_ROUTE_SMALLZ_STATEMENT u /\
     P2A_ROUTE_LEMMA_7_2_X_STATEMENT u /\ P2A_ROUTE_COR_7_12_FIX_STATEMENT u /\
     P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u /\
     P2A_MIN_LGEOD_FIX_STATEMENT u /\ P2A_INJ_FIX_STATEMENT u /\
     P2A_LX_USC_FIX_STATEMENT u /\ P2A_SMOOTHING_FIX_STATEMENT u /\
     P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\
     P2A_GAUSS_TAIL_STATEMENT /\ P2A_LOC_BVP_STATEMENT /\
     P2A_BARRIER_FIX_STATEMENT u /\
     P2A_REQ_SHI_SCALED_STATEMENT u /\ P2A_REQ_RLOWER_STATEMENT u /\
     P2A_REQ_AREA_STATEMENT u /\ P2A_REQ_VOLCMP_STATEMENT u
     ==> P2_THM_8_1_STATEMENT u /\ P2_LEMMA_7_2_STATEMENT u /\ P2_COR_7_12_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2A_ROUTE_BRIDGE_X_STATEMENT; P2A_ROUTE_8_1_FIX_STATEMENT;
              P2A_ROUTE_PARABOLIC_STATEMENT; P2A_ROUTE_SMALLZ_STATEMENT;
              P2A_ROUTE_LEMMA_7_2_X_STATEMENT; P2A_ROUTE_COR_7_12_FIX_STATEMENT] THEN
  MP_TAC P2A_DINI THEN MP_TAC(ISPEC `u:A->bool` P2AX_T1) THEN
  MP_TAC(ISPEC `u:A->bool` P2AX_T2) THEN MP_TAC(ISPEC `u:A->bool` P2AX_T3) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Teeth for the corrected clause.  In a view whose slice atlas is the same *)
(* before and after a time (as at a trivial event of a history: no necks,   *)
(* nothing discarded, so the new stage has the old atlas), a continuous     *)
(* curve that is C^1 on the two stage sets of rfs_st_curve (closed at the   *)
(* event time on the later side, open on the earlier side) need not be      *)
(* p2a_pc1: tau |-> (tau - 1/2)^(3/4) for tau > 1/2 has no one-sided        *)
(* derivative at 1/2 from the earlier side, which p2a_pc1 requires since    *)
(* the atlas does not change (its derivative is square integrable, so the   *)
(* singularity is compatible with a finite L-length).  So clause 5 in the   *)
(* form rfs_L_adm ==> p2a_adm cannot hold.                                  *)
(* ------------------------------------------------------------------------- *)

let P2AX_TG_DERIV = prove
 (`!t. &1 / &2 < t
       ==> ((\t. max (t - &1 / &2) (&0) rpow (&3 / &4)) has_real_derivative
            (&3 / &4) * (t - &1 / &2) rpow (&3 / &4 - &1)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\t. (t - &1 / &2) rpow (&3 / &4)` THEN
  EXISTS_TAC `t - &1 / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t - &1 / &2`; `&3 / &4`] HAS_REAL_DERIVATIVE_RPOW) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `((\t. t - &1 / &2) has_real_derivative &1) (atreal t)` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real. t - &1 / &2`; `\x:real. x rpow (&3 / &4)`;
                 `&1`; `(&3 / &4) * (t - &1 / &2) rpow (&3 / &4 - &1)`; `t:real`]
                REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF; REAL_MUL_RID]);;

let P2AX_TG_ZERO = prove
 (`!t. t <= &1 / &2 ==> max (t - &1 / &2) (&0) rpow (&3 / &4) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `max (t - &1 / &2) (&0) = &0` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[RPOW_ZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let P2AX_TG_QUOT = prove
 (`!h. &0 < h ==> max h (&0) rpow (&3 / &4) = h * inv(h rpow (&1 / &4))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `max h (&0) = h` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &4 = &1 - &1 / &4` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1; real_div]);;

let P2AX_TG_GROWTH = prove
 (`!K h. &0 < K /\ &0 < h /\ h <= inv(K pow 4) ==> K <= inv(h rpow (&1 / &4))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h rpow (&1 / &4) <= inv K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(K pow 4) rpow (&1 / &4)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_INV; GSYM RPOW_POW] THEN
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv K)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_INV; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[RPOW_POS_LT]]);;

let P2AX_TG_CONT = prove
 (`!t0. (\t. max (t - &1 / &2) (&0) rpow (&3 / &4)) real_continuous (atreal t0)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\t. max (t - &1 / &2) (&0) rpow (&3 / &4)) =
                (\x. x rpow (&3 / &4)) o (\t. max (t - &1 / &2) (&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN
    SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN REAL_ARITH_TAC]);;

let P2AX_TG_DCOEF_CONT = prove
 (`!t0. &1 / &2 < t0
        ==> (\t. &3 / &4 * (t - &1 / &2) rpow (&3 / &4 - &1)) real_continuous (atreal t0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
  SUBGOAL_THEN `(\t. (t - &1 / &2) rpow (&3 / &4 - &1)) =
                (\x. x rpow (&3 / &4 - &1)) o (\t. t - &1 / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN ASM_REAL_ARITH_TAC]);;

let P2AX_TG_VDERIV = prove
 (`!x:real^1. &1 / &2 < drop x
      ==> ((\s:real^1. (max (drop s - &1 / &2) (&0) rpow (&3 / &4)) % (basis 1:real^3))
           has_derivative
           (\h. (drop h * (&3 / &4 * (drop x - &1 / &2) rpow (&3 / &4 - &1))) % basis 1))
          (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `drop x` P2AX_TG_DERIV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative; LIFT_DROP; o_DEF] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s:real^1. drop(lift(max (drop s - &1 / &2) (&0) rpow (&3 / &4))) % (basis 1:real^3))
     has_derivative
     (\h. drop(drop h % lift(&3 / &4 * (drop x - &1 / &2) rpow (&3 / &4 - &1))) % basis 1))
    (at x)` MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP; DROP_CMUL]]);;

let P2AX_TG_DVEC_CONT = prove
 (`!h:real^1. (\x:real^1. (drop h * (&3 / &4 * (drop x - &1 / &2) rpow (&3 / &4 - &1))) %
                 (basis 1:real^3)) continuous_on {x | &1 / &2 < drop x}`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(lift o (\x:real^1. drop h * (&3 / &4 * (drop x - &1 / &2) rpow (&3 / &4 - &1)))) =
    lift o (\t. drop h * (&3 / &4 * (t - &1 / &2) rpow (&3 / &4 - &1))) o drop`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `x = lift(drop(x:real^1))` SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN MATCH_MP_TAC P2AX_TG_DCOEF_CONT THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2AX_TEETH_PC1 = prove
 (`?(V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
       (real->real^3->real^3^3)) tt b s0 (gamma:real->real^3).
     &0 < s0 /\ s0 < b /\ b < tt /\
     (!t. smooth_manifold_atlas (p2a_vtop V t) (p2a_vatlas V t) /\
          p2a_vatlas V t = p2a_vatlas V tt) /\
     (!tau. gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
     (!tau0 O. open_in (p2a_vtop V (tt - tau0)) O /\ gamma tau0 IN O
               ==> ?d. &0 < d /\ !tau. abs(tau - tau0) < d ==> gamma tau IN O) /\
     (!c. c IN p2a_vatlas V tt
          ==> continuously_differentiable 1
                {s | &0 < drop s /\ drop s <= s0 /\ gamma(drop s) IN FST c}
                (\s. SND c (gamma(drop s))) /\
              continuously_differentiable 1
                {s | s0 < drop s /\ drop s <= b /\ gamma(drop s) IN FST c}
                (\s. SND c (gamma(drop s)))) /\
     ~(?P. p2a_pc1 V tt gamma (&0) b P)`,
  MAP_EVERY EXISTS_TAC
   [`(\t:real. euclidean:(real^3)topology),(\t:real. open_set_atlas (:real^3)),
     (\t:real. \y:real^3. mat 1:real^3^3)`;
    `&2`; `&1`; `&1 / &2`;
    `\tau. (max (tau - &1 / &2) (&0) rpow (&3 / &4)) % (basis 1:real^3)`] THEN
  REWRITE_TAC[p2a_vtop; p2a_vatlas; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:real^3->bool`] THEN
      REWRITE_TAC[GSYM OPEN_IN] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `max (tau0 - &1 / &2) (&0) rpow (&3 / &4) % (basis 1:real^3)`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `tau0:real` P2AX_TG_CONT) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist; GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_CASES_TAC `tau:real = tau0` THENL
       [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[open_set_atlas; IN_SING; FORALL_UNWIND_THM2; IN_UNIV; FST; SND] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
        EXISTS_TAC `\x:real^1 h:real^1. vec 0:real^3` THEN BETA_TAC THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
        MAP_EVERY EXISTS_TAC [`\s:real^1. vec 0:real^3`; `&1`] THEN
        REWRITE_TAC[HAS_DERIVATIVE_CONST; REAL_LT_01; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[P2AX_TG_ZERO; VECTOR_MUL_LZERO];
      REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
        EXISTS_TAC `\x:real^1 h:real^1.
                      (drop h * (&3 / &4 * (drop x - &1 / &2) rpow (&3 / &4 - &1))) %
                      (basis 1:real^3)` THEN
        BETA_TAC THEN CONJ_TAC THENL
         [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
          MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN MATCH_MP_TAC P2AX_TG_VDERIV THEN
          ASM_REWRITE_TAC[];
          X_GEN_TAC `h:real^1` THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `{x:real^1 | &1 / &2 < drop x}` THEN REWRITE_TAC[P2AX_TG_DVEC_CONT] THEN
          SIMP_TAC[SUBSET; IN_ELIM_THM]]];
    REWRITE_TAC[p2a_pc1; NOT_EXISTS_THM; p2a_vatlas; open_set_atlas; IN_SING; IN_UNIV] THEN
      X_GEN_TAC `P:real->bool` THEN
      DISCH_THEN(MP_TAC o SPECL [`&1 / &2`; `(:real^3),(\x:real^3. x)`] o CONJUNCT2) THEN
      REWRITE_TAC[FST; SND; IN_UNIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o CONJUNCT1 o CONJUNCT2))) THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
      SUBGOAL_THEN `lift(&1 / &2) IN {s:real^1 | &1 / &2 <= drop s /\ drop s <= &1 / &2 + d /\
                                                drop s <= &1}` ASSUME_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^3`
        (MP_TAC o C MATCH_MP (ASSUME `lift(&1 / &2) IN {s:real^1 | &1 / &2 <= drop s /\
                                         drop s <= &1 / &2 + d /\ drop s <= &1}`) o CONJUNCT1)) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[has_derivative_within; LIM_WITHIN]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[REAL_LT_01] o SPEC `&1`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `v = (f':real^1->real^1->real^3) (lift(&1 / &2)) (lift(&1))` THEN
      ABBREV_TAC `K = norm(v:real^3) + &2` THEN
      SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
       [EXPAND_TAC "K" THEN MP_TAC(ISPEC `v:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < inv(K pow 4)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
      ABBREV_TAC `h = min (min (del / &2) (min d (&1 / &2))) (inv(K pow 4))` THEN
      SUBGOAL_THEN `&0 < h /\ h < del /\ h <= d /\ h <= &1 / &2 /\ h <= inv(K pow 4)`
      STRIP_ASSUME_TAC THENL [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(&1 / &2 + h)`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
    SUBGOAL_THEN `lift (&1 / &2 + h) - lift (&1 / &2) = h % lift(&1)`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
    SUBGOAL_THEN
       `max (drop (lift (&1 / &2 + h)) - &1 / &2) (&0) rpow (&3 / &4) = h * inv(h rpow (&1 / &4)) /\
        max (drop (lift (&1 / &2)) - &1 / &2) (&0) rpow (&3 / &4) = &0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(&1 / &2 + h) - &1 / &2 = h` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC P2AX_TG_QUOT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2AX_TG_ZERO THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
    SUBGOAL_THEN `(f':real^1->real^1->real^3) (lift (&1 / &2)) (h % lift(&1)) = h % v`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [EXPAND_TAC "v" THEN MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(h % lift(&1)) = h` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[NORM_MUL; NORM_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
       `inv h % ((h * inv(h rpow (&1 / &4))) % (basis 1:real^3) - (&0 % basis 1 + h % v)) =
        inv(h rpow (&1 / &4)) % basis 1 - v`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; VECTOR_MUL_LID];
        ALL_TAC] THEN
    SUBGOAL_THEN `K <= inv(h rpow (&1 / &4)) /\ &0 < inv(h rpow (&1 / &4))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P2AX_TG_GROWTH THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LT_INV_EQ; RPOW_POS_LT]];
        ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `dist:real^3#real^3->real`)) (concl th))) THEN
    REWRITE_TAC[DIST_0] THEN
    MP_TAC(SPECL [`inv(h rpow (&1 / &4)) % (basis 1:real^3)`; `v:real^3`]
                   (NORM_ARITH `!a b:real^3. norm a - norm b <= norm(a - b)`)) THEN
    REWRITE_TAC[NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

