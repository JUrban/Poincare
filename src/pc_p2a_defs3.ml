(* ========================================================================= *)
(* pc_p2a_defs3: FIX forms of the view-level cores C1-C3, of the barrier    *)
(* L13 and of the route obligations O4, O10, O11 (C1 is false without the   *)
(* hypothesis: a flat torus whose slice atlas changes at every time).  Each *)
(* FIX form adds p2a_atlas_lc V; the routes use the FIX forms of L2, L4,    *)
(* L7, L12.  The originals imply their FIX forms for C1-C3 and L13.  O3 is  *)
(* restated against L12 FIX.  The bridges to the Part 3 statements          *)
(* discharge the hypothesis for history views (P2A_ATLAS_LC_HIST).          *)
(* ========================================================================= *)

needs "src/pc_p2a_defs2.ml";;

prioritize_real();;
type_invention_error := true;;

(* C1 (MT Thm 8.1 for smooth view settings).                                 *)

let P2A_THM_8_1_VIEW_FIX_STATEMENT = new_definition
 `P2A_THM_8_1_VIEW_FIX_STATEMENT (u:A->bool) <=>
    !taub l0 V0. &0 < taub /\ &0 < V0
      ==> ?kappa. &0 < kappa /\
            !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) x tt r tau0 B.
               p2a_svs V /\ p2a_atlas_lc V /\
               &0 < tau0 /\ tau0 <= taub /\ &0 < r /\ r pow 2 <= tau0 /\
               x IN topspace(rfs_vtop V tt) /\
               p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
               compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
               (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                      ==> p3_vrm V s y <= inv(r pow 2)) /\
               open_in (rfs_vtop V (tt - tau0)) B /\
               (?v. mfd_has_volume (rfs_vtop V (tt - tau0),rfs_vatlas V (tt - tau0))
                                   (rfs_vmetric V (tt - tau0)) B v /\ V0 <= v) /\
               (!q. q IN B
                    ==> ?gamma. p2a_min V tt x tau0 gamma /\ gamma tau0 = q /\
                                p2a_L_length V tt gamma tau0 <= &2 * sqrt tau0 * l0)
               ==> ?v. mfd_has_volume (rfs_vtop V tt,rfs_vatlas V tt) (rfs_vmetric V tt)
                                      (rfs_vball V tt x r) v /\
                       kappa * r pow 3 <= v`;;

(* C2 (MT Lemma 7.2 / Prop 16.21(1)-(2), corrected).                         *)

(* Clause (c) also gives the end point gamma tau0 = q, as                 *)
(* P2_LEMMA_7_2_STATEMENT does.                                           *)
let P2A_LEMMA_7_2_VIEW_FIX_STATEMENT = new_definition
 `P2A_LEMMA_7_2_VIEW_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     x tt tau0 K gs Lb.
       p2a_svs V /\ p2a_atlas_lc V /\
       &0 < tau0 /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
       p2a_cbox V K /\
       (!n. p2a_adm V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
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

(* C3 (MT Cor 7.12, corrected).                                              *)

(* Hypothesis (2) asks x IN U s, as P2_COR_7_12_STATEMENT does (only the  *)
(* vertical path at x is used).                                           *)
let P2A_COR_7_12_VIEW_FIX_STATEMENT = new_definition
 `P2A_COR_7_12_VIEW_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     x tt a U r dt.
       p2a_svs V /\ p2a_atlas_lc V /\ a < tt /\ x IN topspace(rfs_vtop V tt) /\
       &0 < r /\ &0 < dt /\ p2a_region V (rfs_vball V tt x r) (tt - dt) tt /\
       p2a_st_open V U a tt /\
       (!t y. y IN U t ==> ?gamma. p2a_min V tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
       (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
       (!t. a <= t /\ t < tt ==> ~(p2a_Lmin_set V tt x U t = {})) /\
       (!t e. a <= t /\ t < tt /\ &0 < e
              ==> ?d. &0 < d /\
                      !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                              ==> ?y. y IN U t /\
                                      p2a_lx V tt x (tt - t) y <=
                                      p2a_lx V tt x (tt - t') y' + e)
       ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ p2a_lx V tt x (tt - t) y <= &3 / &2`;;

(* L13 (MT Prop 7.8 in the junk-free form).                                  *)

let P2A_BARRIER_FIX_STATEMENT = new_definition
 `P2A_BARRIER_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma O e.
       p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma /\
       &0 < e /\ open_in (rfs_vtop V (tt - b)) O /\ gamma b IN O /\
       (!g'. p2a_adm V tt x b g' /\ g' b IN O
             ==> p2a_L_length V tt gamma b <= p2a_L_length V tt g' b)
       ==> ?d. &0 < d /\
               !b'. b < b' /\ b' < b + d
                    ==> ?g'. p2a_adm1 V tt x b' g' /\ g' b' = gamma b /\
                             p2a_L_length V tt g' b' / (&2 * sqrt b') -
                             p2a_L_length V tt gamma b / (&2 * sqrt b) <=
                             ((&3 / &2 - p2a_L_length V tt gamma b / (&2 * sqrt b)) / b + e) *
                             (b' - b)`;;

(* Route obligations against the FIX forms.                                  *)

(* O4 (MT Thm 8.1 via Prop 8.2, Lemmas 8.3, 8.9).                            *)
let P2A_ROUTE_8_1_FIX_STATEMENT = new_definition
 `P2A_ROUTE_8_1_FIX_STATEMENT (u:A->bool) <=>
    P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_LGEOD_FIX_STATEMENT u /\
    P2A_MIN_RESTRICT_STATEMENT u /\ P2A_INJ_FIX_STATEMENT u /\
    P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\
    P2A_LX_USC_FIX_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
    P2A_SMALLZ_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\
    P2A_REQ_AREA_STATEMENT u /\ P2A_REQ_VOLCMP_STATEMENT u
    ==> P2A_THM_8_1_VIEW_FIX_STATEMENT u`;;

(* O10 (MT Lemma 7.2 by broken L-geodesics).                                 *)
let P2A_ROUTE_LEMMA_7_2_FIX_STATEMENT = new_definition
 `P2A_ROUTE_LEMMA_7_2_FIX_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_SMOOTHING_FIX_STATEMENT u /\
    P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_LGEOD_FIX_STATEMENT u
    ==> P2A_LEMMA_7_2_VIEW_FIX_STATEMENT u`;;

(* O11 (MT Thm 7.10 / Cor 7.12: barrier at slice minima, Dini comparison).  *)
let P2A_ROUTE_COR_7_12_FIX_STATEMENT = new_definition
 `P2A_ROUTE_COR_7_12_FIX_STATEMENT (u:A->bool) <=>
    P2A_BARRIER_FIX_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u /\ P2A_DINI_STATEMENT
    ==> P2A_COR_7_12_VIEW_FIX_STATEMENT u`;;

(* O3 against the FIX form of L12 (history views satisfy p2a_atlas_lc, so   *)
(* the original L12 is not needed for the bridge).                          *)
let P2A_ROUTE_BRIDGE_FIX_STATEMENT = new_definition
 `P2A_ROUTE_BRIDGE_FIX_STATEMENT (u:A->bool) <=>
    P3_LEMMA_14_11_STATEMENT u /\ P2A_REQ_RLOWER_STATEMENT u /\
    P2A_SMOOTHING_FIX_STATEMENT u
    ==> P2A_HIST_VIEW_STATEMENT u`;;

(* Each original implies its FIX form.                                       *)

let P2A_THM_8_1_VIEW_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_THM_8_1_VIEW_STATEMENT u ==> P2A_THM_8_1_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_THM_8_1_VIEW_STATEMENT; P2A_THM_8_1_VIEW_FIX_STATEMENT] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`taub:real`; `l0:real`; `V0:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`taub:real`; `l0:real`; `V0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `x:A`; `tt:real`; `r:real`; `tau0:real`;
                       `B:A->bool`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`; `x:A`; `tt:real`; `r:real`; `tau0:real`;
                               `B:A->bool`]) THEN
  ASM_REWRITE_TAC[]);;

let P2A_LEMMA_7_2_VIEW_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_LEMMA_7_2_VIEW_STATEMENT u ==> P2A_LEMMA_7_2_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LEMMA_7_2_VIEW_STATEMENT; P2A_LEMMA_7_2_VIEW_FIX_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `x:A`; `tt:real`; `tau0:real`;
                       `K:real->A->bool`; `gs:num->real->A`; `Lb:real`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`; `x:A`; `tt:real`; `tau0:real`;
                               `K:real->A->bool`; `gs:num->real->A`; `Lb:real`]) THEN
  ASM_REWRITE_TAC[]);;

let P2A_COR_7_12_VIEW_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_COR_7_12_VIEW_STATEMENT u ==> P2A_COR_7_12_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_COR_7_12_VIEW_STATEMENT; P2A_COR_7_12_VIEW_FIX_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `x:A`; `tt:real`; `a:real`;
                       `U:real->A->bool`; `r:real`; `dt:real`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`; `x:A`; `tt:real`; `a:real`;
                               `U:real->A->bool`; `r:real`; `dt:real`]) THEN
  ASM_REWRITE_TAC[]);;

let P2A_BARRIER_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_BARRIER_STATEMENT u ==> P2A_BARRIER_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_BARRIER_STATEMENT; P2A_BARRIER_FIX_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`;
                       `gamma:real->A`; `O:A->bool`; `e:real`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`;
                               `gamma:real->A`; `O:A->bool`; `e:real`]) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The bridges to the Part 3 statements from the FIX cores and the history  *)
(* bridge (history views satisfy p2a_atlas_lc), and the full chain against  *)
(* the FIX forms.                                                           *)
(* ========================================================================= *)

let P2A_T1_FIX = prove
 (`!u:A->bool. P2A_THM_8_1_VIEW_FIX_STATEMENT u /\ P2A_HIST_VIEW_STATEMENT u
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
  UNDISCH_TAC `P2A_HIST_VIEW_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2A_HIST_VIEW_STATEMENT] THEN
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

let P2A_T3_FIX = prove
 (`!u:A->bool. P2A_COR_7_12_VIEW_FIX_STATEMENT u /\ P2A_HIST_VIEW_STATEMENT u
               ==> P2_COR_7_12_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_COR_7_12_VIEW_FIX_STATEMENT; P2_COR_7_12_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "view") (LABEL_TAC "bridge")) THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `a:real`;
                       `U:real->A->bool`; `r:real`; `dt:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "minex") STRIP_ASSUME_TAC))))) THEN
  REMOVE_THEN "bridge" (MP_TAC o SPEC `hs:(A)rfs_history` o
                        REWRITE_RULE[P2A_HIST_VIEW_STATEMENT]) THEN
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


let P2A_T2_FIX = prove
 (`!u:A->bool. P2A_LEMMA_7_2_VIEW_FIX_STATEMENT u /\ P2A_HIST_VIEW_STATEMENT u
               ==> P2_LEMMA_7_2_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LEMMA_7_2_VIEW_FIX_STATEMENT; P2_LEMMA_7_2_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "view") (LABEL_TAC "bridge")) THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `tau0:real`;
                       `K:real->A->bool`; `gs:num->real->A`; `Lb:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "bridge" (MP_TAC o SPEC `hs:(A)rfs_history` o
                        REWRITE_RULE[P2A_HIST_VIEW_STATEMENT]) THEN
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

(* ------------------------------------------------------------------------- *)
(* The Dini comparison lemma.  sg = sup of the times <= ts where f <= c; on *)
(* (sg, ts] f > c; for every e > 0, w = sup of the times in [sg, ts] where  *)
(* f t <= f sg + e (t - sg) is ts (lower semicontinuity closes the set, the *)
(* Dini bound pushes past w), so f ts <= f sg + e (ts - sg) for all e.       *)
(* ------------------------------------------------------------------------- *)


(* The full chain against the FIX forms.                                     *)

let P2A_FULL_CHAIN_FIX = prove
 (`!u:A->bool.
     P2A_ROUTE_BRIDGE_FIX_STATEMENT u /\ P2A_ROUTE_8_1_FIX_STATEMENT u /\
     P2A_ROUTE_PARABOLIC_STATEMENT u /\ P2A_ROUTE_SMALLZ_STATEMENT u /\
     P2A_ROUTE_LEMMA_7_2_FIX_STATEMENT u /\ P2A_ROUTE_COR_7_12_FIX_STATEMENT u /\
     P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u /\
     P2A_MIN_LGEOD_FIX_STATEMENT u /\ P2A_INJ_FIX_STATEMENT u /\
     P2A_LX_USC_FIX_STATEMENT u /\ P2A_SMOOTHING_FIX_STATEMENT u /\
     P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\
     P2A_GAUSS_TAIL_STATEMENT /\ P2A_LOC_BVP_STATEMENT /\
     P2A_BARRIER_FIX_STATEMENT u /\
     P2A_REQ_SHI_SCALED_STATEMENT u /\ P2A_REQ_RLOWER_STATEMENT u /\
     P2A_REQ_AREA_STATEMENT u /\ P2A_REQ_VOLCMP_STATEMENT u /\
     P3_LEMMA_14_11_STATEMENT u
     ==> P2_THM_8_1_STATEMENT u /\ P2_LEMMA_7_2_STATEMENT u /\ P2_COR_7_12_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2A_ROUTE_BRIDGE_FIX_STATEMENT; P2A_ROUTE_8_1_FIX_STATEMENT;
              P2A_ROUTE_PARABOLIC_STATEMENT; P2A_ROUTE_SMALLZ_STATEMENT;
              P2A_ROUTE_LEMMA_7_2_FIX_STATEMENT; P2A_ROUTE_COR_7_12_FIX_STATEMENT] THEN
  MP_TAC P2A_DINI THEN MP_TAC(ISPEC `u:A->bool` P2A_T1_FIX) THEN
  MP_TAC(ISPEC `u:A->bool` P2A_T2_FIX) THEN MP_TAC(ISPEC `u:A->bool` P2A_T3_FIX) THEN
  MESON_TAC[]);;

