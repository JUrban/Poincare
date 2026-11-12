(* ========================================================================= *)
(* Unit pc_p4_top: the history level of Part 4 (finite extinction, MT        *)
(* Thm 18.1 in the simply connected case).  The pinch property p4_pinch_ok   *)
(* of a surgery history, the statements FINITE_EXTINCTION_STATEMENT (the     *)
(* link between Part 3 and Part 4; P4_PINCH_FROM_INV_STATEMENT and           *)
(* P4_EXTINCTION_ALIGN are in pc_p4_align) and RFS_CONTINUATION_STATEMENT,   *)
(* and the route-agnostic extinction argument: P4_RFS_EXTINCTION             *)
(* (FINITE_EXTINCTION_STATEMENT fits RFS_EXTINCTION_STATEMENT) and           *)
(* P4_FINITE_EXTINCTION_FROM_WIDTH (every width system gives finite          *)
(* extinction, explicit time T = ((W0 + c)/c)^4).                            *)
(* ========================================================================= *)

needs "src/pc_p4_defs.ml";;
needs "src/pc_rfs_assembly.ml";;

prioritize_real();;
type_invention_error := true;;

(* The pinch property of a surgery history (MT Prop 15.12 with the Ch 13 cap *)
(* metrics; from the Part 3 invariant by P4_PINCH_FROM_INV of pc_p4_pinch):  *)
(* every component Y of a new stage has an ancestor component X of the old   *)
(* stage such that for t' < ts close to the event time there are (1+e)-pinch *)
(* maps (X, g(t')) -> (Y, g(ts)).                                            *)

let p4_pinch_ok = new_definition
 `p4_pinch_ok (hs:(A)rfs_history) <=>
    !k. 1 <= k /\ k <= hs_count hs
        ==> !Y. Y IN connected_components_of (hs_top hs k)
                ==> ?X. X IN connected_components_of (hs_top hs (k - 1)) /\
                        !e. &0 < e
                            ==> ?t1. hs_time hs (k - 1) <= t1 /\ t1 < hs_time hs k /\
                                     !t. t1 < t /\ t < hs_time hs k
                                         ==> ?p. p4_pinch_map
                                                   (hs_top hs (k - 1),hs_atlas hs (k - 1))
                                                   (hs_metric hs (k - 1) t) X
                                                   (hs_top hs k,hs_atlas hs k)
                                                   (hs_metric hs k (hs_time hs k)) Y
                                                   (&1 + e) p`;;

(* ------------------------------------------------------------------------- *)
(* Finite extinction (MT Thm 18.1, simply connected case): for a closed      *)
(* simply connected Riemannian 3-manifold (top,atlas,g) there is a time T    *)
(* such that every controlled history with the pinch property that starts at *)
(* (top,atlas,g) and lives beyond T is extinct, and all its slices from T on *)
(* are empty.  T depends on (top,atlas,g) only (MT p. 432: on the width at   *)
(* time 0).                                                                  *)
(* ------------------------------------------------------------------------- *)

let FINITE_EXTINCTION_STATEMENT = new_definition
 `FINITE_EXTINCTION_STATEMENT (u:A->bool) <=>
    !top atlas g.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ ~(topspace top = {}) /\
        simply_connected_space top /\ riemannian_metric atlas g
        ==> ?T. &0 <= T /\
                !(hs:(A+num#num#real^3)rfs_history) C eps rp dl kp h iota iota'.
                   rfs_controlled (C,eps) (rp,dl,kp,h) hs /\ p4_pinch_ok hs /\
                   rfs_initial (top,atlas) g hs iota iota' /\
                   T < rfs_horizon hs
                   ==> rfs_extinct hs /\
                       !t. T <= t ==> topspace(rfs_top_at hs t) = {}`;;

(* ------------------------------------------------------------------------- *)
(* MT Thm 15.9 / Cor 15.10 in continuation form, a hypothesis of             *)
(* P4_RFS_EXTINCTION (RFS_EXTINCTION_STATEMENT itself is proved in           *)
(* pc_smt_extinct).  Same quantifier structure as RFS_EXTINCTION_STATEMENT;  *)
(* the scale q is chosen before the horizon B (normalization depends on g0   *)
(* only); for every B there is a controlled history with the pinch property  *)
(* that lives beyond B or is extinct.                                        *)
(* ------------------------------------------------------------------------- *)

let RFS_CONTINUATION_STATEMENT = new_definition
 `RFS_CONTINUATION_STATEMENT (u:A->bool) <=>
    !eps0. &0 < eps0
      ==> ?C eps. &0 < C /\ &0 < eps /\ eps <= eps0 /\
            !dl0. &0 < dl0
              ==> !top atlas g0.
                    hausdorff_space top /\
                    smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                    compact_space top /\ ~(topspace top = {}) /\
                    simply_connected_space top /\
                    riemannian_metric atlas g0
                    ==> ?q. &0 < q /\
                            !B. ?(hs:(A+num#num#real^3)rfs_history) rp dl kp h iota iota'.
                                  rfs_controlled (C,eps) (rp,dl,kp,h) hs /\
                                  p4_pinch_ok hs /\
                                  (!t. &0 <= t ==> dl t <= dl0) /\
                                  rfs_initial (top,atlas) (\x. q %% g0 x) hs iota iota' /\
                                  rfs_normalized (hs_top hs 0,hs_atlas hs 0)
                                                 (hs_metric hs 0 (&0)) /\
                                  (B < rfs_horizon hs \/ rfs_extinct hs)`;;


(* ========================================================================= *)
(* The extinction argument for width systems (P4_Q_ZERO is in pc_p4_defs).   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* FINITE_EXTINCTION_STATEMENT fits RFS_EXTINCTION_STATEMENT.                *)
(* ------------------------------------------------------------------------- *)

let P4_RFS_EXTINCTION = prove
 (`!u:A->bool. RFS_CONTINUATION_STATEMENT u /\ FINITE_EXTINCTION_STATEMENT u
               ==> RFS_EXTINCTION_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[RFS_CONTINUATION_STATEMENT; FINITE_EXTINCTION_STATEMENT;
              RFS_EXTINCTION_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") (LABEL_TAC "fin")) THEN
  X_GEN_TAC `eps0:real` THEN DISCH_TAC THEN
  REMOVE_THEN "cont" (MP_TAC o SPEC `eps0:real`) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `dl0:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g0:A->real^3^3`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dl0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g0:A->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hist"))) THEN
  REMOVE_THEN "fin" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `\x:A. q %% (g0:A->real^3^3) x`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  REMOVE_THEN "hist" (MP_TAC o SPEC `T0:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `hs:(A+num#num#real^3)rfs_history` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `rp:real->real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real->real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:real->real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `iota:A->A+num#num#real^3` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `iota':A+num#num#real^3->A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`hs:(A+num#num#real^3)rfs_history`; `rp:real->real`; `dl:real->real`;
    `kp:real->real`; `h:real->real`; `q:real`; `iota:A->A+num#num#real^3`;
    `iota':A+num#num#real^3->A`] THEN
  REMOVE_THEN "ext" (MP_TAC o SPECL
   [`hs:(A+num#num#real^3)rfs_history`; `C:real`; `eps:real`; `rp:real->real`;
    `dl:real->real`; `kp:real->real`; `h:real->real`; `iota:A->A+num#num#real^3`;
    `iota':A+num#num#real^3->A`]) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The monotone quantity Q = w (4t+1)^(-3/4) + c (4t+1)^(1/4): value at      *)
(* t = 0, the fourth root, Lipschitz bound of (4t+1)^(1/4), lower bound,     *)
(* threshold, and the jump lemma (MT Claim 18.22 with the (1+e)-Lipschitz    *)
(* pinch maps, in integrated form).                                          *)
(* ------------------------------------------------------------------------- *)

let P4_RPOW_QUARTER_POW = prove
 (`!x. &0 <= x ==> (x rpow (&1 / &4)) pow 4 = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  ASM_SIMP_TAC[RPOW_RPOW] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let P4_B_GE_1 = prove
 (`!t. &0 <= t ==> &1 <= (&4 * t + &1) rpow (&1 / &4)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC);;

let P4_B_LIPSCHITZ = prove
 (`!s t. &0 <= s /\ s <= t
         ==> (&4 * t + &1) rpow (&1 / &4) - (&4 * s + &1) rpow (&1 / &4) <= t - s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = (&4 * t + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `v = (&4 * s + &1) rpow (&1 / &4)` THEN
  SUBGOAL_THEN `&1 <= u /\ &1 <= v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P4_B_GE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v <= u` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN MATCH_MP_TAC RPOW_LE2 THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u pow 4 = &4 * t + &1 /\ v pow 4 = &4 * s + &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P4_RPOW_QUARTER_POW THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= (u + v) * (u pow 2 + v pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 = &2 * &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SUBGOAL_THEN `&1 <= u pow 2 /\ &1 <= v pow 2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(u - v) * &4 <= (u - v) * ((u + v) * (u pow 2 + v pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(u - v) * ((u + v) * (u pow 2 + v pow 2)) = u pow 4 - v pow 4`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P4_Q_LOWER = prove
 (`!c w t. &0 <= w /\ &0 <= t ==> c * (&4 * t + &1) rpow (&1 / &4) <= p4_q c w t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_q; REAL_LE_ADDL] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC);;

let P4_Q_THRESHOLD = prove
 (`!c w0 t. &0 < c /\ ((w0 + c) / c) pow 4 <= t
            ==> w0 + c < c * (&4 * t + &1) rpow (&1 / &4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((w0 + c) / c) pow 4` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
    REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `y = (w0 + c) / c` THEN
  SUBGOAL_THEN `w0 + c = c * y` SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `y < &0` THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y = (y pow 4) rpow (&1 / &4)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM RPOW_POW] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RPOW_RPOW o rand o snd) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1]; ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LT2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P4_Q_JUMP_STEP = prove
 (`!c e t ts wX wY Q0.
        &0 < c /\ &0 <= e /\ &0 <= t /\ t <= ts /\ &0 <= wX /\
        p4_q c wX t <= Q0 /\ wY <= (&1 + e) pow 2 * wX
        ==> p4_q c wY ts
            <= (&1 + e) pow 2 *
               (Q0 - c * (&4 * ts + &1) rpow (&1 / &4) + c * (ts - t)) +
               c * (&4 * ts + &1) rpow (&1 / &4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_q] THEN STRIP_TAC THEN
  ABBREV_TAC `At = (&4 * t + &1) rpow (&3 / &4)` THEN
  ABBREV_TAC `Ats = (&4 * ts + &1) rpow (&3 / &4)` THEN
  ABBREV_TAC `Bt = (&4 * t + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `Bts = (&4 * ts + &1) rpow (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < At /\ &0 < Ats /\ At <= Ats` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["At"; "Ats"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `Bts - Bt <= ts - t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Bt"; "Bts"] THEN MATCH_MP_TAC P4_B_LIPSCHITZ THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wX <= (Q0 - c * Bt) * At` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q0 - c * Bt` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= wX / At` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + e) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `wY <= ((&1 + e) pow 2 * (Q0 - c * Bt)) * Ats` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + e) pow 2 * wX` THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Q0 - c * Bt) * At` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wY / Ats <= (&1 + e) pow 2 * (Q0 - c * Bt)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) pow 2 * (Q0 - c * Bt) <=
                (&1 + e) pow 2 * (Q0 - c * Bts + c * (ts - t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c * (Bts - Bt) <= c * (ts - t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P4_REAL_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN
  REAL_ARITH_TAC);;

let P4_Q_JUMP = prove
 (`!c ts wY Q0.
        &0 < c /\ &0 <= wY /\
        (!e. &0 < e
             ==> ?t1. &0 <= t1 /\ t1 < ts /\
                      !t. t1 < t /\ t < ts
                          ==> ?wX. &0 <= wX /\ p4_q c wX t <= Q0 /\
                                   wY <= (&1 + e) pow 2 * wX)
        ==> p4_q c wY ts <= Q0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Bts = (&4 * ts + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `X = Q0 - c * Bts` THEN
  MATCH_MP_TAC P4_REAL_LE_EPS THEN
  X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  ABBREV_TAC `e = min (&1) (eta / (&6 * (abs X + &1)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= &1 /\ e * (&6 * (abs X + &1)) <= eta`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN `&0 < &6 * (abs X + &1)` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(eta / (&6 * (abs X + &1))) * (&6 * (abs X + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = eta / (&8 * c)` THEN
  SUBGOAL_THEN `&0 < d /\ &8 * c * d = eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  ABBREV_TAC `t = (max t1 (ts - d) + ts) / &2` THEN
  SUBGOAL_THEN `t1 < t /\ t < ts /\ ts - t <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `wX:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:real`; `e:real`; `t:real`; `ts:real`; `wX:real`; `wY:real`;
                `Q0:real`] P4_Q_JUMP_STEP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 + e) pow 2 <= &1 + &3 * e` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(&1 + e) pow 2 = &1 + &2 * e + e * e`] THEN
    SUBGOAL_THEN `e * e <= e * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + e) pow 2 - &1) * X <= eta / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 * e) * (abs X + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((&1 + e) pow 2 - &1) * abs X` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH `&0 <= (&1 + e) pow 2 - &1 <=>
                                  &0 <= e * (&2 + e)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH `&0 <= (&1 + e) pow 2 - &1 <=>
                                  &0 <= e * (&2 + e)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) pow 2 * c * (ts - t) <= eta / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * c * d` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Histories: monotone times, the slab containing a time, the view at a      *)
(* time, pinching on a slab, metrics along a slab, stage facts, the slab     *)
(* step of a width system.                                                   *)
(* ------------------------------------------------------------------------- *)

let P4_TIME_MONO = prove
 (`!hs:(A)rfs_history i j.
        rfs_history_ok hs /\ i <= j /\ j <= hs_count hs + 1
        ==> hs_time hs i <= hs_time hs j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[rfs_history_ok] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!d. i + d <= hs_count (hs:(A)rfs_history) + 1
        ==> hs_time hs i <= hs_time hs (i + d)`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hs_time (hs:(A)rfs_history) (i + d)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `i + SUC d <= hs_count (hs:(A)rfs_history) + 1` THEN ARITH_TAC;
        REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `SUC n = n + 1`] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `i + SUC d <= hs_count (hs:(A)rfs_history) + 1` THEN ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j - i:num`) THEN
  SUBGOAL_THEN `(i:num) + (j - i) = j` SUBST1_TAC THENL
   [UNDISCH_TAC `i:num <= j` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P4_TIME_STRICT = prove
 (`!hs:(A)rfs_history i j.
        rfs_history_ok hs /\ i < j /\ j <= hs_count hs + 1
        ==> hs_time hs i < hs_time hs j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `hs_time (hs:(A)rfs_history) (i + 1)` THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS) THEN ASM_ARITH_TAC;
    MATCH_MP_TAC P4_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let P4_SLAB_EQ = prove
 (`!hs:(A)rfs_history k s.
        rfs_history_ok hs /\ k <= hs_count hs /\
        hs_time hs k <= s /\ s < hs_time hs (k + 1)
        ==> rfs_slab hs s = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_slab] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `m:num` THEN BETA_TAC THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k + 1`; `m:num`] P4_TIME_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `m + 1`; `k:num`] P4_TIME_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let P4_SLAB_EXISTS = prove
 (`!hs:(A)rfs_history s.
        rfs_history_ok hs /\ &0 <= s /\ s < rfs_horizon hs
        ==> ?k. k <= hs_count hs /\ hs_time hs k <= s /\ s < hs_time hs (k + 1)`,
  REWRITE_TAC[rfs_horizon] THEN REPEAT STRIP_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC
    `\k. k <= hs_count (hs:(A)rfs_history) /\ hs_time hs k <= s` num_MAX)))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN
      ASM_REWRITE_TAC[LE_0];
      EXISTS_TAC `hs_count (hs:(A)rfs_history)` THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = hs_count (hs:(A)rfs_history)` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let P4_VIEW_AT = prove
 (`!hs:(A)rfs_history k s.
        rfs_history_ok hs /\ k <= hs_count hs /\
        hs_time hs k <= s /\ s < hs_time hs (k + 1)
        ==> &0 <= s /\
            rfs_top_at hs s = hs_top hs k /\ rfs_atlas_at hs s = hs_atlas hs k /\
            rfs_metric_at hs s = hs_metric hs k s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] P4_TIME_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) s` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_live] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] P4_SLAB_EQ) THEN
  ASM_SIMP_TAC[]);;

let P4_PINCHED_SLAB = prove
 (`!hs:(A)rfs_history k s x.
        rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ k <= hs_count hs /\
        hs_time hs k <= s /\ s < hs_time hs (k + 1) /\ x IN topspace(hs_top hs k)
        ==> --(&6) / (&4 * s + &1) <= mfd_scalar (hs_atlas hs k) (hs_metric hs k s) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] P4_VIEW_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_view; rfs_pinched; rfs_pinched_at] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:A`]) THEN ASM_SIMP_TAC[]);;

let P4_RF_METRIC = prove
 (`!top atlas (g:real->A->real^N^N) a b t.
        ricci_flow_from (top,atlas) a b g /\ a <= t /\ t < b
        ==> riemannian_metric atlas (g t)`,
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P4_STAGE_FACTS = prove
 (`!C eps rp dl kp h (hs:(B)rfs_history) k.
        rfs_controlled (C,eps) (rp,dl,kp,h) hs /\ k <= hs_count hs
        ==> hausdorff_space (hs_top hs k) /\
            smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
            compact_space (hs_top hs k) /\
            mfd_orientable (hs_top hs k) (hs_atlas hs k) /\
            ricci_flow_from (hs_top hs k,hs_atlas hs k) (hs_time hs k)
                            (hs_time hs (k + 1)) (hs_metric hs k) /\
            &0 <= hs_time hs k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_controlled] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`hs:(B)rfs_history`; `0`; `k:num`] P4_TIME_MONO) THEN
  ASM_REWRITE_TAC[rfs_history_ok] THEN
  ANTS_TAC THENL [UNDISCH_TAC `k <= hs_count (hs:(B)rfs_history)` THEN ARITH_TAC;
                  ASM_REAL_ARITH_TAC]);;

let P4_SLAB_STEP = prove
 (`!(WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real)
    aA (WB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->real^3^3)->(B->bool)->real)
    aB c C eps rp dl kp h (hs:(B)rfs_history) k Y t0 t.
        p4_width_system (WA,aA) (WB,aB) c /\
        rfs_controlled (C,eps) (rp,dl,kp,h) hs /\ k <= hs_count hs /\
        Y IN connected_components_of (hs_top hs k) /\
        aB (hs_top hs k,hs_atlas hs k) Y /\
        hs_time hs k <= t0 /\ t0 <= t /\ t < hs_time hs (k + 1)
        ==> p4_q c (WB (hs_top hs k,hs_atlas hs k) (hs_metric hs k t) Y) t
            <= p4_q c (WB (hs_top hs k,hs_atlas hs k) (hs_metric hs k t0) Y) t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `eps:real`; `rp:real->real`; `dl:real->real`;
                `kp:real->real`; `h:real->real`; `hs:(B)rfs_history`; `k:num`]
               P4_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o el 2 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`hs_top (hs:(B)rfs_history) k`; `hs_atlas (hs:(B)rfs_history) k`;
    `hs_metric (hs:(B)rfs_history) k`; `hs_time (hs:(B)rfs_history) k`;
    `hs_time (hs:(B)rfs_history) (k + 1)`; `t0:real`; `t:real`; `Y:B->bool`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `x:B`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P4_PINCHED_SLAB THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfs_controlled]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET o
      check (fun th -> is_binary "IN" (concl th) &&
                       rand(concl th) = `connected_components_of (hs_top (hs:(B)rfs_history) k)`)) THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The induction over events and finite extinction.                          *)
(* ------------------------------------------------------------------------- *)

let P4_WIDTH_INDUCTION = prove
 (`!(WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real)
    aA (WB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->real^3^3)->(B->bool)->real)
    aB c Q0 C eps rp dl kp h (hs:(B)rfs_history).
        p4_width_system (WA,aA) (WB,aB) c /\
        rfs_controlled (C,eps) (rp,dl,kp,h) hs /\ p4_pinch_ok hs /\
        (!Y. Y IN connected_components_of (hs_top hs 0)
             ==> aB (hs_top hs 0,hs_atlas hs 0) Y /\
                 p4_q c (WB (hs_top hs 0,hs_atlas hs 0) (hs_metric hs 0 (hs_time hs 0)) Y)
                        (hs_time hs 0) <= Q0)
        ==> !k. k <= hs_count hs
                ==> !Y. Y IN connected_components_of (hs_top hs k)
                        ==> aB (hs_top hs k,hs_atlas hs k) Y /\
                            !t. hs_time hs k <= t /\ t < hs_time hs (k + 1)
                                ==> p4_q c (WB (hs_top hs k,hs_atlas hs k)
                                               (hs_metric hs k t) Y) t <= Q0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sys") (CONJUNCTS_THEN2 (LABEL_TAC "ctl")
    (CONJUNCTS_THEN2 (LABEL_TAC "pok") (LABEL_TAC "base")))) THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `Y:B->bool` THEN DISCH_TAC THEN
    REMOVE_THEN "base" (MP_TAC o SPEC `Y:B->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p4_q c (WB (hs_top hs 0,hs_atlas hs 0)
                         (hs_metric (hs:(B)rfs_history) 0 (hs_time hs 0)) (Y:B->bool))
                       (hs_time hs 0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_SLAB_STEP THEN
    MAP_EVERY EXISTS_TAC
     [`WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real`;
      `aA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->bool)->bool`;
      `aB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->bool)->bool`;
      `C:real`; `eps:real`; `rp:real->real`; `dl:real->real`; `kp:real->real`;
      `h:real->real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  X_GEN_TAC `Y:B->bool` THEN DISCH_TAC THEN
  REMOVE_THEN "pok" (MP_TAC o SPEC `k + 1` o REWRITE_RULE[p4_pinch_ok]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1 /\ (k + 1) - 1 = k`] THEN
  DISCH_THEN(MP_TAC o SPEC `Y:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pin"))) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `k + 1 <= hs_count (hs:(B)rfs_history)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `X:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih")) THEN
  SUBGOAL_THEN `k <= hs_count (hs:(B)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `k + 1 <= hs_count (hs:(B)rfs_history)` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `eps:real`; `rp:real->real`; `dl:real->real`;
                `kp:real->real`; `h:real->real`; `hs:(B)rfs_history`; `k:num`]
               P4_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `eps:real`; `rp:real->real`; `dl:real->real`;
                `kp:real->real`; `h:real->real`; `hs:(B)rfs_history`; `k + 1`]
               P4_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [USE_THEN "sys" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p4_width_system]) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(B)rfs_history)` ASSUME_TAC THENL
   [USE_THEN "ctl" (MP_TAC o GEN_REWRITE_RULE I [rfs_controlled]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time hs (k + 1) < hs_time (hs:(B)rfs_history) ((k + 1) + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P4_TIME_STRICT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k + 1 <= hs_count (hs:(B)rfs_history)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas hs (k + 1))
                  (hs_metric (hs:(B)rfs_history) (k + 1) (hs_time hs (k + 1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P4_RF_METRIC THEN
    MAP_EVERY EXISTS_TAC [`hs_top (hs:(B)rfs_history) (k + 1)`;
                          `hs_time (hs:(B)rfs_history) (k + 1)`;
                          `hs_time (hs:(B)rfs_history) ((k + 1) + 1)`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?t1. hs_time hs k <= t1 /\ t1 < hs_time (hs:(B)rfs_history) (k + 1) /\
                 !t. t1 < t /\ t < hs_time hs (k + 1)
                     ==> aB (hs_top hs (k + 1),hs_atlas hs (k + 1)) (Y:B->bool) /\
                         WB (hs_top hs (k + 1),hs_atlas hs (k + 1))
                            (hs_metric hs (k + 1) (hs_time hs (k + 1))) Y
                         <= (&1 + e) pow 2 *
                            WB (hs_top hs k,hs_atlas hs k) (hs_metric hs k t) (X:B->bool)`
  (LABEL_TAC "tr") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "pin" (MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:B->B`) THEN
    USE_THEN "sys" (MP_TAC o el 3 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `p:B->B` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P4_RF_METRIC THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(B)rfs_history) k`; `hs_time (hs:(B)rfs_history) k`;
                            `hs_time (hs:(B)rfs_history) (k + 1)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->bool)->bool) (hs_top (hs:(B)rfs_history) (k + 1),hs_atlas hs (k + 1)) (Y:B->bool)` ASSUME_TAC THENL
   [USE_THEN "tr" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(t1 + hs_time (hs:(B)rfs_history) (k + 1)) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `p4_q c (WB (hs_top hs (k + 1),hs_atlas hs (k + 1))
               (hs_metric hs (k + 1) (hs_time hs (k + 1))) (Y:B->bool))
           (hs_time (hs:(B)rfs_history) (k + 1)) <= Q0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P4_Q_JUMP THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "sys" (MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "tr" (fun th -> MP_TAC(MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    EXISTS_TAC `WB (hs_top hs k,hs_atlas hs k) (hs_metric (hs:(B)rfs_history) k t)
                   (X:B->bool):real` THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "sys" (MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P4_RF_METRIC THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(B)rfs_history) k`; `hs_time (hs:(B)rfs_history) k`;
                            `hs_time (hs:(B)rfs_history) (k + 1)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_q c (WB (hs_top hs (k + 1),hs_atlas hs (k + 1))
               (hs_metric hs (k + 1) (hs_time hs (k + 1))) (Y:B->bool))
           (hs_time (hs:(B)rfs_history) (k + 1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_SLAB_STEP THEN
  MAP_EVERY EXISTS_TAC
   [`WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real`;
    `aA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->bool)->bool`;
    `aB:(B topology#(((B->bool)#(B->real^3))->bool))->(B->bool)->bool`;
    `C:real`; `eps:real`; `rp:real->real`; `dl:real->real`; `kp:real->real`;
    `h:real->real`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let P4_FINITE_EXTINCTION_FROM_WIDTH = prove
 (`!(WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real)
    aA
    (WB:((A+num#num#real^3) topology#
         ((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->
        ((A+num#num#real^3)->real^3^3)->((A+num#num#real^3)->bool)->real)
    aB c.
        p4_width_system (WA,aA) (WB,aB) c ==> FINITE_EXTINCTION_STATEMENT (:A)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sys") THEN
  REWRITE_TAC[FINITE_EXTINCTION_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [USE_THEN "sys" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p4_width_system]) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) g (topspace top) + c) / c) pow 4` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`hs:(A+num#num#real^3)rfs_history`; `C:real`; `eps:real`; `rp:real->real`;
    `dl:real->real`; `kp:real->real`; `h:real->real`;
    `iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A+num#num#real^3)rfs_history)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_controlled]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `hs:(A+num#num#real^3)rfs_history`; `iota:A->A+num#num#real^3`;
                 `iota':A+num#num#real^3->A`] RFS_INITIAL_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `rp:real->real`; `dl:real->real`;
                `kp:real->real`; `h:real->real`; `hs:(A+num#num#real^3)rfs_history`; `0`]
               P4_STAGE_FACTS) THEN
  ASM_REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(aB:((A+num#num#real^3) topology#((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->((A+num#num#real^3)->bool)->bool) (hs_top (hs:(A+num#num#real^3)rfs_history) 0,hs_atlas hs 0)
       (topspace(hs_top hs 0)) /\
    (WB:((A+num#num#real^3) topology#((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->((A+num#num#real^3)->real^3^3)->((A+num#num#real^3)->bool)->real) (hs_top hs 0,hs_atlas hs 0) (hs_metric hs 0 (&0)) (topspace(hs_top hs 0))
    <= (WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "sys" (MP_TAC o el 5 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`iota:A->A+num#num#real^3`; `iota':A+num#num#real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_initial (top,atlas) (g:A->real^3^3)
                     (hs:(A+num#num#real^3)rfs_history) iota iota'` THEN
      SIMP_TAC[rfs_initial];
      USE_THEN "sys" (MP_TAC o el 4 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real`;
    `aA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->bool)->bool`;
    `WB:((A+num#num#real^3) topology#
         ((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->
        ((A+num#num#real^3)->real^3^3)->((A+num#num#real^3)->bool)->real`;
    `aB:((A+num#num#real^3) topology#
         ((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->
        ((A+num#num#real^3)->bool)->bool`;
    `c:real`; `(WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c`;
    `C:real`; `eps:real`; `rp:real->real`; `dl:real->real`; `kp:real->real`;
    `h:real->real`; `hs:(A+num#num#real^3)rfs_history`] P4_WIDTH_INDUCTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING] THEN
    X_GEN_TAC `Y:A+num#num#real^3->bool` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN
    ASM_REWRITE_TAC[P4_Q_ZERO] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "ind")] THEN
  SUBGOAL_THEN
   `!t. (((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c) / c) pow 4 <= t
        ==> topspace(rfs_top_at (hs:(A+num#num#real^3)rfs_history) t) = {}`
  (LABEL_TAC "empty") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c) / c) pow 4` THEN
      ASM_REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
      ALL_TAC] THEN
    ASM_CASES_TAC `t < rfs_horizon (hs:(A+num#num#real^3)rfs_history)` THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[rfs_top_at; rfs_live; GSYM rfs_horizon] THEN
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY]] THEN
    MP_TAC(ISPECL [`hs:(A+num#num#real^3)rfs_history`; `t:real`] P4_SLAB_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A+num#num#real^3)rfs_history`; `k:num`; `t:real`] P4_VIEW_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUBSET_EMPTY; SUBSET; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A+num#num#real^3` THEN DISCH_TAC THEN
    ABBREV_TAC `Y = connected_component_of (hs_top (hs:(A+num#num#real^3)rfs_history) k) x` THEN
    SUBGOAL_THEN `Y IN connected_components_of (hs_top (hs:(A+num#num#real^3)rfs_history) k)`
    ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "ind" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `Y:A+num#num#real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `t:real`)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`C:real`; `eps:real`; `rp:real->real`; `dl:real->real`;
                  `kp:real->real`; `h:real->real`; `hs:(A+num#num#real^3)rfs_history`;
                  `k:num`] P4_STAGE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 <= (WB:((A+num#num#real^3) topology#((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->((A+num#num#real^3)->real^3^3)->((A+num#num#real^3)->bool)->real) (hs_top hs k,hs_atlas hs k)
               (hs_metric (hs:(A+num#num#real^3)rfs_history) k t)
               (Y:A+num#num#real^3->bool)`
    ASSUME_TAC THENL
     [USE_THEN "sys" (MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [p4_width_system]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P4_RF_METRIC THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(A+num#num#real^3)rfs_history) k`;
                            `hs_time (hs:(A+num#num#real^3)rfs_history) k`;
                            `hs_time (hs:(A+num#num#real^3)rfs_history) (k + 1)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`;
                  `(WB:((A+num#num#real^3) topology#((((A+num#num#real^3)->bool)#((A+num#num#real^3)->real^3))->bool))->((A+num#num#real^3)->real^3^3)->((A+num#num#real^3)->bool)->real) (hs_top hs k,hs_atlas hs k)
                      (hs_metric (hs:(A+num#num#real^3)rfs_history) k t)
                      (Y:A+num#num#real^3->bool)`; `t:real`] P4_Q_LOWER) THEN
    MP_TAC(SPECL [`c:real`; `(WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top)`; `t:real`]
                 P4_Q_THRESHOLD) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_extinct] THEN
  ABBREV_TAC `T1 = max ((((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c) / c) pow 4)
                       (hs_time (hs:(A+num#num#real^3)rfs_history) (hs_count hs))` THEN
  SUBGOAL_THEN `hs_time (hs:(A+num#num#real^3)rfs_history) (hs_count hs) <= T1 /\
                T1 < hs_time hs (hs_count hs + 1) /\
                (((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c) / c) pow 4 <= T1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[REAL_MAX_LE; REAL_LE_MAX; REAL_MAX_LT] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(((WA:(A topology#(((A->bool)#(A->real^3))->bool))->(A->real^3^3)->(A->bool)->real) (top,atlas) (g:A->real^3^3) (topspace top) + c) / c) pow 4 <
                   rfs_horizon (hs:(A+num#num#real^3)rfs_history)` THEN
      REWRITE_TAC[rfs_horizon];
      RULE_ASSUM_TAC(REWRITE_RULE[rfs_history_ok]) THEN ASM_SIMP_TAC[LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A+num#num#real^3)rfs_history`; `hs_count (hs:(A+num#num#real^3)rfs_history)`;
                 `T1:real`] P4_VIEW_AT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) =
    `rfs_top_at (hs:(A+num#num#real^3)rfs_history) T1`)) THEN
  USE_THEN "empty" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


