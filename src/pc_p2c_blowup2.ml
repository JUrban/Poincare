(* ========================================================================= *)
(* Unit pc_p2c_blowup2 (Part 2C): MT Thm 11.8 part 1 in view form            *)
(* (Prop 11.10 with Claim 11.17, the recursion): region bounds RBU(T) along  *)
(* subsequences, the flow limit on (-T,0] they give, the slices of the limit *)
(* at every time s (canonical neighbourhoods by Claim 11.6 at s, bounded     *)
(* curvature at bounded distance from Thm 10.2), MT Cor 11.16 in flow form   *)
(* (P2C_COR_11_16_FLOW_STATEMENT, pc_p2c_c1116req), the -T slice and the     *)
(* extension past -T.                                                        *)
(* ========================================================================= *)

needs "src/pc_p2c_blowup.ml";;
needs "src/pc_p2c_c1116req.ml";;
needs "src/pc_lim_back.ml";;
needs "src/pc_rf_mequiv.ml";;
needs "src/pc_p2b_rmhalf.ml";;
needs "src/pc_p2c_bugq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* RBU(T) and the flow limit on (-T,0]; the slices of a flow limit at its    *)
(* times s: slice limits, compact closures, Shi bounds, Claim 11.6 at s, and *)
(* bounded curvature at bounded distance.                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* RBU(Tr): the region bounds behind the backward extension (MT Prop 11.10): *)
(* for every a in (-Tr,0] one constant K, uniform in the radius A, such that *)
(* eventually the rescaled ball of radius A at t n persists back to time    *)
(* t n + a / Q n, lies in the slices on [a,0] and has |Rm| <= K Q n there.  *)
(* ------------------------------------------------------------------------- *)

let p2bu_rbu = new_definition
 `p2bu_rbu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (x:num->A) (t:num->real) (Q:num->real) (Tr:real) <=>
    !a. --Tr < a /\ a <= &0
        ==> ?K. !A. &0 < A
                ==> ?N. !n. N <= n
                        ==> rfs_persists (V n)
                              (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                              (t n + a / Q n) (t n) /\
                            !s y. a <= s /\ s <= &0 /\
                                  y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                  ==> y IN topspace(rfs_vtop (V n) (t n + s / Q n)) /\
                                      p3_vrm (V n) (t n + s / Q n) y <= K * Q n`;;


let P2BU_RBU_MONO = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q Tr T'.
     p2bu_rbu V x t Q Tr /\ T' <= Tr ==> p2bu_rbu V x t Q T'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbu] THEN STRIP_TAC THEN
  X_GEN_TAC `a:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let P2BU_RBU_SUBSEQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q Tr sub.
     p2bu_rbu V x t Q Tr /\ p3_subseq sub
     ==> p2bu_rbu (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) Tr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbu; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. n <= sub n` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `--Tr < a /\ a <= &0`) o SPEC `a:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(C MP (ASSUME `&0 < A`) (SPEC `A:real` th))) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC th) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

(* RBU(Tr) gives the region hypotheses of P2BU_FROM_SLICE_UPTO on (-Tr,0]    *)
(* and, for each a, a bound on [a,0] uniform in A.                           *)

let P2BU_RBU_TO_J = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q Tr.
     (!n. &0 < Q n) /\ p2bu_rbu V x t Q Tr
     ==> (!A a b. &0 < A /\ real_interval[a,b] SUBSET {s | --Tr < s /\ s <= &0}
                  ==> ?CA N. !n. N <= n
                         ==> (!s. a <= s /\ s <= b
                                  ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                      topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                             rfs_persists (V n)
                               (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                               (t n + a / Q n) (t n + b / Q n) /\
                             !s y. a <= s /\ s <= b /\
                                   y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                   ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n) /\
         (!a. --Tr < a /\ a <= &0
              ==> ?K. !A. &0 < A
                     ==> ?N. !n s y. N <= n /\ a <= s /\ s <= &0 /\
                                     y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                     ==> p3_vrm (V n) (t n + s / Q n) y <= K * Q n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbu] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (LABEL_TAC "rbu")) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`A:real`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `b < a:real` THENL
     [MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[P2CO_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `b / (Q:num->real) n < a / Q n` MP_TAC THENL
         [USE_THEN "Qpos" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[REAL_LT_DIV2_EQ] THEN
          ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `--Tr < a /\ a <= &0 /\ b <= &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET {s | --Tr < s /\ s <= &0}` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `a:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "rbu" (MP_TAC o C MP (CONJ (ASSUME `--Tr < a`) (ASSUME `a <= &0`)) o
                    SPEC `a:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `N:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "in")) THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "in" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) n + a / Q n`; `(t:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `!t b:real. t + b <= t <=> b <= &0`] THEN
      USE_THEN "Qpos" (MP_TAC o SPEC `n:num`) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "in" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rbu" (MP_TAC o C MP (ASSUME `--Tr < a /\ a <= &0`) o SPEC `a:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    DISCH_THEN(fun th -> X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      MP_TAC(C MP (ASSUME `&0 < A`) (SPEC `A:real` th))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`] o CONJUNCT2) THEN ASM_SIMP_TAC[]]);;

(* The flow limit on (-Tr,0] from RBU(Tr) (the tail of P2BU_S9 for general *)
(* Tr): P2BU_FROM_SLICE_UPTO, completeness from the bounds uniform in A,    *)
(* sec >= 0 (Thm 5.33), |Rm| bounded on each [a,0] (P2BU_RM_TRANSFER), and  *)
(* connectedness (every point is joinable to xl).                           *)

let P2BU_FLOW_FROM_RBU = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_THM_5_33_STATEMENT u w
     ==> !V x t Q (top:B topology) atlas g0 xl W (phi:num->B->A) Tr.
           (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) /\
                rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
           (!B. ?N. !n. N <= n ==> B < Q n) /\
           p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
           mfd_complete (top,atlas) g0 /\ &0 < Tr /\ p2bu_rbu V x t Q Tr
           ==> ?sub (top':B topology) atlas' g.
                  p3_subseq sub /\
                  p3_flow_limit_on (\n. V (sub n)) (x o sub) (t o sub) (Q o sub)
                    {s | --Tr < s /\ s <= &0} (top',atlas') g xl /\
                  connected_space top' /\
                  (!s. --Tr < s /\ s <= &0
                       ==> riemannian_metric atlas' (g s) /\ mfd_complete (top',atlas') (g s) /\
                           (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                                    ==> &0 <= mfd_sectional atlas' (g s) y u v)) /\
                  (!a b. --Tr < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top',atlas') a b g) /\
                  (!a. --Tr < a /\ a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g) /\
                  (!a. --Tr < a /\ a <= &0
                       ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top'
                                     ==> mfd_rm_norm atlas' (g s) y <= K) /\
                  (!y. y IN topspace top' ==> mfd_joinable (top',atlas') xl y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qinf")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rbu")))))) THEN
  SUBGOAL_THEN `!n. &0 < (Q:num->real) n` (LABEL_TAC "Qpos") THENL
   [USE_THEN "sl" (MP_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `Tr:real`]
                P2BU_RBU_TO_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rj1") (LABEL_TAC "rj2")) THEN
  SUBGOAL_THEN `is_realinterval {s:real | --Tr < s /\ s <= &0} /\
                (&0) IN {s:real | --Tr < s /\ s <= &0} /\
                (!a0. a0 IN {s:real | --Tr < s /\ s <= &0} /\
                      (!s. s IN {s:real | --Tr < s /\ s <= &0} ==> a0 <= s) ==> a0 = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a0 - Tr) / &2`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `{s:real | --Tr < s /\ s <= &0}`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`] P2BU_FROM_SLICE_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "views" (fun th -> MESON_TAC[th]) THEN NO_TAC;
           GEN_TAC THEN MATCH_MP_TAC P2BU_SLICE_BASE_IN THEN
           MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
             `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
             `W:num->B->bool`; `phi:num->B->A`] THEN
           ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "compl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "join")))))))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub2 n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub2:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top':B topology) (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* completeness on J *)
  SUBGOAL_THEN `!s. --Tr < s /\ s <= &0 ==> mfd_complete (top',atlas') ((g:real->B->real^3^3) s)`
  (LABEL_TAC "cs") THENL
   [X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    USE_THEN "rj2" (MP_TAC o C MP (CONJ (ASSUME `--Tr < s0`) (ASSUME `s0 <= &0`)) o
                    SPEC `s0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
    USE_THEN "compl" (MP_TAC o SPECL [`s0:real`; `&0`; `K:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN
      FIRST [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
             X_GEN_TAC `A:real` THEN DISCH_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN
             ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* sec >= 0 on J (Thm 5.33) *)
  SUBGOAL_THEN `!s y u v. s IN {s:real | --Tr < s /\ s <= &0} /\ y IN topspace top' /\
                          ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas' ((g:real->B->real^3^3) s) y u v`
  (LABEL_TAC "sec") THENL
   [UNDISCH_TAC `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool)` THEN
    REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN
    DISCH_THEN(MP_TAC o ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(Q:num->real) o (sub2:num->num)`;
      `{s:real | --Tr < s /\ s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Q:num->real`; `sub2:num->num`] P2BU_QINF_SUBSEQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* |Rm| bounded on each [a,0] *)
  SUBGOAL_THEN `!a. --Tr < a /\ a <= &0
                    ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top'
                                  ==> mfd_rm_norm atlas' ((g:real->B->real^3^3) s) y <= K`
  (LABEL_TAC "rmb") THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN
    USE_THEN "rj2" (MP_TAC o C MP (CONJ (ASSUME `--Tr < a`) (ASSUME `a <= &0`)) o
                    SPEC `a:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN DISCH_THEN(LABEL_TAC "K") THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `y0:B`] THEN STRIP_TAC THEN
    USE_THEN "fl" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH]) THEN
    DISCH_THEN(X_CHOOSE_THEN `W':num->B->bool` (X_CHOOSE_THEN `phi':num->B->A` ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(Q:num->real) o (sub2:num->num)`;
      `{s:real | --Tr < s /\ s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W':num->B->bool`; `phi':num->B->A`; `s0:real`; `y0:B`; `K:real`] P2BU_RM_TRANSFER) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "K" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* connectedness *)
  SUBGOAL_THEN `connected_space (top':B topology)` ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_SPACE_IFF_CONNECTED_COMPONENT] THEN
    MAP_EVERY X_GEN_TAC [`y1:B`; `y2:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `y1:B`; `y2:B`]
      MFD_JOINABLE_CONNECTED_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `xl:B`; `y1:B`]
        MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub2:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      USE_THEN "cs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    REPEAT STRIP_TAC THEN USE_THEN "rf" MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* Slice limits pass to subsequences (exhaustion and maps re-indexed).     *)

let P2BU_SLICE_LIMIT_SUBSEQ = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q (top:B topology) atlas g xl W (phi:num->B->A) sub.
     p2c_slice_limit_with V x t Q (top,atlas) g xl W phi /\ p3_subseq sub
     ==> p2c_slice_limit_with (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) (top,atlas) g xl
                              (W o sub) (phi o sub)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_slice_limit_with; o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `!n:num. n <= sub n` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(W:num->B->bool) (SUC ((sub:num->num) k))` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LE_SUC_LT] THEN UNDISCH_TAC `p3_subseq sub` THEN
    REWRITE_TAC[p3_subseq] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "UNIONS" with _ -> false))
            (lhs(concl th)))) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `y:B` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:B->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
      EXISTS_TAC `(W:num->B->bool) ((sub:num->num) m)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->B->bool) m SUBSET W ((sub:num->num) m)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:B) IN s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
    DISCH_THEN(fun th -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC th) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]);;

(* A flow limit gives the slice limit at each of its times s, along the     *)
(* tail of the sequence where the maps are diffeomorphisms at time s.       *)

let P2BU_FLOW_TO_SLICE_AT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\ s IN J /\
     riemannian_metric atlas (g s)
     ==> ?N. p2c_slice_limit_with (\n. V (n + N)) (\n. x (n + N))
               (\n. t (n + N) + s / Q (n + N)) (\n. Q (n + N)) (top,atlas) (g s) xl
               (\n. W (n + N)) (\n. phi (n + N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `real_interval[s,s] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r:real = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `{xl:B}`; `0`; `&1`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  EXISTS_TAC `N:num` THEN REWRITE_TAC[p2c_slice_limit_with] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "UNIONS" with _ -> false))
            (lhs(concl th)))) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `y:B` THEN
      DISCH_THEN(X_CHOOSE_THEN `u:B->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
      EXISTS_TAC `(W:num->B->bool) (m + N)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + N)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        UNDISCH_TAC `(y:B) IN u` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    X_GEN_TAC `n:num` THEN
    USE_THEN "N" (MP_TAC o SPEC `n + N:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[REAL_LE_REFL];
    MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `K:B->bool`; `m:num`; `eta:real`] o
      check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
            (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
    EXISTS_TAC `k1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "k1" (MP_TAC o SPEC `n + N:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

(* Compact closures of the rescaled balls about x n at the times s of a     *)
(* flow limit with complete slice g s: they lie in the images of the        *)
(* compact closures of limit balls (LIM_BALL_IN).                           *)

let P2BU_CC_FROM_LIMIT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s.
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)
     ==> !A. &0 < A
             ==> ?N. !n. N <= n
                     ==> compact_in (rfs_vtop (V n) (t n + s / Q n))
                           (rfs_vtop (V n) (t n + s / Q n) closure_of
                            rfs_vball (V n) (t n + s / Q n) (x n) (A * inv(sqrt(Q n))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!n tau. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau)` (LABEL_TAC "haus") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(MATCH_MP P2CV_RV_SVS (SPEC `n:num`
      (ASSUME `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`))) THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`; `xl:B`; `A:real`; `A + &1`] LIM_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "bin")) THEN
  ABBREV_TAC `Kc = (top:B topology) closure_of
                   mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                            ((g:real->B->real^3^3) s) xl (A + &1)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `xl:B`;
                   `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                             ((g:real->B->real^3^3) s) xl (A + &1)`;
                   `A + &1`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                   ((g:real->B->real^3^3) s) xl (A + &1) SUBSET Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `Kc:B->bool`; `0`; `&1`] o
    check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
          (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; SUBSET; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r:real = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
  EXISTS_TAC `k0 + k1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "k1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `k0 + k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real` o CONJUNCT1)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `compact_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n))
                  (IMAGE ((phi:num->B->A) n) Kc)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology (top:B topology) (W(n:num))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE ((phi:num->B->A) n) Kc` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  USE_THEN "bin" (MP_TAC o SPECL [`n:num`; `z:A`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n) (x n) (A * inv(sqrt(Q n)))` THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool)
                 ((g:real->B->real^3^3) s) xl (A + &1) SUBSET Kc` THEN
  SET_TAC[]);;

(* Rescaled balls about x n at the time s of a flow limit lie, eventually,  *)
(* in slightly larger rescaled balls at t n, when g 0 <= g s on the limit   *)
(* (sec >= 0 there, LIM_METRIC_BACK): through LIM_BALL_IN at s, the distance *)
(* comparison RFAH_DIST_COMPARE and LIM_BALL_OUT at 0.                       *)

let P2BU_BALL_S_IN_0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s r.
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
     riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
     (!y v. y IN topspace top ==> v dot (g (&0) y ** v) <= v dot (g s y ** v)) /\ &0 < r
     ==> ?N. !n. N <= n
                 ==> rfs_vball (V n) (t n + s / Q n) (x n) (r * inv(sqrt(Q n))) SUBSET
                     rfs_vball (V n) (t n) (x n) ((r + &2) * inv(sqrt(Q n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!n tau. hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau)` (LABEL_TAC "haus") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(MATCH_MP P2CV_RV_SVS (SPEC `n:num`
      (ASSUME `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)`))) THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                        ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                            riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
  (LABEL_TAC "slices") THENL
   [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`; `xl:B`; `r:real`; `r + &1`] LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ARITH `a < a + &1`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "bin")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `r + &1`; `r + &2`] LIM_BALL_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `a + &1 < a + &2`] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "bout")) THEN
  EXISTS_TAC `k0 + k1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  USE_THEN "bin" (MP_TAC o SPECL [`n:num`; `z:A`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n) (x n) (r * inv(sqrt(Q n)))` THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl (r + &1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(w:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s) xl (r + &1)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) ((g:real->B->real^3^3) s) xl w` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `(g:real->B->real^3^3) (&0)`; `&1`;
                   `xl:B`; `w:B`] RFAH_DIST_COMPARE) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; SQRT_1];
    ALL_TAC] THEN
  USE_THEN "bout" (MP_TAC o SPECL [`n:num`; `w:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k0 + k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2CO_VBALL] THEN SIMP_TAC[]);;

(* Shi bounds at the time s of a flow limit, on the rescaled balls about    *)
(* x n at that time: P2BU_SHI_VIEW_CC with the compact closures of           *)
(* P2BU_CC_FROM_LIMIT, the balls inside the persisting balls at t n         *)
(* (P2BU_BALL_S_IN_0) and the RBU bound back to a0 = (s - Tr) / 2.           *)

let P2BU_SHI_AT_S = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A) Tr s.
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
     riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
     (!y v. y IN topspace top ==> v dot (g (&0) y ** v) <= v dot (g s y ** v)) /\
     p2bu_rbu V x t Q Tr /\ --Tr < s /\ s <= &0
     ==> !A l. &0 < A
               ==> ?CAl N. !n y. N <= n /\
                                 y IN rfs_vball (V n) (t n + s / Q n) (x n) (A * inv(sqrt(Q n)))
                                 ==> p3_vderiv2 (V n) l (t n + s / Q n) y <=
                                     CAl * Q n pow (l + 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  ABBREV_TAC `a0 = (s - Tr) / &2` THEN
  SUBGOAL_THEN `--Tr < a0 /\ a0 < s /\ a0 <= &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `p2bu_rbu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q Tr` THEN REWRITE_TAC[p2bu_rbu] THEN
  DISCH_THEN(MP_TAC o C MP (CONJ (ASSUME `--Tr < a0`) (ASSUME `a0 <= &0`)) o SPEC `a0:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "rbuK")) THEN
  MP_TAC(ISPECL [`l:num`; `max K (&1)`; `A:real`; `s - a0`] P2BU_SHI_VIEW_CC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` (LABEL_TAC "shi")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`] P2BU_CC_FROM_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&4 * A`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "cc")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`; `&4 * A`] P2BU_BALL_S_IN_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "inc")) THEN
  USE_THEN "rbuK" (MP_TAC o SPEC `&4 * A + &2`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "reg")) THEN
  MAP_EVERY EXISTS_TAC [`CA:real`; `N1 + N2 + N3:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ N3 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "reg" (MP_TAC o C MP (ASSUME `N3 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (LABEL_TAC "bd")) THEN
  USE_THEN "inc" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "incn") THEN
  USE_THEN "cc" (MP_TAC o C MP (ASSUME `N1 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "ccn") THEN
  SUBGOAL_THEN `(t:num->real) n + a0 / Q n < t n + s / Q n /\ t n + s / Q n <= t n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LADD; REAL_LT_DIV2_EQ;
                 REAL_ARITH `!t b:real. t + b <= t <=> b <= &0`; REAL_LE_LDIV_EQ;
                 REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n))
                          (rfs_vatlas (V n) (t n + s / Q n)) /\
    open_in (rfs_vtop (V n) (t n + s / Q n))
            (rfs_vball (V n) (t n) (x n) ((&4 * A + &2) * inv(sqrt(Q n))))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                   (rfs_vball (V n) (t n) (x n) ((&4 * A + &2) * inv(sqrt(Q n))))
                   (t n + a0 / Q n) (t n)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n) (x n) (A * inv(sqrt(Q n)))` THEN
    REWRITE_TAC[P2CO_VBALL; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `(t:num->real) n + s / Q n`; `(x:num->A) n`]
                P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "shi" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(x:num->A) n`; `(t:num->real) n + a0 / Q n`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* tau *)
    SUBGOAL_THEN `(Q:num->real) n * ((t n + s / Q n) - (t n + a0 / Q n)) = s - a0`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    (* persistence *)
    MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n + a0 / Q n`; `(t:num->real) n`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((&4 * A + &2) * inv(sqrt(Q n)))`;
      `(t:num->real) n + s / Q n`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    (* the bound *)
    MAP_EVERY X_GEN_TAC [`sg:real`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "bd" (MP_TAC o SPECL [`(sg - (t:num->real) n) * (Q:num->real) n`; `z:A`]) THEN
    SUBGOAL_THEN `(t:num->real) n + ((sg - t n) * Q n) / (Q:num->real) n = sg` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `a0 / (Q:num->real) n < sg - t n` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC];
        REWRITE_TAC[REAL_ARITH `x * q <= &0 <=> &0 <= --x * q`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + s / Q n) (x n) ((&4 * A) * inv(sqrt(Q n))) SUBSET
                     rfs_vball (V n) (t n) (x n) ((&4 * A + &2) * inv(sqrt(Q n)))` THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `kk <= mm ==> pp <= kk ==> pp <= mm`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* Radius comparison for rescaled balls: if Rk <= 4 R q then the ball of    *)
(* radius a R^(-1/2) q^(-1/2) is inside the ball of radius 2 a Rk^(-1/2).   *)

let P2BU_RADIUS_CMP = prove
 (`!a R q Rk. &0 <= a /\ &0 < R /\ &0 < q /\ &0 < Rk /\ Rk <= &4 * R * q
              ==> (a * inv(sqrt R)) * inv(sqrt q) <= (&2 * a) * inv(sqrt Rk)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(sqrt R) * inv(sqrt q) = inv(sqrt(R * q))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_INV_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * inv(sqrt Rk) = inv(sqrt Rk / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = a * (b * c)`;
                   REAL_ARITH `(&2 * a) * b = a * (&2 * b)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * sqrt(R * q) = sqrt(&4 * R * q)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&4) = &2` (fun th -> REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &2 * y ==> x / &2 <= y`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* MT Claim 11.6 at the times s of a flow limit of a blow-up sequence:     *)
(* P2BU_CLAIM_11_6_GEN on the tail of the sequence at times t n + s / Q n   *)
(* (P2BU_FLOW_TO_SLICE_AT), with the canonical neighbourhoods of the blow-up *)
(* hypothesis (times <= t n) and the Shi bounds of P2BU_SHI_AT_S.           *)

let P2BU_CANON_AT_S = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_SLICE_FIX_STATEMENT u w
     ==> ?K1 eps1. &1 <= K1 /\ &0 < eps1 /\
           !C eps kappa r0 mu V x t J (top:B topology) atlas g xl W (phi:num->B->A) Tr s.
              &1 < C /\ &0 < eps /\ eps <= eps1 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J
                (top,atlas) g xl W phi /\
              s IN J /\ riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
              riemannian_metric atlas (g (&0)) /\ mfd_complete (top,atlas) (g (&0)) /\
              (!y v. y IN topspace top ==> v dot (g (&0) y ** v) <= v dot (g s y ** v)) /\
              p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr /\
              --Tr < s /\ s <= &0 /\ connected_space top
              ==> !y. y IN topspace top /\ &4 < mfd_scalar atlas (g s) y
                      ==> ?U. rfs_canonical_nbhd (top,atlas) (g s) (&2 * C) (K1 * eps) y U`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CLAIM_11_6_GEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))))) THEN
  MAP_EVERY EXISTS_TAC [`K1:real`; `e1:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `s:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `Tr:real`; `s:real`] P2BU_SHI_AT_S) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "shi") THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`] P2BU_FLOW_TO_SLICE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  USE_THEN "gen" (MP_TAC o SPECL [`C:real`; `eps:real`; `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)`;
    `\n. (x:num->A) (n + N)`;
    `\n. (t:num->real) (n + N) + s / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)) (t (n + N)) ((x:num->A) (n + N))`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)) ((t:num->real) (n + N)) ((x:num->A) (n + N))`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `(g:real->B->real^3^3) s`; `xl:B`; `\n. (W:num->B->bool) (n + N)`;
    `\n. (phi:num->B->A) (n + N)`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `!t b:real. t + b <= t <=> b <= &0`] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> x <= &0`) THEN
      SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)) ((t:num->real) (n + N)) ((x:num->A) (n + N))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `p2c_flow_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) J
                       (top:B topology,atlas) g xl W phi` THEN
        REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
      MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `l:num`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `CAl:real` (X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0"))) THEN
      MAP_EVERY EXISTS_TAC [`CAl:real`; `N0:num`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `N0 <= n:num` THEN ARITH_TAC];
    SIMP_TAC[]]);;

(* Bounded curvature at bounded distance on the slices of a flow limit of a *)
(* blow-up sequence (the input of Cor 11.16 that MT takes from Thm 10.2 in  *)
(* the approximants): A2 at phi k y, time t k + s / Q k, where R >= Q k     *)
(* once R(y,s) >= 2, transferred by P2BU_POINT_CURV and LIM_BALL_OUT.        *)

let P2BU_BCBD_AT_S = prove
 (`!(u:A->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t J (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J
                (top,atlas) g xl W phi /\
              (!s. s IN J
                   ==> s <= &0 /\ riemannian_metric atlas (g s) /\
                       mfd_complete (top,atlas) (g s)) /\
              connected_space top
              ==> !A. ?D. !s y z. s IN J /\ y IN topspace top /\ z IN topspace top /\
                                  &2 <= mfd_scalar atlas (g s) y /\
                                  mfd_dist (top,atlas) (g s) y z <=
                                  A * inv(sqrt(mfd_scalar atlas (g s) y))
                                  ==> mfd_scalar atlas (g s) z <= D * mfd_scalar atlas (g s) y`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_THM_10_2_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a2"))) THEN
  EXISTS_TAC `e2:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Jp") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `!s'. s' IN J ==> riemannian_metric atlas ((g:real->B->real^3^3) s')`
  (LABEL_TAC "riemJ") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "Jp" (MP_TAC o C MP (ASSUME `(s':real) IN J`) o SPEC `s':real`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN
  ABBREV_TAC `A1 = max A (&1)` THEN
  SUBGOAL_THEN `&0 < A1 /\ A <= A1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "a2" (MP_TAC o SPECL [`eps:real`; `C:real`; `&4 * A1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))))) THEN
  EXISTS_TAC `D:real` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `z:B`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  USE_THEN "Jp" (STRIP_ASSUME_TAC o C MP (ASSUME `(s:real) IN J`) o SPEC `s:real`) THEN
  SUBGOAL_THEN `!n. &0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` (LABEL_TAC "Qpos") THENL
   [UNDISCH_TAC `p2c_flow_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) J
                   (top:B topology,atlas) g xl W phi` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_flow_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t (\n. rfs_vscalar (V n) (t n) (x n)) J
                   (top:B topology,atlas) g xl W phi` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->B->real^3^3) s) y` THEN
  ABBREV_TAC `Rz = mfd_scalar atlas ((g:real->B->real^3^3) s) z` THEN
  SUBGOAL_THEN `!ee. &0 < ee /\ ee <= R / &2 ==> Rz <= D * R + (D + &1) * ee`
  ASSUME_TAC THENL
   [X_GEN_TAC `ee:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `!n tau. ~(topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tau) = {})
                            ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                                riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)`
      (LABEL_TAC "slices") THENL
       [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                     `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                     `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                     `s:real`; `y:B`; `ee:real`] P2BU_POINT_CURV) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "cy")) THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                     `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                     `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                     `s:real`; `z:B`; `ee:real`] P2BU_POINT_CURV) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "cz")) THEN
      SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < inv(sqrt R)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                     `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                     `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                     `s:real`; `y:B`; `(&3 / &2 * A1) * inv(sqrt R)`; `(&2 * A1) * inv(sqrt R)`]
                    LIM_BALL_OUT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "bo")) THEN
      USE_THEN "Qinf" (X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4") o SPEC `D0:real`) THEN
      ABBREV_TAC `k = N1 + N2 + N3 + N4:num` THEN
      SUBGOAL_THEN `N1 <= k /\ N2 <= k /\ N3 <= k /\ N4 <= k:num` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) ((x:num->A) k)` THEN
      SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
       [EXPAND_TAC "q" THEN USE_THEN "Qpos" (ACCEPT_TAC o SPEC `k:num`); ALL_TAC] THEN
      ABBREV_TAC `tk = (t:num->real) k + s / q` THEN
      USE_THEN "cy" (MP_TAC o C MP (ASSUME `N1 <= k:num`) o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      USE_THEN "cz" (MP_TAC o C MP (ASSUME `N2 <= k:num`) o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
      ABBREV_TAC `Rk = mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tk) (rfs_vmetric (V k) tk)
                         ((phi:num->B->A) k y)` THEN
      ABBREV_TAC `Rzk = mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tk) (rfs_vmetric (V k) tk)
                          ((phi:num->B->A) k z)` THEN
      SUBGOAL_THEN `q < Rk /\ Rk <= &4 * R * q` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `R / &2 < Rk / q /\ Rk / q < &3 / &2 * R` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `R / &2 * q` THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
          EXISTS_TAC `(&3 / &2 * R) * q` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      (* A2 at phi k y, time tk *)
      USE_THEN "D" (MP_TAC o REWRITE_RULE[P2B9_RFS_VSCALAR] o
                     SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(phi:num->B->A) k y`; `tk:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
        FIRST
         [USE_THEN "views" (fun th -> MESON_TAC[th]) THEN NO_TAC;
          MAP_EVERY X_GEN_TAC [`y':A`; `s':real`] THEN STRIP_TAC THEN
          USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tk:real` THEN ASM_REWRITE_TAC[] THEN
            EXPAND_TAC "tk" THEN REWRITE_TAC[REAL_ARITH `!t b:real. t + b <= t <=> b <= &0`] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
            REWRITE_TAC[P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
          NO_TAC;
          USE_THEN "N4" (MP_TAC o C MP (ASSUME `N4 <= k:num`) o SPEC `k:num`) THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(phi:num->B->A) k z`) THEN
      ANTS_TAC THENL
       [USE_THEN "bo" (MP_TAC o SPECL [`k:num`; `z:B`]) THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
           [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `A * inv(sqrt R)` THEN
            ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        REWRITE_TAC[P2CO_VBALL] THEN
        MATCH_MP_TAC(SET_RULE `!s t (w:A). s SUBSET t ==> w IN s ==> w IN t`) THEN
        MATCH_MP_TAC P2CU_BALL_MONO THEN
        REWRITE_TAC[REAL_ARITH `&4 * a = &2 * &2 * a`] THEN
        MATCH_MP_TAC P2BU_RADIUS_CMP THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `Rzk / q <= D * (Rk / q)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        REWRITE_TAC[real_div; REAL_ARITH `(D * (a * b)) * q = D * a * (b * q)`] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
        ALL_TAC] THEN
      SUBGOAL_THEN `D * (Rk / q) <= D * R + D * ee` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < D + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (R / &2) ((Rz - D * R) / (&2 * (D + &1)))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D + &1) * min (R / &2) ((Rz - D * R) / (&2 * (D + &1))) <= (Rz - D * R) / &2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(D + &1) * ((Rz - D * R) / (&2 * (D + &1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < D + &1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The view metrics at two times on a persisting set with bounded curvature  *)
(* (MT Claim 8.8 unrestricted), earlier balls inside later balls and back,   *)
(* and Lemma 11.2 forward in time at one point.                              *)
(* ------------------------------------------------------------------------- *)

(* P2BU_VIEW_QF_CMP, P2BU_SQRT_EXP4, P2BU_VIEW_BALL_IN and P2BU_VIEW_BALL_OUT  *)
(* are in pc_p2c_bugq.                                                      *)

(* MT Cor 11.3 forward in time at one point: Lemma 11.2 with t' > t0 (the   *)
(* small ball about y carried forward by the identity of a persisting W).    *)

let P2BU_COR_11_3_FWD = prove
 (`!(u:A->bool) V C Q t0 y W tau.
     P2C_LEMMA_11_2_DB_STATEMENT u /\
     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) /\
     &0 < C /\ &0 < Q /\ &0 < tau /\
     (!x s. t0 <= s /\ s <= t0 + tau /\ x IN topspace(rfs_vtop V s) /\
            &4 * Q <= rfs_vscalar V s x
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x * sqrt(rfs_vscalar V s x) /\
                abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x pow 2) /\
     y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W t0 (t0 + tau)
     ==> !s. t0 <= s /\
             s < t0 + min tau (inv(&16 * C * (max (&0) (rfs_vscalar V t0 y) + &4 * Q)))
             ==> rfs_vscalar V s y <= &2 * (max (&0) (rfs_vscalar V t0 y) + &4 * Q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "db") STRIP_ASSUME_TAC)))))) THEN
  REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN DISCH_THEN(LABEL_TAC "l112") THEN
  ABBREV_TAC `R0 = max (&0) (rfs_vscalar V t0 (y:A))` THEN
  ABBREV_TAC `D = min tau (inv(&16 * C * (R0 + &4 * Q)))` THEN
  SUBGOAL_THEN `&0 < R0 + &4 * Q` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D /\ D <= tau /\ D <= inv(&16 * C * (R0 + &4 * Q))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t0`;
                 `W:A->bool`; `y:A`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rw:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r' = min rw (inv(&2 * C * sqrt(max (rfs_vscalar V t0 (y:A)) (&4 * Q))))` THEN
  SUBGOAL_THEN `inv((inv(&2 * sqrt Q)) pow 2) = &4 * Q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r'` ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball V t0 (y:A) r' SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball V t0 (y:A) rw` THEN
    ASM_REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
    EXPAND_TAC "r'" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V t0) (rfs_vball V t0 (y:A) r')` ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists V (rfs_vball V t0 (y:A) r') t0 (t0 + D)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`t0:real`; `t0 + tau`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN EXISTS_TAC `W:A->bool` THEN
    EXISTS_TAC `t0:real` THEN ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "l112" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `C:real`; `inv(&2 * sqrt Q)`; `y:A`; `t0:real`; `t0 + D`; `r':real`]) THEN
  SUBGOAL_THEN `min t0 (t0 + D) = t0 /\ max t0 (t0 + D) = t0 + D`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "db" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "r'" THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `abs((t0 + D) - t0) = abs D`] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < D ==> abs D = D`];
      DISCH_TAC THEN MATCH_MP_TAC P2CV_SLICE_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`t0:real`; `t0 + D`] THEN
      ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = t0` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN EXPAND_TAC "R0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "rfs_vscalar" with _ -> false))
        (concl th) &&
    not (can (find_term (fun u -> try fst(dest_const u) = "rfs_scalar_grad2" with _ -> false))
        (concl th)))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[P2CO_VBALL] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) t0`;
                   `y:A`; `r':real`] MFD_CENTRE_IN_BALL) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* MT Claim 11.17 (the region below -Tr), the general Claim 11.7 for slice   *)
(* limits, the extension context, and the rescaled balls at the time t n -   *)
(* Tr / Q n.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* P2BU_SCALAR_AT_S0, P2BU_SLICE_SEC and P2BU_SLICE_CURV_BOUND are in        *)
(* pc_p2c_bugq.                                                              *)

(* MT Claim 11.17, first part: with the Cor 11.16 bound K on the limit ball *)
(* B(xl,0,A+1) x (-Tr,0], Lemma 11.2 (P2BU_COR_11_3_POINT) from the time    *)
(* a0 = -Tr + dd/2 extends the bounds on the rescaled ball of radius A at   *)
(* t n back to -(Tr + dd/2), dd = min(1/(16 C (K + 5)), (T0 - Tr)/2, Tr).    *)

let P2BU_C1117_REGION = prove
 (`!(u:A->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g xl W (phi:num->B->A) Tr T0.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\
              &0 < Tr /\ Tr < T0 /\
              p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr /\
              p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                {s | --Tr < s /\ s <= &0} (top,atlas) g xl W phi /\
              (!s. --Tr < s /\ s <= &0
                   ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
              (!a. --Tr < a /\ a <= &0
                   ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                 ==> mfd_rm_norm atlas (g s) y <= K) /\
              (!A. ?K. !s y. --Tr < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                             ==> mfd_scalar atlas (g s) y <= K)
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 <= K /\
                            !n. N <= n
                                ==> rfs_persists (V n)
                                      (rfs_vball (V n) (t n) (x n)
                                         (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                                      (t n - (Tr + dl) / rfs_vscalar (V n) (t n) (x n)) (t n) /\
                                    !s y. t n - (Tr + dl) / rfs_vscalar (V n) (t n) (x n) < s /\
                                          s <= t n /\
                                          y IN rfs_vball (V n) (t n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                                          ==> y IN topspace(rfs_vtop (V n) s) /\
                                              p3_vrm (V n) s y <=
                                              K * rfs_vscalar (V n) (t n) (x n)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_CANON_DB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cdb"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "back") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rbu")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "rc")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (LABEL_TAC "c1116")))))))))))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "bseq" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  SUBGOAL_THEN `!n. &0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` (LABEL_TAC "Qpos") THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* constants *)
  USE_THEN "c1116" (X_CHOOSE_THEN `Kc0:real` (LABEL_TAC "Kc0") o SPEC `A + &1`) THEN
  ABBREV_TAC `Kl = max (&0) Kc0` THEN
  ABBREV_TAC `C1 = max C (&2)` THEN
  SUBGOAL_THEN `&0 <= Kl /\ Kc0 <= Kl /\ &0 < C1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kl"; "C1"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `max (&0) Kc0 = (Kl:real)` (K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&16 * C1 * (Kl + &5))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dd = min (min (inv(&16 * C1 * (Kl + &5))) ((T0 - Tr) / &2)) Tr` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= inv(&16 * C1 * (Kl + &5)) /\ dd <= (T0 - Tr) / &2 /\ dd <= Tr`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `min (min (inv(&16 * C1 * (Kl + &5))) ((T0 - Tr) / &2)) Tr = (dd:real)`
    (K ALL_TAC) THEN
  ABBREV_TAC `a0 = --Tr + dd / &2` THEN
  ABBREV_TAC `a1 = --Tr + dd / &4` THEN
  SUBGOAL_THEN `--Tr < a1 /\ a1 <= &0 /\ a1 < a0 /\ --Tr < a0 /\ a0 <= &0 /\ a0 < &0 /\
                a0 - dd = --(Tr + dd / &2) /\ Tr + dd < T0 /\ &0 < Tr + dd`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "a1"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* RBU at a1, the rm bound of the limit at a0 *)
  USE_THEN "rbu" (MP_TAC o C MP (CONJ (ASSUME `--Tr < a1`) (ASSUME `a1 <= &0`)) o
                  SPEC `a1:real` o BETA_RULE o REWRITE_RULE[p2bu_rbu]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  USE_THEN "rmb" (MP_TAC o C MP (CONJ (ASSUME `--Tr < a0`) (ASSUME `a0 <= &0`)) o
                  SPEC `a0:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kr:real` (LABEL_TAC "Kr")) THEN
  (* the scalar curvature at time a0 on the balls at t n *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `{s:real | --Tr < s /\ s <= &0}`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `a0:real`; `A:real`; `Kl:real`; `max (&0) Kr`] P2BU_SCALAR_AT_S0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `&0 <= max (&0) x`] THEN REPEAT CONJ_TAC THEN
    FIRST
     [USE_THEN "views" (fun th -> MESON_TAC[th]) THEN NO_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "rc" (MP_TAC o SPEC `s:real`) THEN
      ASM_SIMP_TAC[] THEN NO_TAC;
      USE_THEN "rc" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN NO_TAC;
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN USE_THEN "Kr" (MP_TAC o SPECL [`a0:real`; `y:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; REAL_ARITH_TAC] THEN NO_TAC;
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      USE_THEN "Kc0" (MP_TAC o SPECL [`a0:real`; `y:B`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  (* persistence back to Tr + dd *)
  USE_THEN "back" (MP_TAC o SPEC `Tr + dd`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2c_vblowup_back] THEN DISCH_THEN(LABEL_TAC "bk") THEN
  USE_THEN "bk" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2") o SPEC `A + &1`) THEN
  USE_THEN "bk" (X_CHOOSE_THEN `N2a:num` (LABEL_TAC "N2a") o SPEC `A:real`) THEN
  USE_THEN "K0" (X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3") o C MP (ASSUME `&0 < A`) o
                 SPEC `A:real`) THEN
  USE_THEN "Qinf" (X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4") o SPEC `&1`) THEN
  MAP_EVERY EXISTS_TAC [`dd / &2`; `max K0 (&4 * (Kl + &5) + &12 + &2 * exp(&4))`;
                        `N1 + N2 + N2a + N3 + N4:num`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> &0 <= max a b`) THEN
    MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ N2a <= n /\ N3 <= n /\ N4 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 + N2a + N3 + N4 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "p2" o CONJUNCT1) THEN
  USE_THEN "N2a" (MP_TAC o C MP (ASSUME `N2a <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "p2a" o CONJUNCT1) THEN
  USE_THEN "N3" (MP_TAC o C MP (ASSUME `N3 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "r3" o CONJUNCT2) THEN
  USE_THEN "N4" (MP_TAC o C MP (ASSUME `N4 <= n:num`) o SPEC `n:num`) THEN DISCH_TAC THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  SUBGOAL_THEN `a0 / q < &0 /\ (Tr + dd) * inv q = (Tr + dd) / q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO]; REWRITE_TAC[real_div]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(Tr + dd) * inv q = (Tr + dd) / q`]) THEN
  SUBGOAL_THEN `(t:num->real) n - (Tr + dd) / q < t n - (Tr + dd / &2) / q /\
                t n - (Tr + dd / &2) / q = (t n + a0 / q) - dd / q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `a0 - dd = --(Tr + dd / &2)` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dd) / q`; `(t:num->real) n`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((A + &1) * inv(sqrt q))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) (A * inv(sqrt q))` THEN
    REWRITE_TAC[P2CO_VBALL] THEN
    MATCH_MP_TAC(SET_RULE `!s t (w:A). s SUBSET t ==> w IN s ==> w IN t`) THEN
    MATCH_MP_TAC P2CU_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN
                    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!sg. t n - (Tr + dd) / q < sg /\ sg <= (t:num->real) n
                     ==> open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) sg)
                           (rfs_vball (V n) (t n) (x n) ((A + &1) * inv(sqrt q)))`
  (LABEL_TAC "op") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (rfs_vball (V n) (t n) (x n) ((A + &1) * inv(sqrt q)))
                   (t n - (Tr + dd) / q) (t n)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `sg:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` ASSUME_TAC THENL
   [USE_THEN "op" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s <= (t:num->real) n + a0 / q` THENL
   [(* Lemma 11.2 from time t n + a0 / q *)
    USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE
      [ASSUME `rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n) = q`]) THEN
    MP_TAC(ISPECL [`u:A->bool`; `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `C1:real`; `q:real`;
                   `(t:num->real) n + a0 / q`; `y:A`;
                   `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((A + &1) * inv(sqrt q))`;
                   `dd / q`] P2BU_COR_11_3_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`z:A`; `s':real`] THEN STRIP_TAC THEN
        USE_THEN "cdb" (MP_TAC o SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `C:real`; `eps:real`; `z:A`; `s':real`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[]];
        USE_THEN "op" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
        MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dd) / q`; `(t:num->real) n`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `R0 = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n + a0 / q) (y:A)` THEN
    SUBGOAL_THEN `max (&0) R0 + &4 * q <= (Kl + &5) * q` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= Kl * q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `dd / q <= inv(&16 * C1 * (max (&0) R0 + &4 * q))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < max (&0) R0 + &4 * q` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&16 * C1 * (Kl + &5)) / q` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
        SUBGOAL_THEN `inv(&16 * C1 * (Kl + &5)) / q = inv(&16 * C1 * ((Kl + &5) * q))`
        SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (&2 * (Kl + &5)) + &12 + &2 * exp(&4)) * q` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BU_VIEW_PINCH_RM_Q THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        UNDISCH_TAC `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)` THEN
        USE_THEN "views" (MP_TAC o SPEC `n:num`) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (el 2 (CONJUNCTS th)) (ASSUME `s < &0`)]) THEN
        REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    (* RBU on [a1,0] *)
    USE_THEN "r3" (MP_TAC o SPECL [`(s - (t:num->real) n) * q`; `y:A`]) THEN
    SUBGOAL_THEN `(t:num->real) n + ((s - t n) * q) / q = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `a0 / q < s - (t:num->real) n` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_ARITH `x * q <= &0 <=> &0 <= --x * q`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `kk <= mm ==> pp <= kk ==> pp <= mm`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* The context of the extension step (MT Prop 11.10): the blow-up sequence  *)
(* with backward persistence up to T0, RBU(Tr), the flow limit on (-Tr,0]   *)
(* with its properties, and the Cor 11.16 bound.                             *)

let p2bu_extctx = new_definition
 `p2bu_extctx (C:real,eps:real,kappa:real,r0:real,mu:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) (T0:real) (Tr:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) <=>
    p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\
    (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
    (!A. ?N. !n. N <= n
                 ==> compact_in (rfs_vtop (V n) (t n))
                       (rfs_vtop (V n) (t n) closure_of
                        rfs_vball (V n) (t n) (x n)
                          (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
    (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\
    &0 < Tr /\ Tr < T0 /\
    p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr /\
    p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
      {s | --Tr < s /\ s <= &0} (top,atlas) g xl W phi /\
    connected_space top /\
    (!s. --Tr < s /\ s <= &0
         ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
             (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
    (!a b. --Tr < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
    (!a. --Tr < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!a. --Tr < a /\ a <= &0
         ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                       ==> mfd_rm_norm atlas (g s) y <= K) /\
    (!A. ?K. !s y. --Tr < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                   ==> mfd_scalar atlas (g s) y <= K)`;;


(* In the extension context, g 0 <= g s on the limit (LIM_METRIC_BACK).     *)

let P2BU_EXTCTX_METRIC_BACK = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A) s.
     p2bu_extctx (C,eps,kappa,r0,mu) V x t T0 Tr (top,atlas) g xl W phi /\
     --Tr < s /\ s <= &0
     ==> !y v. y IN topspace top ==> v dot (g (&0) y ** v) <= v dot (g s y ** v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_extctx] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_METRIC_BACK THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `(s - Tr) / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "rfs_flow_upto" with _ -> false))
          (concl th))) THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s':real`; `z:B`; `u:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "mfd_sectional" with _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* Facts of the extension context in the forms used below.                 *)

let P2BU_EXTCTX_FACTS = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
     p2bu_extctx (C,eps,kappa,r0,mu) V x t T0 Tr (top,atlas) g xl W phi
     ==> (!n. p2c_regular_view (V n) /\ rfs_pinched (V n) /\
              (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
              x n IN topspace(rfs_vtop (V n) (t n))) /\
         (!n. &0 < rfs_vscalar (V n) (t n) (x n)) /\
         (!n tau. hausdorff_space (rfs_vtop (V n) tau)) /\
         (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                      riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
         (!s. --Tr < s /\ s <= &0
              ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
         (!s. --Tr < s /\ s <= &0
              ==> !y v. y IN topspace top ==> v dot (g (&0) y ** v) <= v dot (g s y ** v)) /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views") (K ALL_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o BETA_RULE o REWRITE_RULE[p2c_flow_limit_with] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_flow_limit_with" with _ -> false))
        (concl th))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "views" (MP_TAC o MATCH_MP P2CV_RV_SVS o CONJUNCT1 o SPEC `n:num`) THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    MATCH_MP_TAC P2CO_REGULAR_SLICES THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> try fst(dest_const u) = "mfd_sectional" with _ -> false))
          (concl th))) THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BU_EXTCTX_METRIC_BACK THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`;
      `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[]]);;

(* The rescaled balls at the time t n - Tr / Q n: inside the balls at t n   *)
(* of radius 2A + 4, with compact closures.  Through the time s = -Tr + eta *)
(* of the flow limit: P2BU_VIEW_BALL_IN on the region of P2BU_C1117_REGION  *)
(* (eta so small that the distortion factor exp(2 K eta) is <= 2), then     *)
(* P2BU_BALL_S_IN_0 and P2BU_CC_FROM_LIMIT at s.                             *)

let P2BU_TT_BALL = prove
 (`!(u:A->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_extctx (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top,atlas) g xl W phi
              ==> !A. &0 < A
                      ==> ?N. !n. N <= n
                              ==> rfs_vball (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) SUBSET
                                  rfs_vball (V n) (t n) (x n)
                                    ((&2 * A + &4) * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) /\
                                  compact_in
                                    (rfs_vtop (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)))
                                    (rfs_vtop (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n))
                                     closure_of
                                     rfs_vball (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n))
                                       (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_C1117_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1117"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx")))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "ctx" (MP_TAC o MATCH_MP P2BU_EXTCTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcJ") (CONJUNCTS_THEN2 (LABEL_TAC "mback")
    STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "ctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  (* the region at radius 2A + 4 *)
  USE_THEN "c1117" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * A + &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))))) THEN
  ABBREV_TAC `eta = min (Tr / &2) (inv(&4 * (K + &1)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= Tr / &2 /\ &2 * K * eta <= inv(&2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&4 * (K + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * K * inv(&4 * (K + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "eta" THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&2 * K * inv(&4 * (K + &1)) = (K / (K + &1)) * inv(&2)` SUBST1_TAC THENL
         [MATCH_MP_TAC(REAL_FIELD `&0 < k + &1 ==> &2 * k * inv(&4 * (k + &1)) =
                                     (k / (k + &1)) * inv(&2)`) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= k ==> &0 < k + &1`] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * K * eta) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * (&2 * K * eta)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s = --Tr + eta` THEN
  SUBGOAL_THEN `--Tr < s /\ s <= &0 /\ (s:real) IN {s | --Tr < s /\ s <= &0} /\
                (&0) IN {s | --Tr < s /\ s <= &0}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "rcJ" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "rcJ" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* balls at s inside balls at t n, compact closures at s *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
                 `{s:real | --Tr < s /\ s <= &0}`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`; `&2 * A + &2`] P2BU_BALL_S_IN_0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "mback" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
           ASM_REAL_ARITH_TAC;
           USE_THEN "views" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
                 `{s:real | --Tr < s /\ s <= &0}`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s:real`] P2BU_CC_FROM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * A + &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ N3 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N1" (MP_TAC o C MP (ASSUME `N1 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pW") (LABEL_TAC "bW")) THEN
  USE_THEN "N2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "inc") THEN
  USE_THEN "N3" (MP_TAC o C MP (ASSUME `N3 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "ccs") THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  ABBREV_TAC `b = (t:num->real) n + s / q` THEN
  ABBREV_TAC `tt = (t:num->real) n - Tr / q` THEN
  ABBREV_TAC `Wn = rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((&2 * A + &4) * inv(sqrt q))` THEN
  SUBGOAL_THEN `&0 < inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:num->real) n - (Tr + dl) / q < tt /\ tt < b /\ b <= t n`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tt"; "b"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - a < t + b <=> --a < b`] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t + b <= t <=> b <= &0`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b) Wn /\ open_in (rfs_vtop (V n) tt) Wn`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) Wn (t n - (Tr + dl) / q) (t n)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `b:real` th) THEN MP_TAC(SPEC `tt:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN Wn` ASSUME_TAC THENL
   [EXPAND_TAC "Wn" THEN REWRITE_TAC[P2CO_VBALL] THEN
    USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `(t:num->real) n`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `Wn:A->bool` THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `b:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `R = (&2 * A + &1) * inv(sqrt q)` THEN
  SUBGOAL_THEN `R < (&2 * A + &2) * inv(sqrt q)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b closure_of rfs_vball (V n) b (x n) R SUBSET Wn`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b (x n) ((&2 * A + &2) * inv(sqrt q))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b,rfs_vatlas (V n) b)
                    (rfs_vmetric (V n) b) (x n) R` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
        REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
        GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "Wn" THEN
      UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b (x n) ((&2 * A + &2) * inv(sqrt q)) SUBSET
                   rfs_vball (V n) (t n) (x n) (((&2 * A + &2) + &2) * inv(sqrt q))` THEN
      REWRITE_TAC[REAL_ARITH `(&2 * A + &2) + &2 = &2 * A + &4`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `Wn:A->bool`; `(t:num->real) n - (Tr + dl) / q`; `b:real`;
                 `K * q`; `tt:real`; `(x:num->A) n`; `(x:num->A) n`; `R:real`;
                 `inv(sqrt q) / &2`; `A * inv(sqrt q)`] P2BU_VIEW_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dl) / q`; `(t:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`t':real`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "bW" (MP_TAC o SPECL [`t':real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[P2CO_VBALL] THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&2 * (K * q) * (b - tt) = &2 * K * eta` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["b"; "tt"; "s"] THEN UNDISCH_TAC `&0 < q` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (A * inv(sqrt q))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b (x n) R SUBSET
                rfs_vtop (V n) b closure_of rfs_vball (V n) b (x n) R` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[P2CO_VBALL; mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b (x n) R` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b closure_of rfs_vball (V n) b (x n) R` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b closure_of rfs_vball (V n) b (x n) R` THEN
  SUBGOAL_THEN `subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b) Wn = subtopology (rfs_vtop (V n) tt) Wn`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `Wn:A->bool`; `(t:num->real) n - (Tr + dl) / q`; `b:real`;
                   `tt:real`; `b:real`] P2CV_SLICE_DIFFEO) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LT_IMP_LE; REAL_LE_REFL] THEN
      MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dl) / q`; `(t:num->real) n`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt) Kc` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in (subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b) Wn) Kc` MP_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME
      `subtopology (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b) Wn = subtopology (rfs_vtop (V n) tt) Wn`]) THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `Kc:A->bool` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) b (x n) R` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Shi bounds and a volume bound at the time t n - Tr / Q n, compactness of  *)
(* those slices and the curvature bound of their limit (MT Claim 11.17,      *)
(* second part).                                                             *)
(* ------------------------------------------------------------------------- *)

(* P2BU_SLICE_DBOUND is in pc_p2c_bugq.                                      *)

(* Shi bounds at the time t n - Tr / Q n on the rescaled balls about x n:  *)
(* P2BU_SHI_VIEW_CC with the compact closures and inclusions of            *)
(* P2BU_TT_BALL and the region of P2BU_C1117_REGION.                         *)

let P2BU_TT_SHI = prove
 (`!(u:A->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_extctx (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top,atlas) g xl W phi
              ==> !A l. &0 < A
                        ==> ?CAl N. !n y. N <= n /\
                              y IN rfs_vball (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n))
                                     (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                              ==> p3_vderiv2 (V n) l (t n - Tr / rfs_vscalar (V n) (t n) (x n)) y
                                  <= CAl * rfs_vscalar (V n) (t n) (x n) pow (l + 2)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_C1117_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1117"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_TT_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ttb"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "ctx")))) THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
  USE_THEN "ctx" (MP_TAC o MATCH_MP P2BU_EXTCTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcJ") (CONJUNCTS_THEN2 (LABEL_TAC "mback")
    STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "ctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  USE_THEN "c1117" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * (&4 * A) + &4`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))))) THEN
  USE_THEN "ttb" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(MP_TAC o SPEC `&4 * A`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  MP_TAC(ISPECL [`l:num`; `max K (&1)`; `A:real`; `dl / &2`] P2BU_SHI_VIEW_CC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` (LABEL_TAC "shi")) THEN
  MAP_EVERY EXISTS_TAC [`CA:real`; `N1 + N2:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N1" (MP_TAC o C MP (ASSUME `N1 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pW") (LABEL_TAC "bW")) THEN
  USE_THEN "N2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inc") (LABEL_TAC "cc")) THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  ABBREV_TAC `tt = (t:num->real) n - Tr / q` THEN
  ABBREV_TAC `Wn = rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((&2 * (&4 * A) + &4) * inv(sqrt q))` THEN
  SUBGOAL_THEN `&0 < inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:num->real) n - (Tr + dl) / q < t n - (Tr + dl / &2) / q /\
                t n - (Tr + dl / &2) / q < tt /\ tt <= t n /\
                q * (tt - (t n - (Tr + dl / &2) / q)) = dl / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - b <= t <=> &0 <= b`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt) Wn` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) Wn (t n - (Tr + dl) / q) (t n)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `tt:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) (A * inv(sqrt q))` THEN
    REWRITE_TAC[P2CO_VBALL; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `tt:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "shi" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(x:num->A) n`; `(t:num->real) n - (Tr + dl / &2) / q`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dl) / q`; `(t:num->real) n`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`Wn:A->bool`; `tt:real`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           EXPAND_TAC "Wn" THEN ASM_REWRITE_TAC[] THEN NO_TAC;
           REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * q` THEN CONJ_TAC THENL
     [USE_THEN "bW" (MP_TAC o SPECL [`s:real`; `z:A`]) THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          USE_THEN "inc" MP_TAC THEN
          UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) ((&4 * A) * inv(sqrt q))` THEN
          SET_TAC[]];
        SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]]);;

(* A volume bound at the time t n - Tr / Q n on the rescaled ball of radius *)
(* eta about x n: kappa-noncollapsing there (the backward hypothesis) on    *)
(* the scale eta Q n^(-1/2), eta = min 1 (min (sqrt dl) (1 / sqrt K)).        *)

let P2BU_TT_VOL = prove
 (`!(u:A->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_extctx (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top,atlas) g xl W phi
              ==> ?eta N. &0 < eta /\
                    !n. N <= n
                        ==> ?v. mfd_has_volume
                                  (rfs_vtop (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)),
                                   rfs_vatlas (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)))
                                  (rfs_vmetric (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)))
                                  (rfs_vball (V n) (t n - Tr / rfs_vscalar (V n) (t n) (x n)) (x n)
                                     (eta * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))) v /\
                                kappa * (eta * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) pow 3
                                <= v`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_C1117_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1117"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_TT_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ttb"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "ctx")))) THEN
  USE_THEN "ctx" (MP_TAC o MATCH_MP P2BU_EXTCTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcJ") (CONJUNCTS_THEN2 (LABEL_TAC "mback")
    STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "ctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (K ALL_TAC)))))) THEN
  USE_THEN "c1117" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * &1 + &4`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))))) THEN
  USE_THEN "ttb" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  (* noncollapsing at x n and t n - Tr / Q n *)
  FIRST_ASSUM(MP_TAC o SPEC `(Tr + T0) / &2` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_back" with _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2c_vblowup_back] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3") o SPEC `&1`) THEN
  ABBREV_TAC `K1 = max K (&1)` THEN
  SUBGOAL_THEN `&0 < K1 /\ K <= K1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (&1) (min (sqrt dl) (inv(sqrt K1)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 /\ eta pow 2 <= dl /\ K1 * eta pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt dl /\ &0 < inv(sqrt K1) /\ sqrt dl pow 2 = dl /\
                  inv(sqrt K1) pow 2 = inv K1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_INV];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eta <= sqrt dl /\ eta <= inv(sqrt K1)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt dl pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 * inv(sqrt K1) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  USE_THEN "Qinf" (X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4") o SPEC `(eta / r0) pow 2`) THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `N1 + N2 + N3 + N4:num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n /\ N2 <= n /\ N3 <= n /\ N4 <= n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N1 + N2 + N3 + N4 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "N1" (MP_TAC o C MP (ASSUME `N1 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pW") (LABEL_TAC "bW")) THEN
  USE_THEN "N2" (MP_TAC o C MP (ASSUME `N2 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inc") (K ALL_TAC)) THEN
  USE_THEN "N3" (MP_TAC o C MP (ASSUME `N3 <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(LABEL_TAC "nc" o CONJUNCT2) THEN
  USE_THEN "N4" (MP_TAC o C MP (ASSUME `N4 <= n:num`) o SPEC `n:num`) THEN DISCH_TAC THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)` THEN
  ABBREV_TAC `tt = (t:num->real) n - Tr / q` THEN
  ABBREV_TAC `Wn = rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) ((&2 * &1 + &4) * inv(sqrt q))` THEN
  ABBREV_TAC `r = eta * inv(sqrt q)` THEN
  SUBGOAL_THEN `&0 < sqrt q /\ sqrt q pow 2 = q /\ &0 < inv(sqrt q)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= &1 * inv(sqrt q) /\ r pow 2 <= dl / q /\
                K * q <= inv(r pow 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r pow 2 = eta pow 2 / q` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_REWRITE_TAC[real_div];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "r" THEN REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `eta / r0 < sqrt q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_INV_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      SUBGOAL_THEN `(K * q) * eta pow 2 = (K * eta pow 2) * q` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K1 * eta pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:num->real) n - (Tr + dl) / q <= tt - r pow 2 /\ tt <= t n /\
                (t:num->real) n - (Tr + T0) / &2 / q < tt`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(Tr + dl) / q = Tr / q + dl / q` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `t - b <= t <=> &0 <= b`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN Wn` ASSUME_TAC THENL
   [EXPAND_TAC "Wn" THEN REWRITE_TAC[P2CO_VBALL] THEN
    USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `(t:num->real) n`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) (&1 * inv(sqrt q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN
    USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `(t:num->real) n`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt) Wn` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) Wn (t n - (Tr + dl) / q) (t n)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `tt:real`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `tt - r pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < a ==> t - a < t`) THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->A) n IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `Wn:A->bool` THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `tt:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) r SUBSET Wn` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) (&1 * inv(sqrt q))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "nc" (MP_TAC o SPECL [`tt:real`; `(x:num->A) n`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3_noncoll_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_parabolic_exists] THEN MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n - (Tr + dl) / q`; `(t:num->real) n`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`Wn:A->bool`; `tt:real`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM p3_vrm] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * q` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "bW" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) r SUBSET Wn` THEN
      UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) tt (x n) r` THEN SET_TAC[]]]);;

(* MT Claim 11.17, second part: the slices at t n - Tr / Q n converge along *)
(* a subsequence, and their limit has bounded curvature (the slice form of  *)
(* A4), so R <= D Q n on the rescaled balls of every radius at that time.  *)

let P2BU_TT_DBOUND = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
     P2C_CG_COMPACT_STATEMENT u w /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_extctx (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top,atlas) g xl W phi
              ==> ?sub D. p3_subseq sub /\ &0 < D /\
                    !A. &0 < A
                        ==> ?N. !n y. N <= n /\
                              y IN rfs_vball (V (sub n))
                                     (t (sub n) - Tr / rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                     (x (sub n))
                                     (A * inv(sqrt(rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))))
                              ==> rfs_vscalar (V (sub n))
                                    (t (sub n) - Tr / rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                    y <=
                                  D * rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_C1117_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1117"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_TT_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ttb"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_TT_SHI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tts"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_TT_VOL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ttv"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_SLICE_DBOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sdb"))) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 (min e4 e5))` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "ctx")))) THEN
  USE_THEN "ctx" (MP_TAC o MATCH_MP P2BU_EXTCTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcJ") (CONJUNCTS_THEN2 (LABEL_TAC "mback")
    STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "ctx" (STRIP_ASSUME_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  (* the base points lie in the slices at t n - Tr / Q n, eventually *)
  USE_THEN "c1117" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N0")))))) THEN
  SUBGOAL_THEN `!n. N0 <= n
                    ==> (x:num->A) n IN
                        topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                                   (t n - Tr / rfs_vscalar (V n) (t n) (x n)))`
  (LABEL_TAC "xin") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N0" (MP_TAC o C MP (ASSUME `N0 <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`(t:num->real) n - Tr / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)`;
                               `(x:num->A) n`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - b <= t <=> &0 <= b`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2CO_VBALL] THEN
      USE_THEN "slices" (MP_TAC o SPECL [`n:num`; `(t:num->real) n`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) n` THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* compactness, Shi and volume at t n - Tr / Q n *)
  USE_THEN "ttb" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "TB")] THEN
  USE_THEN "tts" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "TS")] THEN
  USE_THEN "ttv" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `Nv:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "TV")))) THEN
  (* the shifted sequence *)
  USE_THEN "sdb" (MP_TAC o SPECL [`C:real`; `eps:real`; `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N0)`;
    `\n. (x:num->A) (n + N0)`;
    `\n. (t:num->real) (n + N0) - Tr / rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N0)) (t (n + N0)) (x (n + N0))`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N0)) ((t:num->real) (n + N0)) ((x:num->A) (n + N0))`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "xin" MATCH_MP_TAC THEN ARITH_TAC;
      X_GEN_TAC `B:real` THEN USE_THEN "Qinf" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `N <= n:num` THEN ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `t - b <= t <=> &0 <= b`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN USE_THEN "Qpos" (MP_TAC o SPEC `n + N0:num`) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "TB" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "N" (MP_TAC o SPEC `n + N0:num`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `N <= n:num` THEN ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "TS" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `l:num`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `CAl:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "N"))) THEN
      MAP_EVERY EXISTS_TAC [`CAl:real`; `N:num`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `N <= n:num` THEN ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`eta:real`; `kappa:real`; `Nv:num`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "TV" MATCH_MP_TAC THEN
      UNDISCH_TAC `Nv <= n:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub0:num->num` (X_CHOOSE_THEN `D:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))))) THEN
  MAP_EVERY EXISTS_TAC [`\n. (sub0:num->num) n + N0`; `D:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [UNDISCH_TAC `p3_subseq (sub0:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
         MESON_TAC[LT_ADD_RCANCEL];
         USE_THEN "D" ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Lemma 11.2 on both sides of a time, and the extension step of MT Prop     *)
(* 11.10: RBU(Tr) extends to RBU(Tr + d/2) along a subsequence.              *)
(* ------------------------------------------------------------------------- *)

(* Lemma 11.2 on both sides of t0 at one point: if R(y,t0) <= D Q and an   *)
(* open W about y persists over (t0 - tau, t0 + tau] with tau Q <=          *)
(* 1/(16 C (D + 4)), then R(y,s) <= 2 (D + 4) Q for |s - t0| < tau.          *)

let P2BU_DB_AROUND = prove
 (`!(u:A->bool) V C Q t0 y W tau D.
     P2C_LEMMA_11_2_DB_STATEMENT u /\
     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) /\
     &0 < C /\ &0 < Q /\ &0 < tau /\ &0 <= D /\ tau * Q <= inv(&16 * C * (D + &4)) /\
     (!x s. s <= t0 + tau /\ x IN topspace(rfs_vtop V s) /\
            &4 * Q <= rfs_vscalar V s x
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x * sqrt(rfs_vscalar V s x) /\
                abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x pow 2) /\
     y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W (t0 - tau) (t0 + tau) /\
     rfs_vscalar V t0 y <= D * Q
     ==> !s. t0 - tau < s /\ s < t0 + tau ==> rfs_vscalar V s y <= &2 * (D + &4) * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `max (&0) (rfs_vscalar V t0 (y:A)) + &4 * Q <= (D + &4) * Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= D * Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau <= inv(&16 * C * (max (&0) (rfs_vscalar V t0 (y:A)) + &4 * Q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&16 * C * ((D + &4) * Q))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `inv(&16 * C * ((D + &4) * Q)) = inv(&16 * C * (D + &4)) / Q` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (max (&0) (rfs_vscalar V t0 (y:A)) + &4 * Q) <= &2 * (D + &4) * Q`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= t0` THENL
   [MP_TAC(ISPECL [`u:A->bool`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`;
                   `C:real`; `Q:real`; `t0:real`; `y:A`; `W:A->bool`; `tau:real`]
                  P2BU_COR_11_3_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`z:A`; `s':real`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
        MAP_EVERY EXISTS_TAC [`t0 - tau`; `t0 + tau`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a`] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`u:A->bool`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)`;
                   `C:real`; `Q:real`; `t0:real`; `y:A`; `W:A->bool`; `tau:real`]
                  P2BU_COR_11_3_FWD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`z:A`; `s':real`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
        MAP_EVERY EXISTS_TAC [`t0 - tau`; `t0 + tau`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a`] THEN
    ASM_REAL_ARITH_TAC]);;

(* MT Prop 11.10, the extension step: in the extension context, along a    *)
(* subsequence, RBU(Tr) extends to RBU(Tr + d/2) with d = min(1/(16 C (D +  *)
(* 4)), Tr, T0 - Tr), D the curvature bound at -Tr (P2BU_TT_DBOUND): the    *)
(* balls at t n lie in balls at -Tr (P2BU_VIEW_BALL_OUT on the region of    *)
(* P2BU_C1117_REGION), and Lemma 11.2 on both sides of -Tr                  *)
(* (P2BU_DB_AROUND) with pinching gives one bound uniform in the radius.    *)

let P2BU_EXT_STEP = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
     P2C_CG_COMPACT_STATEMENT u w /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_extctx (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top,atlas) g xl W phi
              ==> ?sub dl. p3_subseq sub /\ &0 < dl /\
                    p2bu_rbu (\n. V (sub n)) (x o sub) (t o sub)
                      ((\n. rfs_vscalar (V n) (t n) (x n)) o sub) (Tr + dl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_TT_DBOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ttd"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_C1117_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1117"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_CANON_DB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cdb"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "ctx")))) THEN
  USE_THEN "ctx" (MP_TAC o MATCH_MP P2BU_EXTCTX_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "haus") (CONJUNCTS_THEN2 (LABEL_TAC "slices")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcJ") (CONJUNCTS_THEN2 (LABEL_TAC "mback")
    STRIP_ASSUME_TAC)))))) THEN
  USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2bu_extctx]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bseq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "back")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rbu") STRIP_ASSUME_TAC))))))) THEN
  USE_THEN "bseq" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  (* the curvature bound at -Tr *)
  USE_THEN "ttd" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Db"))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C1 = max C (&2)` THEN
  SUBGOAL_THEN `&0 < C1` ASSUME_TAC THENL [EXPAND_TAC "C1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&16 * C1 * (D + &4))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = min (inv(&16 * C1 * (D + &4))) (min Tr (T0 - Tr))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= inv(&16 * C1 * (D + &4)) /\ d <= Tr /\ d <= T0 - Tr`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `d / &2`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2bu_rbu; o_THM] THEN
  X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  ABBREV_TAC `a1 = --Tr + d / &2` THEN
  SUBGOAL_THEN `--Tr < a1 /\ a1 <= &0 /\ Tr + d / &2 < T0 /\ &0 < Tr + d / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "a1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "rbu" (MP_TAC o C MP (CONJ (ASSUME `--Tr < a1`) (ASSUME `a1 <= &0`)) o
                  SPEC `a1:real` o BETA_RULE o REWRITE_RULE[p2bu_rbu]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (LABEL_TAC "K1")) THEN
  EXISTS_TAC `max K1 (&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4))` THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  (* persistence back to Tr + d/2 *)
  USE_THEN "back" (MP_TAC o SPEC `Tr + d / &2`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2c_vblowup_back] THEN DISCH_THEN(LABEL_TAC "bk") THEN
  USE_THEN "bk" (X_CHOOSE_THEN `Nb:num` (LABEL_TAC "Nb") o SPEC `A + &1`) THEN
  USE_THEN "bk" (X_CHOOSE_THEN `Nba:num` (LABEL_TAC "Nba") o SPEC `A:real`) THEN
  (* the region of radius A + 1 *)
  USE_THEN "c1117" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `A + &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl2:real` (X_CHOOSE_THEN `K2:real` (X_CHOOSE_THEN `Nc:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Nc")))))) THEN
  USE_THEN "Db" (MP_TAC o SPEC `exp(&2 * K2 * Tr) * A`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nd:num` (LABEL_TAC "Nd")) THEN
  USE_THEN "K1" (X_CHOOSE_THEN `Nr:num` (LABEL_TAC "Nr") o C MP (ASSUME `&0 < A`) o
                 SPEC `A:real`) THEN
  USE_THEN "Qinf" (X_CHOOSE_THEN `Nq:num` (LABEL_TAC "Nq") o SPEC `&1`) THEN
  EXISTS_TAC `Nb + Nba + Nc + Nd + Nr + Nq:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "ge" (ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `m = (sub:num->num) n` THEN
  SUBGOAL_THEN `Nb <= m /\ Nba <= m /\ Nc <= m /\ Nd <= n:num /\ Nr <= m /\ Nq <= m:num`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n <= m:num` THEN
    UNDISCH_TAC `Nb + Nba + Nc + Nd + Nr + Nq <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Nb" (MP_TAC o C MP (ASSUME `Nb <= m:num`) o SPEC `m:num`) THEN
  DISCH_THEN(LABEL_TAC "pb" o CONJUNCT1) THEN
  USE_THEN "Nba" (MP_TAC o C MP (ASSUME `Nba <= m:num`) o SPEC `m:num`) THEN
  DISCH_THEN(LABEL_TAC "pba" o CONJUNCT1) THEN
  USE_THEN "Nc" (MP_TAC o C MP (ASSUME `Nc <= m:num`) o SPEC `m:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pc") (LABEL_TAC "bc")) THEN
  USE_THEN "Nd" (LABEL_TAC "dn" o REWRITE_RULE[ASSUME `Nd <= n:num`;
                                              ASSUME `(sub:num->num) n = m`] o SPEC `n:num`) THEN
  USE_THEN "Nr" (MP_TAC o C MP (ASSUME `Nr <= m:num`) o SPEC `m:num`) THEN
  DISCH_THEN(LABEL_TAC "r1" o CONJUNCT2) THEN
  USE_THEN "Nq" (ASSUME_TAC o C MP (ASSUME `Nq <= m:num`) o SPEC `m:num`) THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `m:num`) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
  ABBREV_TAC `q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m) ((x:num->A) m)` THEN
  ABBREV_TAC `tt = (t:num->real) m - Tr / q` THEN
  ABBREV_TAC `tau = (d / &2) / q` THEN
  SUBGOAL_THEN `&0 < inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau /\ (tau * q = d / &2) /\
                ((t:num->real) m - (Tr + d / &2) * inv q = tt - tau) /\
                (tt + tau = t m + a1 / q) /\ tt + tau <= t m /\ tt < t m /\
                (t:num->real) m - (Tr + dl2) / q < tt /\
                (&2 * (K2 * q) * (t m - tt) = &2 * K2 * Tr)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tau"; "tt"; "a1"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `t m - Tr / q + d / &2 / q = (t:num->real) m + (--Tr + d / &2) / q`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `t + b <= t <=> b <= &0`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - b < t <=> &0 < b`] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t - a < t - b <=> b < a`] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the balls at t m inside the balls at -Tr *)
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m`;
                 `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m) (x m) ((A + &1) * inv(sqrt q))`;
                 `(t:num->real) m - (Tr + dl2) / q`; `(t:num->real) m`; `K2 * q`; `tt:real`;
                 `(x:num->A) m`; `A * inv(sqrt q)`] P2BU_VIEW_BALL_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
      USE_THEN "bc" (MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[P2CO_VBALL] THEN
      USE_THEN "slices" (MP_TAC o SPECL [`m:num`; `(t:num->real) m`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) m` THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bo") THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) m - (Tr + d / &2) * inv q`; `(t:num->real) m`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `t - x <= t + y <=> --y <= x`; real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`sg:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tt - tau < (t:num->real) m + sg / q /\ t m + sg / q <= t m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(t:num->real) m - (Tr + d / &2) * inv q = tt - tau` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `t - x < t + y <=> --x < y`; real_div; GSYM REAL_MUL_LNEG] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `t + b <= t <=> b <= &0`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m + sg / q))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (rfs_vball (V m) (t m) (x m) (A * inv(sqrt q)))
                   (t m - (Tr + d / &2) * inv q) (t m)` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `(t:num->real) m + sg / q`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a1 <= sg` THENL
   [USE_THEN "r1" (MP_TAC o SPECL [`sg:real`; `y:A`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `kk <= mm ==> pp <= kk ==> pp <= mm`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Lemma 11.2 around -Tr *)
  SUBGOAL_THEN `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) tt (x m) ((exp(&2 * K2 * Tr) * A) * inv(sqrt q))`
  ASSUME_TAC THENL
   [USE_THEN "bo" (MP_TAC o REWRITE_RULE[SUBSET] ) THEN
    DISCH_THEN(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  USE_THEN "dn" (MP_TAC o SPEC `y:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m`; `C1:real`; `q:real`; `tt:real`; `y:A`;
                 `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m) (x m) ((A + &1) * inv(sqrt q))`;
                 `tau:real`; `D:real`] P2BU_DB_AROUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THEN
    FIRST
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `s':real`] THEN STRIP_TAC THEN
      USE_THEN "cdb" (MP_TAC o SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m`; `C:real`; `eps:real`; `z:A`; `s':real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]] THEN NO_TAC;
      UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m) (x m) (A * inv(sqrt q))` THEN
      REWRITE_TAC[P2CO_VBALL] THEN
      MATCH_MP_TAC(SET_RULE `!s t (w:A). s SUBSET t ==> w IN s ==> w IN t`) THEN
      MATCH_MP_TAC P2CU_BALL_MONO THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (rfs_vball (V m) (t m) (x m) ((A + &1) * inv(sqrt q)))
                     (t m - (Tr + d / &2) * inv q) (t m)` THEN
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `tt:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN NO_TAC;
      MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`(t:num->real) m - (Tr + d / &2) * inv q`; `(t:num->real) m`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(t:num->real) m + sg / q`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `tt + tau = (t:num->real) m + a1 / q` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_LT_LADD; real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4)) * q` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BU_VIEW_PINCH_RM_Q THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (t m + sg / q))` THEN
      FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(t:num->real) m + sg / q < &0`) o
                    SPEC `(t:num->real) m + sg / q` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "discrete_topology" with _ -> false))
            (concl th))) THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* The flow limit on (-T,0] from RBU(T) and a time-0 slice limit, with MT    *)
(* Cor 11.16 on it (P2BU_FLOW_CTX), the context of the extension step        *)
(* (P2BU_CTX_FROM_RBU), RBU from region bounds, and the start RBU(T1) for    *)
(* some T1 > 0 (P2BU_STAGE3_RBU, from Claims 11.6, 11.7 and Cor 11.3 at time *)
(* 0).                                                                       *)
(* ========================================================================= *)

(* The backward hypothesis passes to subsequences.                         *)

let P2BU_BACK_SUBSEQ = prove
 (`!kappa r0 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Tb sub.
     p2c_vblowup_back (kappa,r0) V x t Tb /\ p3_subseq sub
     ==> p2c_vblowup_back (kappa,r0) (\n. V (sub n)) (x o sub) (t o sub) Tb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vblowup_back; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. n <= sub n` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[]);;

(* The scalar curvature of a flow limit at its base point at time 0 is 1   *)

(* The scalar curvature of a flow limit at its base point at time 0 is 1   *)
(* when the scales are R(x n, t n) (P2BU_POINT_CURV).                        *)

let P2BU_BASE_SCALAR_ONE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t J (top:B topology) atlas g xl W (phi:num->B->A).
     (!n. p2c_regular_view (V n)) /\
     p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s))
     ==> mfd_scalar atlas (g (&0)) xl = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `!e. &0 < e ==> abs(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) xl - &1) < e`
  MP_TAC THENL [ALL_TAC; MESON_TAC[REAL_LT_REFL; REAL_ABS_NZ; REAL_SUB_0]] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `e:real`] P2BU_POINT_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o CONJUNCT1 o CONJUNCT2 o
                                     REWRITE_RULE[LE_REFL] o SPEC `N:num`)) THEN
  ASM_REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ]);;

(* Neck spheres separate in a flow limit when they do in the approximants   *)
(* (P2BU_SEP_SLICE on the slice limit at time 0).                            *)

let P2BU_FLOW_SEP = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A).
     (!n. p2c_regular_view (V n)) /\
     (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     riemannian_metric atlas (g (&0))
     ==> apx_sphere_sep top atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`] P2BU_FLOW_TO_SLICE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_flow_limit_with] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_flow_limit_with" with _ -> false))
          (concl th))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  MATCH_MP_TAC P2BU_SEP_SLICE THEN
  MAP_EVERY EXISTS_TAC [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)`; `\n. (x:num->A) (n + N)`;
    `\n. (t:num->real) (n + N) + &0 / Q (n + N)`; `\n. (Q:num->real) (n + N)`;
    `(g:real->B->real^3^3) (&0)`; `xl:B`; `\n. (W:num->B->bool) (n + N)`;
    `\n. (phi:num->B->A) (n + N)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (n + N)`; `\n. (x:num->A) (n + N)`;
    `\n. (t:num->real) (n + N) + &0 / Q (n + N)`; `\n. (Q:num->real) (n + N)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `(g:real->B->real^3^3) (&0)`; `xl:B`; `\n. (W:num->B->bool) (n + N)`;
    `\n. (phi:num->B->A) (n + N)`; `k:num`] P2BU_SLICE_BASE_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (k + N)`; `(t:num->real) (k + N) + &0 / Q (k + N)`;
                 `(x:num->A) (k + N)`] P2C_REGULAR_SLICE) THEN
  ASM_SIMP_TAC[]);;

(* The flow limit on (-Tr,0] from RBU(Tr) and a time-0 slice limit, with   *)
(* MT Cor 11.16 on it: p2bu_flowctx is p2bu_extctx without the backward      *)
(* hypothesis and without Tr < T0 (so that it also serves at Tr = T0).       *)

let p2bu_flowctx = new_definition
 `p2bu_flowctx (C:real,eps:real,kappa:real,r0:real,mu:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) (t:num->real) (Tr:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) <=>
    p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\
    (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
    (!A. ?N. !n. N <= n
                 ==> compact_in (rfs_vtop (V n) (t n))
                       (rfs_vtop (V n) (t n) closure_of
                        rfs_vball (V n) (t n) (x n)
                          (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
    &0 < Tr /\
    p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr /\
    p2c_flow_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
      {s | --Tr < s /\ s <= &0} (top,atlas) g xl W phi /\
    connected_space top /\
    (!s. --Tr < s /\ s <= &0
         ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s) /\
             (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                      ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
    (!a b. --Tr < a /\ a < b /\ b <= &0 ==> ricci_flow_on (top,atlas) a b g) /\
    (!a. --Tr < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!a. --Tr < a /\ a <= &0
         ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                       ==> mfd_rm_norm atlas (g s) y <= K) /\
    (!A. ?K. !s y. --Tr < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                   ==> mfd_scalar atlas (g s) y <= K)`;;

let P2BU_EXTCTX_FLOWCTX = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 Tr (top:B topology) atlas g xl W (phi:num->B->A).
     p2bu_extctx (C,eps,kappa,r0,mu) V x t T0 Tr (top,atlas) g xl W phi <=>
     p2bu_flowctx (C,eps,kappa,r0,mu) V x t Tr (top,atlas) g xl W phi /\
     (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\ Tr < T0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_extctx; p2bu_flowctx] THEN CONV_TAC TAUT);;

(* The flow limit on (-Tr,0] along a subsequence (P2BU_FLOW_FROM_RBU), and *)
(* MT Cor 11.16 on it (P2C_COR_11_16_FLOW_STATEMENT with canonical           *)
(* neighbourhoods at every time, P2BU_CANON_AT_S, and bounded curvature at   *)
(* bounded distance, P2BU_BCBD_AT_S).                                         *)

let P2BU_FLOW_CTX = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t Tr (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              &0 < Tr /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top0,atlas0) g0 xl0 W0 phi0 /\
              mfd_complete (top0,atlas0) g0 /\
              p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr
              ==> ?sub (top:B topology) atlas g xl W (phi:num->B->A).
                     p3_subseq sub /\
                     p2bu_flowctx (C,eps,kappa,r0,mu) (\n. V (sub n)) (x o sub) (t o sub) Tr
                       (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CANON_AT_S) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cas"))))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_BCBD_AT_S) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bcbd"))) THEN
  UNDISCH_TAC `P2C_COR_11_16_FLOW_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2C_COR_11_16_FLOW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1116"))) THEN
  EXISTS_TAC `min e1 (min e2 (e3 / K1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tr:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rbu")))))))))) THEN
  SUBGOAL_THEN `K1 * eps <= e3 /\ &1 < &2 * C /\ &0 < K1 * eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `eps <= e3 / K1` THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= k ==> &0 < k`] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "bseq" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (K ALL_TAC)))))) THEN
  (* the flow limit on (-Tr,0] *)
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_FLOW_FROM_RBU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`; `Tr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Jp")
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmb") (LABEL_TAC "join")))))))))))) THEN
  SUBGOAL_THEN `(\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)) o (sub:num->num) =
                (\n. rfs_vscalar (V (sub n)) ((t o sub) n) ((x o sub) n))`
  (LABEL_TAC "Qeq") THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  USE_THEN "fl" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH; ASSUME
    `(\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)) o (sub:num->num) =
     (\n. rfs_vscalar (V (sub n)) ((t o sub) n) ((x o sub) n))`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A` (LABEL_TAC "flw"))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl0:B`;
    `W:num->B->bool`; `phi:num->B->A`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the facts along the subsequence *)
  SUBGOAL_THEN `p2c_vblowup_seq (C,eps,kappa,r0,mu) (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n))
                  ((x:num->A) o sub) ((t:num->real) o sub)` (LABEL_TAC "bs2") THENL
   [MATCH_MP_TAC P2BU_VBLOWUP_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bu_rbu (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) ((x:num->A) o sub) ((t:num->real) o sub)
                  (\n. rfs_vscalar (V (sub n)) ((t o sub) n) ((x o sub) n)) Tr`
  (LABEL_TAC "rbu2") THENL
   [USE_THEN "Qeq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC P2BU_RBU_SUBSEQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                xl0 IN topspace top` STRIP_ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. --Tr < s /\ s <= &0
                    ==> !y v. y IN topspace top
                              ==> v dot ((g:real->B->real^3^3) (&0) y ** v) <= v dot (g s y ** v)`
  (LABEL_TAC "mback") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LIM_METRIC_BACK THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `(s - Tr) / &2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s':real`; `z:B`; `u':real^3`; `w':real^3`] THEN STRIP_TAC THEN
      USE_THEN "Jp" (MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0)) /\
                mfd_complete (top,atlas) (g (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "Jp" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* Cor 11.16 *)
  USE_THEN "c1116" (MP_TAC o SPECL [`&2 * C`; `K1 * eps`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `Tr:real`; `xl0:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* separation *)
      MATCH_MP_TAC P2BU_FLOW_SEP THEN
      MAP_EVERY EXISTS_TAC [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`; `(x:num->A) o (sub:num->num)`;
        `(t:num->real) o (sub:num->num)`;
        `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)) (((t:num->real) o sub) n)
                         (((x:num->A) o sub) n)`;
        `{s:real | --Tr < s /\ s <= &0}`; `g:real->B->real^3^3`; `xl0:B`;
        `W:num->B->bool`; `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
      (* the slices *)
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--Tr < s`) (ASSUME `s <= &0`)) o
                     SPEC `s:real`) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "cas" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`; `(x:num->A) o (sub:num->num)`;
        `(t:num->real) o (sub:num->num)`; `{s:real | --Tr < s /\ s <= &0}`;
        `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
        `xl0:B`; `W:num->B->bool`; `phi:num->B->A`; `Tr:real`; `s:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
        FIRST [USE_THEN "mback" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
               REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
        SIMP_TAC[]];
      (* the curvature bounds on [a,0] *)
      X_GEN_TAC `a:real` THEN DISCH_TAC THEN ASM_CASES_TAC `a <= &0` THENL
       [USE_THEN "rmb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `&0` THEN ASM_REAL_ARITH_TAC];
      (* bounded curvature at bounded distance *)
      USE_THEN "bcbd" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`; `(x:num->A) o (sub:num->num)`;
        `(t:num->real) o (sub:num->num)`; `{s:real | --Tr < s /\ s <= &0}`;
        `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
        `xl0:B`; `W:num->B->bool`; `phi:num->B->A`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
        FIRST [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
               USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--Tr < s`) (ASSUME `s <= &0`)) o
                              SPEC `s:real`) THEN SIMP_TAC[] THEN NO_TAC;
               REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      (* R(xl,0) = 1 *)
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2BU_BASE_SCALAR_ONE THEN
      MAP_EVERY EXISTS_TAC [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) n)`; `(x:num->A) o (sub:num->num)`;
        `(t:num->real) o (sub:num->num)`; `{s:real | --Tr < s /\ s <= &0}`;
        `top:B topology`; `W:num->B->bool`; `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
      FIRST [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
             USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--Tr < s`) (ASSUME `s <= &0`)) o
                            SPEC `s:real`) THEN SIMP_TAC[] THEN NO_TAC;
             USE_THEN "views" (fun th -> MESON_TAC[th])]];
    DISCH_THEN(LABEL_TAC "K1116")] THEN
  REWRITE_TAC[p2bu_flowctx] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "cc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[] THEN NO_TAC;
    ALL_TAC]);;

(* The context of the extension step (P2BU_FLOW_CTX with the backward       *)
(* hypothesis below T0 and Tr < T0).                                         *)

let P2BU_CTX_FROM_RBU = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 Tr (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\
              &0 < Tr /\ Tr < T0 /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top0,atlas0) g0 xl0 W0 phi0 /\
              mfd_complete (top0,atlas0) g0 /\
              p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) Tr
              ==> ?sub (top:B topology) atlas g xl W (phi:num->B->A).
                     p3_subseq sub /\
                     p2bu_extctx (C,eps,kappa,r0,mu) (\n. V (sub n)) (x o sub) (t o sub) T0 Tr
                       (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BU_FLOW_CTX) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fc")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `Tr:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`] THEN
  STRIP_TAC THEN
  USE_THEN "fc" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tr:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun v -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC v)
   [`sub:num->num`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[P2BU_EXTCTX_FLOWCTX] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BU_BACK_SUBSEQ THEN ASM_SIMP_TAC[]);;

(* RBU(dl) from region bounds on (t n - dl / Q n, t n] uniform in A.        *)

let P2BU_RBU_OF_REGION = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q dl K.
     &0 < dl /\ (!n. &0 < Q n) /\
     (!A. &0 < A
          ==> ?N. !n. N <= n
                 ==> rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                       (t n - dl / Q n) (t n) /\
                     !s y. t n - dl / Q n < s /\ s <= t n /\
                           y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                           ==> y IN topspace(rfs_vtop (V n) s) /\ p3_vrm (V n) s y <= K * Q n)
     ==> p2bu_rbu V x t Q dl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (LABEL_TAC "reg"))) THEN
  REWRITE_TAC[p2bu_rbu] THEN X_GEN_TAC `a:real` THEN STRIP_TAC THEN EXISTS_TAC `K:real` THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "reg" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(C MP (ASSUME `N <= n:num`) (SPEC `n:num` th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "in")) THEN
  USE_THEN "Qpos" (ASSUME_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `!s. --dl < s ==> (t:num->real) n - dl / Q n < t n + s / Q n`
  (LABEL_TAC "lt") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `t - a < t + b <=> --a < b`; real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= &0 ==> (t:num->real) n + s / Q n <= t n` (LABEL_TAC "le") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `t + b <= t <=> b <= &0`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n - dl / Q n`; `(t:num->real) n`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "lt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "le" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The start of the extension (MT Thm 11.1 inside the proof of Thm 11.8):   *)
(* on a connected complete time-0 slice limit, Claims 11.6 and 11.7 give    *)
(* R <= D Q n on all rescaled balls, and Cor 11.3 (P2BU_SEQ_REGION) gives   *)
(* RBU(dl) with dl = min(mu / max 1 D, 1/(16 C (D + 4))).                    *)

let P2BU_STAGE3_RBU = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g0 xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top,atlas) g0 xl W phi /\
              mfd_complete (top,atlas) g0 /\ connected_space top
              ==> ?T1. &0 < T1 /\ p2bu_rbu V x t (\n. rfs_vscalar (V n) (t n) (x n)) T1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sreg"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CLAIM_11_6) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c116"))))) THEN
  UNDISCH_TAC `P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a4"))) THEN
  EXISTS_TAC `min e2 (min e3 (e4 / K1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `K1 * eps <= e4 /\ &1 < &2 * C /\ &0 < K1 * eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `eps <= e4 / K1` THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= k ==> &0 < k`] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  USE_THEN "c116" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`; `&2 * C`; `K1 * eps`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_CLAIM_11_7) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`;
                         `g1:B->real^3^3`] THEN STRIP_TAC THEN
    USE_THEN "a4" (MP_TAC o SPECL [`&2 * C`; `K1 * eps`; `top1:B topology`;
      `atlas1:((B->bool)#(B->real^3))->bool`; `g1:B->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dbd")))] THEN
  EXISTS_TAC `min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BU_RBU_OF_REGION THEN
  EXISTS_TAC `&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_slice_limit_with] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
          (concl th))) THEN SIMP_TAC[];
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "sreg" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `A:real`; `D:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        USE_THEN "Dbd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* The recursion of MT Prop 11.10 and MT Thm 11.8 part 1.  Eventual          *)
(* subsequences (p2bu_evsub), the diagonal of nested subsequences, the       *)
(* greedy form of MT's supremum argument (P2BU_GREEDY), the extension step   *)
(* along subsequences (P2BU_EXT_RBU), RBU(T0) (P2BU_RBU_FULL), the connected *)
(* time-0 data (P2BU_GOOD_START) and the assembly (P2BU_THM_11_8_PART1, with *)
(* the Cor 11.16 bound on balls).                                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The recursion of MT Prop 11.10 (the greedy form of MT's supremum         *)
(* argument).  p2bu_rbus V x t d T: RBU(T) along the subsequence d of the   *)
(* base sequence, with the scales R(x (d n), t (d n)).  p2bu_evsub d r: d   *)
(* is strictly increasing and eventually takes values in every tail of r.   *)
(* p2bu_good: the data of the base sequence (blow-up sequence, separation,  *)
(* compact closures, the backward hypothesis below T0, a connected complete *)
(* time-0 slice limit).                                                      *)
(* ------------------------------------------------------------------------- *)

let p2bu_rbus = new_definition
 `p2bu_rbus (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (x:num->A) (t:num->real) (d:num->num) (Tr:real) <=>
    p2bu_rbu (\n. V (d n)) (\n. x (d n)) (\n. t (d n))
             (\n. rfs_vscalar (V (d n)) (t (d n)) (x (d n))) Tr`;;

let p2bu_evsub = new_definition
 `p2bu_evsub (d:num->num) (r:num->num) <=>
    p3_subseq d /\ !N. ?M. !n. M <= n ==> ?m. N <= m /\ d n = r m`;;

let p2bu_good = new_definition
 `p2bu_good (C,eps,kappa,r0,mu)
     (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     (x:num->A) (t:num->real) (T0:real)
     (top0:B topology,atlas0:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3) (xl0:B)
     (W0:num->B->bool) (phi0:num->B->A) <=>
    p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\
    (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
    (!A. ?N. !n. N <= n
                 ==> compact_in (rfs_vtop (V n) (t n))
                       (rfs_vtop (V n) (t n) closure_of
                        rfs_vball (V n) (t n) (x n)
                          (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
    (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb) /\
    p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
      (top0,atlas0) g0 xl0 W0 phi0 /\
    mfd_complete (top0,atlas0) g0 /\ connected_space top0`;;

let P2BU_EVSUB_TRANS = prove
 (`!d r q. p2bu_evsub d r /\ p2bu_evsub r q ==> p2bu_evsub d q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_evsub] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r"))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `N:num` THEN
  USE_THEN "r" (X_CHOOSE_TAC `M1:num` o SPEC `N:num`) THEN
  USE_THEN "d" (X_CHOOSE_TAC `M:num` o SPEC `M1:num`) THEN
  EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC o C MP (ASSUME `M <= n:num`) o
    SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:num`)) (concl th))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o C MP (ASSUME `M1 <= k:num`) o
    SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N:num`)) (concl th))) THEN
  EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]);;

let P2BU_SUBSEQ_GE = prove
 (`!r n. p3_subseq r ==> n <= r n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_subseq] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONOTONE_BIGGER) THEN SIMP_TAC[]);;

let P2BU_SUBSEQ_O = prove
 (`!r e. p3_subseq r /\ p3_subseq e ==> p3_subseq (r o e)`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P2BU_EVSUB_REFL = prove
 (`!r. p3_subseq r ==> p2bu_evsub r r`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[p2bu_evsub] THEN X_GEN_TAC `N:num` THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

let P2BU_EVSUB_COMPOSE = prove
 (`!r e. p3_subseq r /\ p3_subseq e ==> p2bu_evsub (r o e) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bu_evsub] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `(e:num->num) n` THEN REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[]);;

let P2BU_SUBSEQ_LE = prove
 (`!r a b. p3_subseq r /\ a <= b ==> r a <= r b`,
  REWRITE_TAC[p3_subseq] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a:num = b` THENL
   [ASM_REWRITE_TAC[LE_REFL];
    MATCH_MP_TAC LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LT_LE]]);;

let P2BU_EVSUB_FACTOR = prove
 (`!d r. p3_subseq r /\ p2bu_evsub d r ==> ?e. p3_subseq e /\ p2bu_evsub (r o e) d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_evsub] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `M:num` o SPEC `0`))) THEN
  SUBGOAL_THEN `?e:num->num. !n. (d:num->num) (n + M) = (r:num->num) (e n)` (X_CHOOSE_TAC `e:num->num`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + M:num`) THEN REWRITE_TAC[LE_ADDR] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_subseq e` ASSUME_TAC THENL
   [REWRITE_TAC[p3_subseq] THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:num->num) ((e:num->num) n) <= r (e m)` MP_TAC THENL
     [MATCH_MP_TAC P2BU_SUBSEQ_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `!n. (d:num->num) (n + M) = (r:num->num) ((e:num->num) n)`);
                NOT_LE] THEN
    UNDISCH_TAC `p3_subseq d` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT_ADD_RCANCEL];
    ALL_TAC] THEN
  EXISTS_TAC `e:num->num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `n + M:num` THEN ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LE_ADD]);;

let P2BU_RBUS_EVSUB = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t r d Tr.
     p2bu_rbus V x t r Tr /\ p2bu_evsub d r ==> p2bu_rbus V x t d Tr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbus; p2bu_rbu; p2bu_evsub] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rb") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ev"))) THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  USE_THEN "rb" (MP_TAC o C MP (ASSUME `--Tr < a /\ a <= &0`) o SPEC `a:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(C MP (ASSUME `&0 < A`) (SPEC `A:real` th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  USE_THEN "ev" (X_CHOOSE_THEN `M:num` (LABEL_TAC "M") o SPEC `N:num`) THEN
  EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "M" (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o C MP (ASSUME `M <= n:num`) o
    SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BU_RBU_UNION = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q Tj L.
     (!j:num. p2bu_rbu V x t Q (Tj j)) /\ (!a. --L < a ==> ?j. --Tj j < a)
     ==> p2bu_rbu V x t Q L`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rb") (LABEL_TAC "ap")) THEN
  REWRITE_TAC[p2bu_rbu] THEN X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  USE_THEN "ap" (X_CHOOSE_TAC `j:num` o C MP (ASSUME `--L < a`) o SPEC `a:real`) THEN
  USE_THEN "rb" (MP_TAC o REWRITE_RULE[p2bu_rbu] o SPEC `j:num`) THEN
  DISCH_THEN(MP_TAC o C MP (CONJ (ASSUME `--Tj (j:num) < a`) (ASSUME `a <= &0`)) o
    SPEC `a:real`) THEN
  SIMP_TAC[]);;

let P2BU_DIAG_NESTED = prove
 (`!r:num->num->num.
     (!j. p3_subseq (r j)) /\ (!j. ?e. p3_subseq e /\ r (SUC j) = r j o e)
     ==> p3_subseq (\n. r n n) /\ !j. p2bu_evsub (\n. r n n) (r j)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sq") (LABEL_TAC "nest")) THEN
  SUBGOAL_THEN `!j k n. ?m. n <= m /\ (r:num->num->num) (j + k) n = r j m` (LABEL_TAC "ind")
  THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [GEN_TAC THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL];
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    USE_THEN "nest" (X_CHOOSE_THEN `e:num->num` STRIP_ASSUME_TAC o SPEC `j + k:num`) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o SPEC `(e:num->num) n`) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES; o_THM] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(e:num->num) n` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_subseq (\n. (r:num->num->num) n n)` ASSUME_TAC THENL
   [REWRITE_TAC[p3_subseq] THEN
    MP_TAC(ISPEC `\m n:num. (r:num->num->num) m m < r n n` TRANSITIVE_STEPWISE_LT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MESON_TAC[LT_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    USE_THEN "nest" (X_CHOOSE_THEN `e:num->num` STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    USE_THEN "sq" (MP_TAC o REWRITE_RULE[p3_subseq] o SPEC `n:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC n` THEN REWRITE_TAC[LT] THEN
    MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2bu_evsub] THEN MAP_EVERY X_GEN_TAC [`j:num`; `N:num`] THEN
  EXISTS_TAC `j + N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "ind" (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o
    SPECL [`j:num`; `n - j:num`; `n:num`]) THEN
  EXISTS_TAC `m:num` THEN
  SUBGOAL_THEN `j + n - j = n:num` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `j + N <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j + N <= n:num` THEN UNDISCH_TAC `n <= m:num` THEN
  ARITH_TAC);;

let p2bu_reach = new_definition
 `p2bu_reach (G:(num->num)->real->bool) (T0:real) (r:num->num) =
    sup {Tb | &0 < Tb /\ Tb <= T0 /\ ?d. p2bu_evsub d r /\ G d Tb}`;;

let P2BU_SUP_SET = prove
 (`!(s:real->bool) b.
     ~(s = {}) /\ (!x. x IN s ==> x <= b)
     ==> (!x. x IN s ==> x <= sup s) /\ sup s <= b /\
         (!eps. &0 < eps ==> ?x. x IN s /\ sup s - eps < x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_APPROACH THEN
  REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]);;

let P2BU_SUP_SEQ = prove
 (`!(a:num->real) b.
     (!j. a j <= b)
     ==> ?L. (!j. a j <= L) /\ L <= b /\ (!c. c < L ==> ?j. c < a j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (a:num->real) (:num)`; `b:real`] P2BU_SUP_SET) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; UNIV_NOT_EMPTY; FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `sup (IMAGE (a:num->real) (:num))` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sup (IMAGE (a:num->real) (:num)) - c`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REAL_ARITH_TAC);;

let P2BU_REACH = prove
 (`!(G:(num->num)->real->bool) T0 r.
     (?Ta d. &0 < Ta /\ Ta <= T0 /\ p2bu_evsub d r /\ G d Ta)
     ==> (!Ta d. &0 < Ta /\ Ta <= T0 /\ p2bu_evsub d r /\ G d Ta
                 ==> Ta <= p2bu_reach G T0 r) /\
         (!eps. &0 < eps
                ==> ?Tb d. &0 < Tb /\ Tb <= T0 /\ p2bu_evsub d r /\ G d Tb /\
                           p2bu_reach G T0 r - eps < Tb)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2bu_reach] THEN
  W(fun (asl,w) ->
     let s = find_term (fun t -> try fst(dest_const(rator t)) = "sup" with _ -> false) w in
     MP_TAC(ISPECL [rand s; `T0:real`] P2BU_SUP_SET)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < eps`) o SPEC `eps:real`) THEN
  MESON_TAC[]);;

(* The greedy form of MT's supremum argument (p. 278): a property G d T of  *)
(* subsequences d and times T, monotone in T, inherited by eventual          *)
(* subsequences, closed under increasing unions in T, holding at some T1 > 0 *)
(* for the whole sequence, and extendable past every T < T0 along a further  *)
(* subsequence, holds at T0 along some subsequence.                          *)

let P2BU_GREEDY = prove
 (`!(G:(num->num)->real->bool) T0 T1.
     &0 < T1 /\ &0 < T0 /\ G (\n. n) T1 /\
     (!d Ta Tb. G d Ta /\ Tb <= Ta ==> G d Tb) /\
     (!r d Ta. G r Ta /\ p2bu_evsub d r ==> G d Ta) /\
     (!d Tj L. (!j:num. G d (Tj j)) /\ (!a. --L < a ==> ?j. --Tj j < a) ==> G d L) /\
     (!Tr d. &0 < Tr /\ Tr < T0 /\ p3_subseq d /\ G d Tr
             ==> ?e dl. p3_subseq e /\ &0 < dl /\ G (d o e) (Tr + dl))
     ==> ?d. p3_subseq d /\ G d T0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (LABEL_TAC "ext"))))))) THEN
  (* one greedy step below a subsequence r *)
  SUBGOAL_THEN
   `!r Ta eps. p3_subseq r /\ &0 < Ta /\ Ta <= T0 /\ (G:(num->num)->real->bool) r Ta /\
               &0 < eps
               ==> ?e Tb. p3_subseq e /\ &0 < Tb /\ Tb <= T0 /\ G (r o e) Tb /\
                          p2bu_reach G T0 r - eps < Tb`
  (LABEL_TAC "app") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:(num->num)->real->bool`; `T0:real`; `r:num->num`] P2BU_REACH) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`Ta:real`; `r:num->num`] THEN ASM_SIMP_TAC[P2BU_EVSUB_REFL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < eps`) o SPEC `eps:real` o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `Tb:real` (X_CHOOSE_THEN `d:num->num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`d:num->num`; `r:num->num`] P2BU_EVSUB_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:num->num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`e:num->num`; `Tb:real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ev" MATCH_MP_TAC THEN EXISTS_TAC `d:num->num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the greedy sequence *)
  MP_TAC(ISPECL
   [`\n:num z:(num->num)#real. p3_subseq (FST z) /\ &0 < SND z /\ SND z <= T0 /\
                               (G:(num->num)->real->bool) (FST z) (SND z)`;
    `\n:num z:(num->num)#real z':(num->num)#real.
        (?e. p3_subseq e /\ FST z' = FST z o e) /\
        p2bu_reach (G:(num->num)->real->bool) T0 (FST z) - inv(&n + &1) < SND z'`]
   DEPENDENT_CHOICE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `(\n:num. n), min T1 T0` THEN REWRITE_TAC[FST; SND; p3_subseq] THEN
      REPEAT CONJ_TAC THEN
      FIRST [SIMP_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC;
             USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `T1:real` THEN
             ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`n:num`; `z:(num->num)#real`] THEN STRIP_TAC THEN
      USE_THEN "app" (MP_TAC o SPECL [`FST(z:(num->num)#real)`; `SND(z:(num->num)#real)`;
                                      `inv(&n + &1)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:num->num` (X_CHOOSE_THEN `Tb:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `FST(z:(num->num)#real) o (e:num->num), Tb:real` THEN
      ASM_REWRITE_TAC[FST; SND] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `e:num->num` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(num->num)#real`
    (CONJUNCTS_THEN2 (LABEL_TAC "Pf") (LABEL_TAC "Rf"))) THEN
  (* the diagonal *)
  SUBGOAL_THEN `(!j. p3_subseq (FST((f:num->(num->num)#real) j))) /\
                (!j. ?e. p3_subseq e /\ FST(f (SUC j)) = FST(f j) o e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `j:num` THENL
     [USE_THEN "Pf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
      USE_THEN "Rf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\j:num. FST((f:num->(num->num)#real) j)` P2BU_DIAG_NESTED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dev")) THEN
  SUBGOAL_THEN `!j. (G:(num->num)->real->bool) (\n. FST((f:num->(num->num)#real) n) n)
                                                (SND(f j))`
  (LABEL_TAC "Gd") THENL
   [X_GEN_TAC `j:num` THEN USE_THEN "ev" MATCH_MP_TAC THEN
    EXISTS_TAC `FST((f:num->(num->num)#real) j)` THEN
    USE_THEN "dev" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Pf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the limit time L *)
  MP_TAC(ISPECL [`\j. SND((f:num->(num->num)#real) j)`; `T0:real`] P2BU_SUP_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN USE_THEN "Pf" (MP_TAC o SPEC `j:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 (LABEL_TAC "Lub")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Lap")))) THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `SND((f:num->(num->num)#real) 0)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "Pf" (MP_TAC o SPEC `0`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:(num->num)->real->bool) (\n. FST((f:num->(num->num)#real) n) n) L`
  (LABEL_TAC "GL") THENL
   [USE_THEN "un" MATCH_MP_TAC THEN EXISTS_TAC `\j. SND((f:num->(num->num)#real) j)` THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "Lap" (MP_TAC o SPEC `--a`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `L < T0` THENL
   [ALL_TAC;
    SUBGOAL_THEN `L:real = T0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `\n. FST((f:num->(num->num)#real) n) n` THEN ASM_REWRITE_TAC[]] THEN
  (* L < T0 is impossible: one more extension step *)
  USE_THEN "ext" (MP_TAC o SPECL [`L:real`; `\n. FST((f:num->(num->num)#real) n) n`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->num` (X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!j. min (L + dl) T0 <=
        p2bu_reach (G:(num->num)->real->bool) T0 (FST((f:num->(num->num)#real) j))`
  (LABEL_TAC "L2") THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `&0 < min (L + dl) T0 /\ min (L + dl) T0 <= T0 /\
                  p2bu_evsub ((\n. FST((f:num->(num->num)#real) n) n) o (e:num->num))
                             (FST(f j)) /\
                  (G:(num->num)->real->bool) ((\n. FST(f n) n) o e) (min (L + dl) T0)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
        MATCH_MP_TAC P2BU_EVSUB_TRANS THEN
        EXISTS_TAC `\n. FST((f:num->(num->num)#real) n) n` THEN
        USE_THEN "dev" (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC P2BU_EVSUB_COMPOSE THEN ASM_REWRITE_TAC[];
        USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `L + dl` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:(num->num)->real->bool`; `T0:real`;
                   `FST((f:num->(num->num)#real) j)`] P2BU_REACH) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`min (L + dl) T0`;
                            `(\n. FST((f:num->(num->num)#real) n) n) o (e:num->num)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    EXISTS_TAC `(\n. FST((f:num->(num->num)#real) n) n) o (e:num->num)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `min (L + dl) T0 - L` REAL_ARCH_INV) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "Rf" (MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
  USE_THEN "L2" (MP_TAC o SPEC `n:num`) THEN
  USE_THEN "Lub" (MP_TAC o SPEC `SUC n`) THEN
  UNDISCH_TAC `inv(&n) < min (L + dl) T0 - L` THEN
  REAL_ARITH_TAC);;

(* The extension step along subsequences (MT Prop 11.10): the context of     *)
(* the step (P2BU_CTX_FROM_RBU) and the step itself (P2BU_EXT_STEP).         *)

let P2BU_EXT_RBU = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A)
            Tr d.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_good (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 (top0,atlas0) g0 xl0 W0 phi0 /\
              &0 < Tr /\ Tr < T0 /\ p3_subseq d /\ p2bu_rbus V x t d Tr
              ==> ?e dl. p3_subseq e /\ &0 < dl /\ p2bu_rbus V x t (d o e) (Tr + dl)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CTX_FROM_RBU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_EXT_STEP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`; `Tr:real`; `d:num->num`] THEN
  REWRITE_TAC[REAL_LE_MIN; p2bu_good] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (CONJUNCTS_THEN2 (LABEL_TAC "back") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rbs")))))))) THEN
  SUBGOAL_THEN `!n:num. n <= d n` (LABEL_TAC "ge") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((d:num->num) n)`; `\n. (x:num->A) ((d:num->num) n)`;
    `\n. (t:num->real) ((d:num->num) n)`; `T0:real`; `Tr:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `\n. (W0:num->B->bool) ((d:num->num) n)`; `\n. (phi0:num->B->A) ((d:num->num) n)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MP_TAC(ISPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
        `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `d:num->num`] P2BU_VBLOWUP_SUBSEQ) THEN
      ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
      X_GEN_TAC `A:real` THEN USE_THEN "cc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      X_GEN_TAC `Tb:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`kappa:real`; `r0:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tb:real`;
                     `d:num->num`] P2BU_BACK_SUBSEQ) THEN
      ASM_SIMP_TAC[o_DEF] THEN NO_TAC;
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
        `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n) ((x:num->A) n)`; `top0:B topology`;
        `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
        `W0:num->B->bool`; `phi0:num->B->A`; `d:num->num`] P2BU_SLICE_LIMIT_SUBSEQ) THEN
      ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
      USE_THEN "rbs" (MP_TAC o REWRITE_RULE[p2bu_rbus]) THEN SIMP_TAC[] THEN NO_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ec"))))))))) THEN
  USE_THEN "ec" (fun ec -> USE_THEN "ext" (fun ext ->
    MP_TAC(MATCH_MP ext (CONJ (ASSUME `&1 < C`) (CONJ (ASSUME `&0 < eps`)
      (CONJ (ASSUME `eps <= e2`) ec)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(sub:num->num) o (sub2:num->num)`; `dl:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BU_SUBSEQ_O THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2bu_rbus; o_DEF] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[o_DEF] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2bu_rbu" with _ -> false))
          (concl th) &&
      can (find_term ((=) `dl:real`)) (concl th)))]);;

(* The start of the recursion in p2bu_good form (P2BU_STAGE3_RBU).          *)

let P2BU_RBU_START = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2bu_good (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 (top0,atlas0) g0 xl0 W0 phi0
              ==> ?T1. &0 < T1 /\ p2bu_rbus V x t (\n. n) T1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BU_STAGE3_RBU) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`] THEN
  REWRITE_TAC[p2bu_good] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bu_rbus; ETA_AX] THEN
  USE_THEN "st" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* MT Prop 11.10 iterated (the supremum argument of MT p. 278): RBU(T0)      *)
(* along a subsequence.                                                       *)

let P2BU_RBU_FULL = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0 (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < T0 /\
              p2bu_good (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t T0 (top0,atlas0) g0 xl0 W0 phi0
              ==> ?d. p3_subseq d /\ p2bu_rbus V x t d T0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_RBU_START) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_EXT_RBU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ex"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "st" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\d Ta. p2bu_rbus (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (x:num->A) (t:num->real) d Ta`; `T0:real`; `T1:real`]
                P2BU_GREEDY) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbus] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BU_RBU_MONO THEN EXISTS_TAC `Ta:real` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC P2BU_RBUS_EVSUB;
    REPEAT GEN_TAC THEN REWRITE_TAC[p2bu_rbus] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC P2BU_RBU_UNION THEN EXISTS_TAC `Tj:num->real` THEN
                         ACCEPT_TAC th);
    REPEAT STRIP_TAC THEN
    USE_THEN "ex" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`; `top0:B topology`;
      `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
      `W0:num->B->bool`; `phi0:num->B->A`; `Tr:real`; `d:num->num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* The time-0 data of Thm 11.8: the connected time-0 limit of Thm 11.1      *)
(* (P2BU_TIME0_LIMIT, restricted to the component of its base point) along  *)
(* a subsequence, in p2bu_good form.                                          *)

let P2BU_GOOD_START = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t T0.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb)
              ==> ?sub1 (top0:B topology) atlas0 g0 xl0 W0 (phi0:num->B->A).
                     p3_subseq sub1 /\
                     p2bu_good (C,eps,kappa,r0,mu) (\n. V (sub1 n)) (\n. x (sub1 n))
                       (\n. t (sub1 n)) T0 (top0,atlas0) g0 xl0 W0 phi0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BU_TIME0_LIMIT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t0l")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 (LABEL_TAC "cc")
    (LABEL_TAC "back"))))))) THEN
  USE_THEN "t0l" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[o_DEF]))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub1 n` (LABEL_TAC "ge") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)`; `\n. (x:num->A) ((sub1:num->num) n)`;
    `\n. (t:num->real) ((sub1:num->num) n)`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)) ((t:num->real) (sub1 n)) ((x:num->A) (sub1 n))`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `xl:B`]
   P2CO_P3_SLICE_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)` P2CO_REGULAR_SLICES) THEN ANTS_TAC THENL
     [USE_THEN "bseq" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN SIMP_TAC[];
      DISCH_TAC THEN REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(MATCH_ACCEPT_TAC o SPECL [`(sub1:num->num) n`; `s:real`])];
    ALL_TAC] THEN
  REWRITE_TAC[P2C_SLICE_LIMIT_WITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_TAC `phi:num->B->A`))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`sub1:num->num`;
    `subtopology (top:B topology) {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) {y | mfd_joinable (top:B topology,atlas) xl y}`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool) {y | mfd_joinable (top:B topology,atlas) xl y} (g:B->real^3^3)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  ASM_REWRITE_TAC[p2bu_good] THEN REPEAT CONJ_TAC THEN
  FIRST
   [MP_TAC(ISPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `sub1:num->num`] P2BU_VBLOWUP_SUBSEQ) THEN
    ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
    REPEAT GEN_TAC THEN USE_THEN "sep" (fun th -> REWRITE_TAC[th]) THEN NO_TAC;
    X_GEN_TAC `A:real` THEN USE_THEN "cc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    X_GEN_TAC `Tb:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `r0:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Tb:real`;
                   `sub1:num->num`] P2BU_BACK_SUBSEQ) THEN
    ASM_SIMP_TAC[o_DEF] THEN NO_TAC]);;

(* With sec >= 0, the scalar bound of Cor 11.16 on balls bounds abs Rm.     *)

let P2BU_BALL_RM_BOUND = prove
 (`!(top:B topology) atlas (g:real->B->real^3^3) xl T0.
     smooth_manifold_atlas top atlas /\
     (!s. --T0 < s /\ s <= &0
          ==> riemannian_metric atlas (g s) /\
              (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                       ==> &0 <= mfd_sectional atlas (g s) y u v)) /\
     (!A. ?K. !s y. --T0 < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                    ==> mfd_scalar atlas (g s) y <= K)
     ==> (!A. ?K. !s y. --T0 < s /\ s <= &0 /\ y IN mfd_ball (top,atlas) (g (&0)) xl A
                        ==> mfd_rm_norm atlas (g s) y <= K)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Jp") (LABEL_TAC "sc"))) THEN
  X_GEN_TAC `A:real` THEN USE_THEN "sc" (X_CHOOSE_TAC `K:real` o SPEC `A:real`) THEN
  EXISTS_TAC `K / &2` THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl A` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--T0 < s`) (ASSUME `s <= &0`)) o
                 SPEC `s:real`) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) y / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= k ==> a / &2 <= k / &2`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* MT Thm 11.8, the first part (T0 finite) in view form, with the bound of  *)
(* MT Cor 11.16 on balls: the time-0 limit,                                  *)
(* RBU(T0) by the recursion, the flow limit on (-T0,0] with Cor 11.16 there  *)
(* (P2BU_FLOW_CTX at Tr = T0), and the conversion to p3_flow_limit.          *)

let P2BU_THM_11_8_PART1 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\ P2C_COR_11_16_FLOW_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu) (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
              ==> !T0. &0 < T0 /\
                       (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb)
                       ==> ?sub (top:B topology) atlas g xl.
                              p3_subseq sub /\
                              p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                                (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                (top,atlas) g xl T0 /\
                              (!s. --T0 < s /\ s <= &0
                                   ==> mfd_complete (top,atlas) (g s) /\
                                       !y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                                               ==> &0 <= mfd_sectional atlas (g s) y u v) /\
                              (!a. --T0 < a
                                   ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                                 ==> mfd_rm_norm atlas (g s) y <= K) /\
                              (!A. ?K. !s y. --T0 < s /\ s <= &0 /\
                                             y IN mfd_ball (top,atlas) (g (&0)) xl A
                                             ==> mfd_rm_norm atlas (g s) y <= K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_GOOD_START) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gs"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_RBU_FULL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "full"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_FLOW_CTX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fc"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  X_GEN_TAC `T0:real` THEN STRIP_TAC THEN
  (* the connected time-0 limit *)
  USE_THEN "gs" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `T0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top0:B topology`
    (X_CHOOSE_THEN `atlas0:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl0:B` (X_CHOOSE_THEN `W0:num->B->bool` (X_CHOOSE_THEN `phi0:num->B->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "good"))))))))) THEN
  (* RBU(T0) along a further subsequence *)
  USE_THEN "full" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)`; `\n. (x:num->A) ((sub1:num->num) n)`;
    `\n. (t:num->real) ((sub1:num->num) n)`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `W0:num->B->bool`; `phi0:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "rb" o REWRITE_RULE[p2bu_rbus]))) THEN
  SUBGOAL_THEN `!n:num. n <= d n` (LABEL_TAC "ge") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BU_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o REWRITE_RULE[p2bu_good]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bs1") (CONJUNCTS_THEN2 (LABEL_TAC "sep1")
    (CONJUNCTS_THEN2 (LABEL_TAC "cc1") (CONJUNCTS_THEN2 (LABEL_TAC "back1")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl1") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  (* the flow limit on (-T0,0] with Cor 11.16 *)
  USE_THEN "fc" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) n))`;
    `\n. (x:num->A) ((sub1:num->num) ((d:num->num) n))`;
    `\n. (t:num->real) ((sub1:num->num) ((d:num->num) n))`; `T0:real`; `top0:B topology`;
    `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
    `\n. (W0:num->B->bool) ((d:num->num) n)`; `\n. (phi0:num->B->A) ((d:num->num) n)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MP_TAC(ISPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
        `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)`; `\n. (x:num->A) ((sub1:num->num) n)`;
        `\n. (t:num->real) ((sub1:num->num) n)`; `d:num->num`] P2BU_VBLOWUP_SUBSEQ) THEN
      ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
      REPEAT GEN_TAC THEN USE_THEN "sep1" (MP_TAC o SPECL [`(d:num->num) n`; `s:real`]) THEN
      REWRITE_TAC[] THEN NO_TAC;
      X_GEN_TAC `A:real` THEN USE_THEN "cc1" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(d:num->num) n`) THEN REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)`; `\n. (x:num->A) ((sub1:num->num) n)`;
        `\n. (t:num->real) ((sub1:num->num) n)`;
        `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) n)) ((t:num->real) (sub1 n))
                         ((x:num->A) (sub1 n))`;
        `top0:B topology`; `atlas0:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl0:B`;
        `W0:num->B->bool`; `phi0:num->B->A`; `d:num->num`] P2BU_SLICE_LIMIT_SUBSEQ) THEN
      ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
      USE_THEN "rb" MP_TAC THEN REWRITE_TAC[] THEN NO_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub3:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[p2bu_flowctx; o_DEF]))))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "flw") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Jp") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "rmb")
    (LABEL_TAC "sc")))))))))))) THEN
  SUBGOAL_THEN
   `p3_flow_limit_on (\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))
      (\n. (x:num->A) (sub1 (d (sub3 n)))) (\n. (t:num->real) (sub1 (d (sub3 n))))
      (\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (sub1 (d (sub3 n)))) (t (sub1 (d (sub3 n))))
                       (x (sub1 (d (sub3 n)))))
      {s | --T0 < s /\ s <= &0} (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
      (g:real->B->real^3^3) (xl:B)`
  (LABEL_TAC "fon") THENL
   [REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
    MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
    USE_THEN "flw" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the conversion: times min T0 (T0 (1 - 1/(k+2))) *)
  MP_TAC(ISPECL [`\k:num. T0:real`; `T0:real`] P2BU_TS_PROPS) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ts1") (LABEL_TAC "ts2")) THEN
  MP_TAC(ISPECL [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. (x:num->A) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. (t:num->real) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n)))`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub1:num->num) ((d:num->num) ((sub3:num->num) n))))
                     ((t:num->real) (sub1 (d (sub3 n)))) ((x:num->A) (sub1 (d (sub3 n))))`;
    `{s:real | --T0 < s /\ s <= &0}`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `\k:num. min T0 (T0 * (&1 - inv(&k + &2)))`] P2BU_FLOW_LIMIT_OF_ON) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "fon" ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN USE_THEN "ts1" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub4:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `T0:real`))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `a:real` THEN DISCH_TAC THEN
      USE_THEN "ts2" (MP_TAC o C MP (ASSUME `a < T0`) o SPEC `a:real`) THEN
      DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
      USE_THEN "upto" ACCEPT_TAC];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(sub1:num->num) o (d:num->num) o (sub3:num->num) o (sub4:num->num)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
    `xl:B`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC P2BU_SUBSEQ_O THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_DEF] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[o_DEF] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p3_flow_limit" with _ -> false))
          (concl th)));
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--T0 < s`) (ASSUME `s <= &0`)) o
                   SPEC `s:real`) THEN SIMP_TAC[];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN ASM_CASES_TAC `a <= &0` THENL
     [USE_THEN "rmb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2BU_BALL_RM_BOUND THEN REPEAT CONJ_TAC THENL
     [USE_THEN "fon" (MP_TAC o REWRITE_RULE[p3_flow_limit_on]) THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "Jp" (MP_TAC o C MP (CONJ (ASSUME `--T0 < s`) (ASSUME `s <= &0`)) o
                     SPEC `s:real`) THEN SIMP_TAC[];
      USE_THEN "sc" ACCEPT_TAC]]);;

