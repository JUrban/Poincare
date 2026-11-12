(* ========================================================================= *)
(* Unit pc_rfs_limpinch: curvature of limit metrics (rfs_limit_metric) at a *)
(* point of the open set Om.                                                *)
(*  - RFS_LIMIT_CURV: the scalar and the sectional curvatures of g(t)        *)
(*    converge to those of the limit metric gl as t -> ts from the left,    *)
(*    uniformly in the plane, and the sectional curvatures of gl at the     *)
(*    point are bounded (full atlas, preferred chart; LCK_CURVATURE_         *)
(*    STABILITY at k = 2);                                                   *)
(*  - RFS_LIMIT_SEC_MIN: the least sectional curvature converges;            *)
(*  - RFS_PINCHED_AT_LIMIT: Hamilton-Ivey pinching (rfs_pinched_at) passes   *)
(*    to the limit metric at ts > 0.                                         *)
(* Auxiliary lemmas: left limits along the left half-line net at ts, and     *)
(* infima of uniformly close plane functions.                                *)
(* Used in the proof of MT Lemma 15.11 (pc_p3e_15_11, step S4) and by        *)
(* pc_p2c_horns (pinching of the maximal extension).                         *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfa_sec.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Left limits, infima over planes, the curvature of limit metrics, and      *)
(* pinching at the limit.                                                    *)
(* ========================================================================= *)

let RFSLP_NONTRIVIAL_LEFT = prove
 (`!ts. ~trivial_limit (atreal ts within {s | s <= ts})`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{s:real | s <= ts}`; `ts:real`] TRIVIAL_LIMIT_WITHIN_REALINTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; is_realinterval] THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `ts - &1`) THEN REAL_ARITH_TAC]);;
let RFSLP_LEFT_LIM_NET = prove
 (`!f l ts.
     (!e. &0 < e ==> ?d. &0 < d /\ !t. ts - d < t /\ t < ts ==> abs(f t - l) <= e)
     ==> (f ---> l) (atreal ts within {s | s <= ts})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;
let RFSLP_LEFT_EVENTUALLY = prove
 (`!P ts d. &0 < d /\ (!t. ts - d < t /\ t < ts ==> P t)
            ==> eventually P (atreal ts within {s | s <= ts})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;
let RFSLP_NONCOLLINEAR_BASIS = prove
 (`~collinear {vec 0:real^3,basis 1,basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
  SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;
let RFSLP_INF_PLANES_CLOSE = prove
 (`!(f:real^3->real^3->real) h e B.
     (!u v. ~collinear {vec 0,u,v} ==> abs(f u v) <= B) /\
     (!u v. ~collinear {vec 0,u,v} ==> abs(h u v - f u v) <= e)
     ==> abs(inf {h u v | u,v | ~collinear {vec 0,u,v}} -
             inf {f u v | u,v | ~collinear {vec 0,u,v}}) <= e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B") (LABEL_TAC "C")) THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0:real^3,u,v}
          ==> --B <= (f:real^3->real^3->real) u v /\
              --B - e <= (h:real^3->real^3->real) u v /\
              f u v - e <= h u v /\ h u v - e <= f u v`
  (LABEL_TAC "F") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "B" (fun th -> MP_TAC(MP (SPECL [`u:real^3`; `v:real^3`] th)
                                       (ASSUME `~collinear {vec 0:real^3,u,v}`))) THEN
    USE_THEN "C" (fun th -> MP_TAC(MP (SPECL [`u:real^3`; `v:real^3`] th)
                                       (ASSUME `~collinear {vec 0:real^3,u,v}`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = {(f:real^3->real^3->real) u v | u,v | ~collinear {vec 0,u,v}}` THEN
  ABBREV_TAC `s' = {(h:real^3->real^3->real) u v | u,v | ~collinear {vec 0,u,v}}` THEN
  SUBGOAL_THEN `~(s:real->bool = {}) /\ ~(s':real->bool = {})` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "s'"] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC RFSLP_NONCOLLINEAR_BASIS THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN s ==> --B <= x) /\ (!x. x IN s' ==> --B - e <= x)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "s'"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "F" (fun th -> MP_TAC(MP (SPECL [`u:real^3`; `v:real^3`] th)
                                       (ASSUME `~collinear {vec 0:real^3,u,v}`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inf s - e <= inf s'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real->bool`; `(f:real^3->real^3->real) u v`] INF_LE_ELEMENT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC `--B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "F" (fun th -> MP_TAC(MP (SPECL [`u:real^3`; `v:real^3`] th)
                                       (ASSUME `~collinear {vec 0:real^3,u,v}`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inf s' - e <= inf s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INF THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s':real->bool`; `(h:real^3->real^3->real) u v`] INF_LE_ELEMENT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC `--B - e:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "F" (fun th -> MP_TAC(MP (SPECL [`u:real^3`; `v:real^3`] th)
                                       (ASSUME `~collinear {vec 0:real^3,u,v}`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFS_LIMIT_CURV = prove
 (`!(top:A topology) atlas Om ts (g:real->A->real^3^3) gl y.
     smooth_manifold_atlas top atlas /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ open_in top Om /\ y IN Om /\
     (?d0. &0 < d0 /\ !t. ts - d0 < t /\ t < ts ==> riemannian_metric atlas (g t))
     ==> (?B. !u v. ~collinear {vec 0,u,v}
                    ==> abs(mfd_sectional atlas gl y u v) <= B) /\
         !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. ts - d < t /\ t < ts
                         ==> abs(mfd_scalar atlas (g t) y - mfd_scalar atlas gl y) <= e /\
                             !u v. ~collinear {vec 0,u,v}
                                   ==> abs(mfd_sectional atlas (g t) y u v -
                                           mfd_sectional atlas gl y u v) <= e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[rfs_limit_metric] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "CV")) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  SUBGOAL_THEN `c IN (atlas:((A->bool)#(A->real^3))->bool) /\ (y:A) IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER Om)` THEN
  SUBGOAL_THEN `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN USE_THEN "MF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) y IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `sqrt(lrm_deriv_norm2 0
                  (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)
                  (SND(c:(A->bool)#(A->real^3)) y))` THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sqrt(abs(lrm_deriv_norm2 0
                    (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)
                    (SND(c:(A->bool)#(A->real^3)) y)))`; `e:real`]
                (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ST"))) THEN
  USE_THEN "CV" (MP_TAC o SPECL [`{y:A}`; `2`; `eta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; COMPACT_IN_SING; SING_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `min d0 d1` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                  ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                                 ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                     ((g:real->A->real^3^3) t)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)` THEN
      SIMP_TAC[metric_field];
      EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar; mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ST" (MP_TAC o SPECL [`S:real^3->bool`;
                                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl`;
                                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                                    ((g:real->A->real^3^3) t)`;
                                 `SND(c:(A->bool)#(A->real^3)) y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN REAL_ARITH_TAC;
      USE_THEN "D1" (MP_TAC o SPECL [`t:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    SIMP_TAC[]]);;

let RFS_LIMIT_SEC_MIN = prove
 (`!(top:A topology) atlas Om ts (g:real->A->real^3^3) gl y.
     smooth_manifold_atlas top atlas /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ open_in top Om /\ y IN Om /\
     (?d0. &0 < d0 /\ !t. ts - d0 < t /\ t < ts ==> riemannian_metric atlas (g t))
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. ts - d < t /\ t < ts
                         ==> abs(mfd_sec_min atlas (g t) y - mfd_sec_min atlas gl y) <= e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RFS_LIMIT_CURV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) (LABEL_TAC "L")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "L" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  MP_TAC(ISPECL [`\u v. mfd_sectional atlas (gl:A->real^3^3) (y:A) u v`;
                 `\u v. mfd_sectional atlas ((g:real->A->real^3^3) t) (y:A) u v`;
                 `e:real`; `B:real`] RFSLP_INF_PLANES_CLOSE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let RFS_PINCHED_AT_LIMIT = prove
 (`!(top:A topology) atlas Om ts (g:real->A->real^3^3) gl y.
     smooth_manifold_atlas top atlas /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ open_in top Om /\ y IN Om /\ &0 < ts /\
     (?d0. &0 < d0 /\
           !t. ts - d0 < t /\ t < ts
               ==> riemannian_metric atlas (g t) /\ rfs_pinched_at atlas (g t) t y)
     ==> rfs_pinched_at atlas gl ts y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "P0")))))))) THEN
  SUBGOAL_THEN `?d0. &0 < d0 /\ !t. ts - d0 < t /\ t < ts
                     ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `net = atreal ts within {s:real | s <= ts}` THEN
  SUBGOAL_THEN `~trivial_limit (net:(real)net)` ASSUME_TAC THENL
   [EXPAND_TAC "net" THEN REWRITE_TAC[RFSLP_NONTRIVIAL_LEFT]; ALL_TAC] THEN
  SUBGOAL_THEN `((\t. mfd_scalar atlas ((g:real->A->real^3^3) t) (y:A)) --->
                 mfd_scalar atlas gl y) net`
  ASSUME_TAC THENL
   [EXPAND_TAC "net" THEN MATCH_MP_TAC RFSLP_LEFT_LIM_NET THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `Om:A->bool`; `ts:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`;
                   `y:A`] RFS_LIMIT_CURV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t. --(mfd_sec_min atlas ((g:real->A->real^3^3) t) (y:A))) --->
                 --(mfd_sec_min atlas gl y)) net`
  ASSUME_TAC THENL
   [EXPAND_TAC "net" THEN MATCH_MP_TAC RFSLP_LEFT_LIM_NET THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `Om:A->bool`; `ts:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`;
                   `y:A`] RFS_LIMIT_SEC_MIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--a - --b = --(a - b)`; REAL_ABS_NEG] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\t:real. t) ---> ts) net` ASSUME_TAC THENL
   [EXPAND_TAC "net" THEN REWRITE_TAC[REALLIM_WITHINREAL_ID]; ALL_TAC] THEN
  REWRITE_TAC[rfs_pinched_at] THEN CONJ_TAC THENL
   [(* the lower bound of R *)
    MP_TAC(ISPECL [`net:(real)net`;
                   `\t. mfd_scalar atlas ((g:real->A->real^3^3) t) (y:A) -
                        --(&6) / (&4 * t + &1)`;
                   `mfd_scalar atlas (gl:A->real^3^3) (y:A) - --(&6) / (&4 * ts + &1)`;
                   `&0`] REALLIM_LBOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REALLIM_DIV THEN REWRITE_TAC[REALLIM_CONST] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
        MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "net" THEN MATCH_MP_TAC RFSLP_LEFT_EVENTUALLY THEN
        EXISTS_TAC `min d0 ts` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        USE_THEN "P0" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[rfs_pinched_at] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the Hamilton-Ivey clause *)
  DISCH_TAC THEN
  ABBREV_TAC `X0 = --(mfd_sec_min atlas (gl:A->real^3^3) (y:A))` THEN
  MP_TAC(ISPECL [`net:(real)net`;
                 `\t. mfd_scalar atlas ((g:real->A->real^3^3) t) (y:A) -
                      &2 * --(mfd_sec_min atlas (g t) y) *
                      (log(--(mfd_sec_min atlas (g t) y)) + log(&1 + t) - &3)`;
                 `mfd_scalar atlas (gl:A->real^3^3) (y:A) -
                  &2 * X0 * (log X0 + log(&1 + ts) - &3)`;
                 `&0`] REALLIM_LBOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`log`; `net:(real)net`;
                       `\t. --(mfd_sec_min atlas ((g:real->A->real^3^3) t) (y:A))`;
                       `X0:real`] REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
        ASM_SIMP_TAC[REAL_CONTINUOUS_AT_LOG];
        MP_TAC(ISPECL [`net:(real)net`; `\t:real. log(&1 + t)`; `\t:real. &3`;
                       `log(&1 + ts)`; `&3`] REALLIM_SUB) THEN
        REWRITE_TAC[REALLIM_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`log`; `net:(real)net`; `\t:real. &1 + t`; `&1 + ts`]
                      REALLIM_REAL_CONTINUOUS_FUNCTION) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_AT_LOG THEN ASM_REAL_ARITH_TAC;
          MP_TAC(ISPECL [`net:(real)net`; `\t:real. &1`; `\t:real. t`; `&1`; `ts:real`]
                        REALLIM_ADD) THEN
          ASM_REWRITE_TAC[REALLIM_CONST]]];
      ALL_TAC] THEN
    (* eventually the inequality holds, since eventually X(t) > 0 *)
    UNDISCH_TAC `((\t. --(mfd_sec_min atlas ((g:real->A->real^3^3) t) (y:A))) ---> X0) net` THEN
    EXPAND_TAC "net" THEN REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < X0`) o SPEC `X0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "X"))) THEN
    MATCH_MP_TAC RFSLP_LEFT_EVENTUALLY THEN
    EXISTS_TAC `min d (min d0 ts)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "X" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "P0" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_pinched_at] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

