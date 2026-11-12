(* ========================================================================= *)
(* pc_p2a_l72i: O10 view-X form, part 3, MT Lemma 7.2(b1).                   *)
(* Location-controlled smoothing: copies of the corner rounding              *)
(* (P2AXS_ROUND1) and of the singular-corner removal (P2AXS_INT_STEP) that   *)
(* keep a location property p2aj_loc of the curve (each point has a set,     *)
(* open in the slices of a time interval, on which a predicate Q holds), so  *)
(* that the smoothed curve stays in the fat boxes.  Then the competitor of   *)
(* (b1): a curve of the sequence whose last piece is replaced by a BVP       *)
(* solution ending at the end point of the limit.                            *)
(* The first part: the location property.                                    *)
(* ========================================================================= *)

needs "src/pc_p2a_l72h.ml";;
needs "src/pc_p2a_smx.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Location control for the smoothing of curves.  p2aj_loc V tt b Q gamma:  *)
(* every point gamma tau, 0 < tau <= b, has a set O, open in the slices of  *)
(* a time interval (t1,t2) around tau, on which Q t holds for t in (t1,t2). *)
(* The roundings and corner removals below keep this property, so the      *)
(* smoothed curve satisfies Q (used for the membership in the fat boxes).   *)
(* ------------------------------------------------------------------------- *)

let p2aj_loc = new_definition
 `p2aj_loc (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
           (tt:real) (b:real) (Q:real->A->bool) (gamma:real->A) <=>
    !tau. &0 < tau /\ tau <= b
          ==> ?O t1 t2. t1 < tau /\ tau < t2 /\ gamma tau IN O /\
                        (!t. t1 < t /\ t < t2 ==> open_in (p2a_vtop V (tt - t)) O) /\
                        (!t y. t1 < t /\ t < t2 /\ &0 < t /\ t <= b /\ y IN O ==> Q t y)`;;

let P2AJ_LOC_Q = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt b Q (gamma:real->A).
     p2aj_loc V tt b Q gamma ==> !tau. &0 < tau /\ tau <= b ==> Q tau (gamma tau)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2aj_loc] THEN DISCH_TAC THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* A modification of the curve on (c1,c2] inside one set O of the property. *)

let P2AJ_LOC_PATCH = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt b Q (gamma:real->A) gamma1 O t1 t2 c1 c2.
     p2aj_loc V tt b Q gamma /\
     (!t. t1 < t /\ t < t2 ==> open_in (p2a_vtop V (tt - t)) O) /\
     (!t y. t1 < t /\ t < t2 /\ &0 < t /\ t <= b /\ y IN O ==> Q t y) /\
     t1 < c1 /\ c2 < t2 /\
     (!tau. ~(c1 < tau /\ tau <= c2) ==> gamma1 tau = gamma tau) /\
     (!tau. c1 < tau /\ tau <= c2 ==> gamma1 tau IN O)
     ==> p2aj_loc V tt b Q gamma1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2aj_loc] THEN STRIP_TAC THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `c1 < tau /\ tau <= c2` THENL
   [MAP_EVERY EXISTS_TAC [`O:A->bool`; `t1:real`; `t2:real`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma1:real->A`)) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "IN")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* Rounding corners with location control. *)

(* Rounding one corner with control of the location.                      *)

let P2AJ_ROUND1_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P tau1 e (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_adm V tt x b gamma /\
     p2a_pc1 V tt gamma (&0) b P /\ &0 < tau1 /\ tau1 < b /\
     p2a_atlas_const V (tt - tau1) /\ &0 < e /\ p2aj_loc V tt b Q gamma
     ==> ?gamma1. p2a_adm V tt x b gamma1 /\ p2a_pc1 V tt gamma1 (&0) b (P DELETE tau1) /\
                  gamma1 b = gamma b /\
                  p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e /\
                  (!tau. ~(abs(tau - tau1) < e) ==> gamma1 tau = gamma tau) /\
                  (!tau. &0 <= tau /\ tau <= b
                         ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                      (p2a_vmetric V (tt - tau)) (gamma1 tau) (gamma tau) < e) /\
                  p2aj_loc V tt b Q gamma1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau1` (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `sqrt tau1` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s0 pow 2` o REWRITE_RULE[p2aj_loc] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aj_loc")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `OO:A->bool` (X_CHOOSE_THEN `tO1:real` (X_CHOOSE_THEN `tO2:real`
    STRIP_ASSUME_TAC))) THEN
  (* the region chart at the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2AXR_REGION_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; P2AX_ADM_IMP]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  (* corner bounds *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `P:real->bool`; `s0:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`] P2A_CORNER_S_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0 + k0 / &2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[NORM_POS_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M`
  ASSUME_TAC THENL [REWRITE_TAC[p2a_cdata] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice atlas is constant near the corner time *)
  UNDISCH_TAC `p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s0 pow 2)` THEN
  REWRITE_TAC[p2a_atlas_const] THEN
  DISCH_THEN(X_CHOOSE_THEN `da:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`s0:real`; `da:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k1. &0 < k1 /\ k1 < k0 /\ k1 <= ha` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (k0 / &2) ha` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* uniform slice distances near the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `s0 - k1`; `s0 + k1`; `s0:real`;
                 `(gamma:real->A)(s0 pow 2)`] P2A_SLICE_DIST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `da:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x - y) < d ==> abs((t - x) - (t - y)) < d`) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ha:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIST"))))) THEN
  SUBGOAL_THEN `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2) SUBSET
                IMAGE phi (U INTER W)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "DIST" (MP_TAC o SPECL [`s0:real`; `z:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* a bound for the s-Lagrangian near the corner *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - k1`; `s0 + k1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2)`;
                 `s0 - k1 / &2`; `s0 + k1 / &2`; `(&1 + p2a_bc) * M`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th) &&
      can (find_term ((=) `k0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB"))] THEN
  (* the chart radius for the location *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `tt - s0 pow 2`; `OO:A->bool`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                P2A_CHART_INV_NBHD) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (phi((gamma:real->A)(s0 pow 2))) =
                  gamma(s0 pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b'':real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; FUN_IN_IMAGE];
    DISCH_THEN(X_CHOOSE_THEN `rO:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RO")))] THEN
  MP_TAC(SPECL [`rO:real`; `M:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kO:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KO"))) THEN
  MP_TAC(SPECL [`s0:real`; `min (s0 pow 2 - tO1) (tO2 - s0 pow 2)`] P2A_SQ_NEAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hW:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HW"))) THEN
  (* the choice of the scale k *)
  MP_TAC(SPECL [`r / &2`; `M:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KC"))) THEN
  MP_TAC(SPECL [`e:real`; `L * M`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KD"))) THEN
  MP_TAC(SPECL [`e:real`; `&3 * abs Kb`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ke:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KE"))) THEN
  MP_TAC(SPECL [`s0:real`; `e:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `he:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HE"))) THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k <= k1 / &2 /\ k <= r / &2 /\ k <= kc /\ k <= kd /\ k <= ke /\ k <= he / &2 /\
        k <= kO /\ k <= hW / &2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min (min (k1 / &2) (r / &2)) (min (min kc kd) (min ke (he / &2))))
                    (min kO (hW / &2))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * M < r / &2 /\ k * (L * M) < e /\ k * (&3 * abs Kb) < e /\ k * M < rO`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "KC" MATCH_MP_TAC; USE_THEN "KD" MATCH_MP_TAC; USE_THEN "KE" MATCH_MP_TAC;
      USE_THEN "KO" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k < k0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  (* the blend and the curve stay in the closed ball of radius r/2 *)
  SUBGOAL_THEN
   `!s. abs(s - s0) <= k
        ==> (phi:A->real^N)((gamma:real->A)(s pow 2)) IN cball(phi(gamma(s0 pow 2)),r / &2) /\
            p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s) IN
            cball(phi(gamma(s0 pow 2)),r / &2)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    SUBGOAL_THEN `M * abs(s - s0) <= k * M` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * abs(s - s0)` THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "BNEAR" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < k
        ==> p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                      s0 k (lift s) IN IMAGE phi (U INTER W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      not(is_forall(concl th)))) THEN
    USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `p2a_round (gamma:real->A) U W (phi:A->real^N) s0 k` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_ROUND_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2A_ROUND_PC1 THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2a_round] THEN
    SUBGOAL_THEN `~(b <= (s0 - &3 * k / &4) pow 2) /\ ~(b <= (s0 + &3 * k / &4) pow 2)`
    (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(s0 + &3 * k / &4) pow 2 < b /\ (s0 - &3 * k / &4) pow 2 <= (s0 + &3 * k / &4) pow 2`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(s0 + k0) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_ROUND_LENGTH THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `Kb:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THEN USE_THEN "KB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `k * Kb <= k * abs Kb` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_round] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(abs(tau - s0 pow 2) < e)` THEN REWRITE_TAC[] THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 - &3 * k / &4`) THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 + &3 * k / &4`) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2A_ROUND_DIST THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `r:real`;
                          `L:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AJ_LOC_PATCH THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `OO:A->bool`; `tO1:real`; `tO2:real`;
                          `(s0 - &3 * k / &4) pow 2`; `(s0 + &3 * k / &4) pow 2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "HW" (MP_TAC o SPEC `s0 - &3 * k / &4`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      USE_THEN "HW" (MP_TAC o SPEC `s0 + &3 * k / &4`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_round] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_round] THEN
      SUBGOAL_THEN `~(tau <= (s0 - &3 * k / &4) pow 2)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[p2a_rsig]] THEN
      MP_TAC(SPECL [`s0 - &3 * k / &4`; `s0 + &3 * k / &4`; `tau:real`] P2A_SQRT_BETWEEN) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "RO" (MP_TAC o SPEC
        `p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                   s0 k (lift(sqrt tau))`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      USE_THEN "BNEAR" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[dist] THEN
      SUBGOAL_THEN `M * abs(sqrt tau - s0) <= k * M` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;



(* Rounding all corners with control of the location.                      *)

let P2AJ_SMOOTH_INDUCT_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V
     ==> !P. FINITE P
             ==> !(gamma:real->A) e.
                   p2a_adm V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b P /\
                   (!s. s IN P ==> &0 < s /\ s < b /\ p2a_atlas_const V (tt - s)) /\ &0 < e /\
                   p2aj_loc V tt b Q gamma
                   ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                                p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                                (!tau. (!s. s IN P ==> ~(abs(tau - s) < e))
                                       ==> gamma' tau = gamma tau) /\
                                (!tau. &0 <= tau /\ tau <= b
                                       ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                                    (p2a_vmetric V (tt - tau))
                                                    (gamma' tau) (gamma tau) < e) /\
                                p2aj_loc V tt b Q gamma'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[p2a_adm1; REAL_LE_ADDR] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `tau:real`] P2A_ADM_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau1:real`; `P:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau1 /\ tau1 < b /\
                p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - tau1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau1:real`; `P:real->bool`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = min (e / &2) (d / &3)` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= e / &2 /\ &3 * e1 <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `(tau1:real) INSERT P`; `tau1:real`; `e1:real`; `Q:real->A->bool`]
                P2AJ_ROUND1_LOC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((tau1:real) INSERT P) DELETE tau1 = P` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S1") (CONJUNCTS_THEN2 (LABEL_TAC "D1") ASSUME_TAC))))))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`gamma1:real->A`; `e1:real`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S2") (CONJUNCTS_THEN2 (LABEL_TAC "D2") ASSUME_TAC)))))) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `(gamma1:real->A) tau` THEN CONJ_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "S1" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau1:real`) THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs(tau - tau1) < e1` THENL
   [SUBGOAL_THEN `(gamma':real->A) tau = gamma1 tau` SUBST1_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(gamma1:real->A) tau = gamma tau` (SUBST1_TAC o SYM) THENL
     [USE_THEN "S1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;


let P2AJ_SMOOTHING_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_adm V tt x b gamma /\ &0 < e /\
     p2aj_loc V tt b Q gamma
     ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                  p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                  (!tau. &0 <= tau /\ tau <= b
                        ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                     (p2a_vmetric V (tt - tau)) (gamma' tau) (gamma tau) < e) /\
                  p2aj_loc V tt b Q gamma'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?P. p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt gamma (&0) b P`
  (X_CHOOSE_TAC `P:real->bool`) THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `P:real->bool`]
                P2A_PC1_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Q:real->A->bool`]
                P2AJ_SMOOTH_INDUCT_LOC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{s | s IN P /\ &0 < s /\ s < b /\
                                p2a_atlas_const (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                                  (tt - s)}`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[p2a_pc1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;


(* Removing singular corners with location control. *)

(* Removing one interior singular corner with control of the location.     *)

let P2AJ_INT_STEP_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P B tau0 e (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2axs_pc1b V tt gamma (&0) b P B /\ &0 < tau0 /\ tau0 < b /\ &0 < e /\
     p2aj_loc V tt b Q gamma
     ==> ?gamma1 P1. p2a_admx V tt x b gamma1 /\
                     p2axs_pc1b V tt gamma1 (&0) b P1 (B DELETE tau0) /\
                     gamma1 b = gamma b /\
                     p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e /\
                     p2aj_loc V tt b Q gamma1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (P:real->bool) /\ FINITE (B:real->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2axs_pc1b]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau0` (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC)
  THENL
   [EXISTS_TAC `sqrt tau0` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s0 pow 2` o REWRITE_RULE[p2aj_loc] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aj_loc")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `OO:A->bool` (X_CHOOSE_THEN `tO1:real` (X_CHOOSE_THEN `tO2:real`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b /\ s0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  (* the region chart at the corner and the punctured window *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2AXR_REGION_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `s0:real`]
                P2AXR_MINX_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))))) THEN
  ABBREV_TAC `h1 = min h (min s0 (sqrt b - s0)) / &2` THEN
  SUBGOAL_THEN `&0 < h1 /\ h1 < h /\ h1 < s0 /\ s0 + h1 < sqrt b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `min h (min s0 (sqrt b - s0)) / &2 = (h1:real)` (K ALL_TAC) THEN
  SUBGOAL_THEN `!s. s0 - h1 < s /\ s < s0 + h1 ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  (LABEL_TAC "WIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 < s /\ s < s0 + h1 ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  (LABEL_TAC "WINLE") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 <= s /\ s <= s0 + h1 ==> s pow 2 < b` (LABEL_TAC "SB") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - h1 <= s /\ s <= s0 + h1 ==> (gamma:real->A)(s pow 2) IN U INTER W`
  (LABEL_TAC "MEM") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN
    USE_THEN "SB" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s0 - h1 <= s /\ s <= s0 + h1 /\ ~(s = s0)
        ==> (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) differentiable (at (lift s)) /\
            (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
              continuous (at (lift s))`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
    USE_THEN "SB" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s0 - h1) (s0 + h1)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?rho0. &0 < rho0 /\
                       cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0) SUBSET
                       IMAGE phi (U INTER W) /\
                       (!y. y IN cball(phi(gamma(s0 pow 2)),rho0)
                            ==> chart_inv (U INTER W,phi) y IN (OO:A->bool))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?rho1. &0 < rho1 /\
                         cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho1) SUBSET
                         IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p2a_lsmooth] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
      REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `tt - s0 pow 2`; `OO:A->bool`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                  P2A_CHART_INV_NBHD) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (phi((gamma:real->A)(s0 pow 2))) =
                    gamma(s0 pow 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC P2A_REGION_CHART_INV THEN
        MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b'':real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; FUN_IN_IMAGE];
      DISCH_THEN(X_CHOOSE_THEN `rO:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `min rho1 (rO / &2)` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rO:real`)) (concl th))) THEN
      ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`;
                 `s0 - h1 / &2`; `s0 + h1 / &2`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QB"))))) THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`;
                 `s0 - h1 / &2`; `s0 + h1 / &2`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB")) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. s0 - h1 / &2 <= s /\ s <= s0 + h1 / &2 /\
          y IN cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)
          ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b''
                 (U INTER W,phi)) tt s y (vec 0)) <= Kp`
  (LABEL_TAC "KP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN USE_THEN "KB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC]) THEN
  UNDISCH_THEN `abs(Kb:real) = Kp` (K ALL_TAC) THEN
  (SUBGOAL_THEN `?eps. &0 < eps /\ eps * (&16 * (Cg + &1)) = e`
  (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / (&16 * (Cg + &1))` THEN
    SUBGOAL_THEN `&0 < &16 * (Cg + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < &16 * (Cg + &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * Cg * eps <= e / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (e / &8) (c * eps / &4)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e / &8 /\ eta <= c * eps / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < c * eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  UNDISCH_THEN `min (e / &8) (c * eps / &4) = (eta:real)` (K ALL_TAC) THEN
  (SUBGOAL_THEN `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt gamma b
                real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt x b gamma` THEN
    SIMP_TAC[p2a_admx];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b`;
                 `&0`; `b:real`; `s0 pow 2`; `s0 pow 2`; `eta:real`]
                REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_INTEGRAL_REFL;
               REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KAP"))) THEN
  MP_TAC(SPECL [`s0:real`; `kap:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HK")))) THEN
  (SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(s0 - h1 / &2),lift(s0 + h1 / &2)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s0 - h1 / &2`; `s0 + h1 / &2`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2AXR_ADMX_SCONT (ASSUME
      `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`)] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "WINLE" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift(s0 - h1 / &2),lift(s0 + h1 / &2)]` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift s0`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho0 / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY")))) THEN
  (MP_TAC(ISPECL [`s0 pow 2`; `(P:real->bool) UNION B`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `dP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DP"))) THEN
  MP_TAC(SPECL [`s0:real`; `dP:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hP:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HP"))) THEN
  MP_TAC(SPECL [`min (c * eps / &4) (e / &8)`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KA"))) THEN
  MP_TAC(SPECL [`s0:real`; `min (s0 pow 2 - tO1) (tO2 - s0 pow 2)`] P2A_SQ_NEAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hW:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HW"))) THEN
  ABBREV_TAC `k = min (min (h1 / &2) (min hk hP)) (min (min dy hW) ka) / &4` THEN
  SUBGOAL_THEN `&0 < k /\ &2 * k <= ka /\ k < h1 / &2 /\ k < hk /\ k < hP /\ k < dy /\ k < hW`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  UNDISCH_THEN `min (min (h1 / &2) (min hk hP)) (min (min dy hW) ka) / &4 = (k:real)` (K ALL_TAC) THEN
  (ABBREV_TAC `s1 = s0 - k` THEN ABBREV_TAC `s2 = s0 + k` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < s0 /\ s0 < s2 /\ s1 < s2 /\ s0 - h1 < s1 /\ s2 < s0 + h1 /\
                s0 - h1 / &2 <= s1 /\ s2 <= s0 + h1 / &2`
  STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < s0 pow 2 /\ s0 pow 2 < s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 < b` ASSUME_TAC THENL
   [USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `!r. s1 <= r /\ r <= s2
                    ==> dist((phi:A->real^N)((gamma:real->A)(r pow 2)),phi(gamma(s0 pow 2))) <
                        rho0 / &4`
  (LABEL_TAC "YB") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "DY" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!r. s1 <= r /\ r <= s2
                    ==> (phi:A->real^N)((gamma:real->A)(r pow 2)) IN
                        cball(phi(gamma(s0 pow 2)),rho0)`
  (LABEL_TAC "YC") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    USE_THEN "YB" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!r A. s1 <= r /\ r <= s2
          ==> c * norm A pow 2 <=
              A dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                       (tt - r pow 2) (phi((gamma:real->A)(r pow 2))) ** A)`
  (LABEL_TAC "QBL") THENL
   [MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
    USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `(phi:A->real^N)((gamma:real->A)(r pow 2))`;
                                   `A:real^N`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!r. s1 <= r /\ r <= s2
        ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N))
                         tt r (phi((gamma:real->A)(r pow 2))) (vec 0)) <= Kp`
  (LABEL_TAC "KPL") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KP" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "YC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!u v. s1 <= u /\ u <= s2 /\ s1 <= v /\ v <= s2
          ==> abs(real_integral (real_interval[u pow 2,v pow 2])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                        (real->A->real^N^N)) tt gamma b)) < eta`
  (LABEL_TAC "INT") THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    USE_THEN "KAP" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "SB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `Kp * (s0 - s1) <= c * eps / &4 /\ Kp * (s2 - s0) <= c * eps / &4 /\
                (s2 - s1) * Kp <= e / &8` STRIP_ASSUME_TAC THENL
   [USE_THEN "KA" (MP_TAC o SPEC `k:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "KA" (MP_TAC o SPEC `&2 * k`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1 pow 2 IN B) /\ ~(s2 pow 2 IN B)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "DP" (MP_TAC o SPEC `s1 pow 2`) THEN
      USE_THEN "HP" (MP_TAC o SPEC `s1:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "DP" (MP_TAC o SPEC `s2 pow 2`) THEN
      USE_THEN "HP" (MP_TAC o SPEC `s2:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - h1`; `s0 + h1`; `s1:real`; `s0:real`; `c:real`; `Kp:real`; `eps:real`]
                P2AXS_MID_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QBL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KPL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x < y ==> x <= y`) THEN
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "D1")]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0 - h1`; `s0 + h1`; `s0:real`; `s2:real`; `c:real`; `Kp:real`; `eps:real`]
                P2AXS_START_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "C1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QBL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KPL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x < y ==> x <= y`) THEN
      USE_THEN "INT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "D2")]) THEN
  (SUBGOAL_THEN
   `norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
    &8 * eps * (s2 - s1)` (LABEL_TAC "D") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) +
                 norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2)))) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) pow 2 +
                      norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2))) pow 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s0 pow 2))) -
                   norm((phi:A->real^N)((gamma:real->A)(s0 pow 2)) - phi(gamma(s1 pow 2)))`
                  REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      USE_THEN "D1" MP_TAC THEN USE_THEN "D2" MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
            (inv(s2 - s1) * (s - s1)) % (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))) IN
            cball(phi(gamma(s0 pow 2)),rho0)`
  (LABEL_TAC "ZIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `rho0:real`] CONVEX_CBALL) THEN
    REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN(MP_TAC o SPECL [`(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                               `(phi:A->real^N)((gamma:real->A)(s2 pow 2))`;
                               `inv(s2 - s1) * (s - s1)`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "YC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "YC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`s1:real`; `s2:real`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        MP_TAC(SPECL [`s1:real`; `s2:real`; `s:real`] P2AXS_UNIT_PARAM) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC]) THEN
  (ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                       ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                        (inv(s2 - s1) * (sqrt tau - s1)) %
                        (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(s2 - s1) * (drop v - s1)) %
                             (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `s2:real`; `s0 - h1`; `s0 + h1`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(is_forall(concl th)))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(s2 - s1) % ((phi:A->real^N)((gamma:real->A)(s2 pow 2)) -
                                  phi(gamma(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(s2 - s1) * (drop v - s1)) %
                         (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(s2 - s1) % ((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LSEG") (LABEL_TAC "HRI"))) THEN
  (SUBGOAL_THEN `(sig:real->A) (s1 pow 2) = (gamma:real->A)(s1 pow 2) /\
                sig (s2 pow 2) = gamma(s2 pow 2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `inv(s2 - s1) * (s2 - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `y1 + &1 % (y2 - y1):real^N = y2`] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "MEM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`] P2AXR_REPLACE_X) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ADM1") (LABEL_TAC "LEN1"))] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`; `P:real->bool`; `B:real->bool`]
                P2AXS_REPLACE_PC1B) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P1:real->bool` (LABEL_TAC "PB1"))) THEN
  (SUBGOAL_THEN
   `real_integral (real_interval[s1 pow 2,s2 pow 2])
      (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt sig (s2 pow 2)) =
    p2a_cL (p2a_rlocal V W b'' (U INTER W,phi:A->real^N)) tt
      (\v. phi((gamma:real->A)(s1 pow 2)) +
           (inv(s2 - s1) * (drop v - s1)) % (phi(gamma(s2 pow 2)) - phi(gamma(s1 pow 2))))
      s1 s2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN USE_THEN "HRI" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - h1`; `s0 + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`;
                 `(phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))`;
                 `inv(s2 - s1)`; `s1:real`; `s2:real`;
                 `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),rho0)`; `Cg:real`; `Kp:real`]
                P2A_ZPIECE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`s:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "KP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(s1 pow 2))`;
                 `s1:real`; `s2:real`; `Cg:real`; `Kp:real`; `eps:real`; `e / &4`; `e / &8`]
                P2AXS_ZBOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  USE_THEN "INT" (MP_TAC o SPECL [`s1:real`; `s2:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  EXISTS_TAC `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
                    else if tau <= s2 pow 2 then (sig:real->A) tau else gamma tau` THEN
  EXISTS_TAC `P1:real->bool` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ADM1" ACCEPT_TAC;
    MATCH_MP_TAC P2AXS_PC1B_MONO THEN
    EXISTS_TAC `{s:real | s IN B /\ (s <= s1 pow 2 \/ s2 pow 2 < s)}` THEN
    ASM_REWRITE_TAC[FINITE_DELETE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2) /\ ~(b <= s2 pow 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "LEN1" SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AJ_LOC_PATCH THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `OO:A->bool`; `tO1:real`; `tO2:real`;
                          `s1 pow 2`; `s2 pow 2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "HW" (MP_TAC o SPEC `s1:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      USE_THEN "HW" (MP_TAC o SPEC `s2:real`) THEN
      ANTS_TAC THENL [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(tau <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      EXPAND_TAC "sig" THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`s1:real`; `s2:real`; `tau:real`] P2A_SQRT_BETWEEN) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `OO:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]));;


(* Removing all singular corners, none at the end, with location control.  *)

let P2AJ_REMOVE_BAD_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V
     ==> !B. FINITE B
             ==> !(gamma:real->A) P e.
                   p2a_admx V tt x b gamma /\ p2axs_pc1b V tt gamma (&0) b P B /\ &0 < e /\
                   ~(b IN B) /\ p2aj_loc V tt b Q gamma
                   ==> ?gamma1 P1. p2a_admx V tt x b gamma1 /\
                                   p2axs_pc1b V tt gamma1 (&0) b P1 {} /\
                                   gamma1 b = gamma b /\
                                   p2a_L_length V tt gamma1 b <=
                                   p2a_L_length V tt gamma b + e /\
                                   p2aj_loc V tt b Q gamma1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`gamma:real->A`; `P:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `B:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `P:real->bool`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t:real = b) /\ ~(b IN (B:real->bool))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < t /\ t <= b` THENL
   [ALL_TAC;
    USE_THEN "IH" MATCH_MP_TAC THEN EXISTS_TAC `P:real->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AXS_PC1B_MONO THEN EXISTS_TAC `(t:real) INSERT B` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN
   `?gamma1 P1. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b gamma1 /\
                p2axs_pc1b V tt gamma1 (&0) b P1 B /\
                gamma1 b = (gamma:real->A) b /\
                p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e / &2 /\
                p2aj_loc V tt b Q gamma1`
  (X_CHOOSE_THEN `gamma1:real->A` (X_CHOOSE_THEN `P1:real->bool` STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `B:real->bool = (t INSERT B) DELETE t` SUBST1_TAC THENL
     [REWRITE_TAC[DELETE_INSERT] THEN ASM_MESON_TAC[DELETE_NON_ELEMENT]; ALL_TAC] THEN
    MATCH_MP_TAC P2AJ_INT_STEP_LOC THEN EXISTS_TAC `P:real->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`gamma1:real->A`; `P1:real->bool`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma2:real->A` (X_CHOOSE_THEN `P2:real->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`gamma2:real->A`; `P2:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A p2a_admx curve without a singular point at the end is approximated in *)
(* L-length, with the same end point, by p2a_adm1 curves keeping the       *)
(* location property.                                                       *)

let P2AJ_SMOOTHING_X_LOC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A) P B e (Q:real->A->bool).
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_admx V tt x b gamma /\
     p2axs_pc1b V tt gamma (&0) b P B /\ ~(b IN B) /\ &0 < e /\ p2aj_loc V tt b Q gamma
     ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                  p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                  p2aj_loc V tt b Q gamma'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`; `Q:real->A->bool`] P2AJ_REMOVE_BAD_LOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `B:real->bool`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2axs_pc1b]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `P:real->bool`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2AXS_PC1B_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` (X_CHOOSE_THEN `P1:real->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`; `gamma1:real->A`; `e / &2`;
                 `Q:real->A->bool`] P2AJ_SMOOTHING_LOC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AX_ADMX_ADM THEN EXISTS_TAC `P1:real->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Tools for (b1), the end replacement and its cost. *)

(* ------------------------------------------------------------------------- *)
(* Tools for (b1): a point avoiding countably many finite sets of squares,  *)
(* chart balls are open in the slices of a region, the fat boxes as a       *)
(* function of the time, and the location property from box chart balls.  *)
(* ------------------------------------------------------------------------- *)

let P2AJ_AVOID_COUNTABLE = prove
 (`!a b (B:num->real->bool).
     &0 <= a /\ a < b /\ (!n. FINITE(B n))
     ==> ?s. a < s /\ s < b /\ !n. ~(s pow 2 IN B n)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(LABEL_TAC "NEG" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!s. a < s /\ s < b ==> ?n. s pow 2 IN (B:num->real->bool) n` (LABEL_TAC "BAD")
  THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REMOVE_THEN "NEG" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[NOT_FORALL_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lift a`; `lift b`] (CONJUNCT2 UNCOUNTABLE_INTERVAL)) THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC `IMAGE lift (UNIONS {IMAGE sqrt ((B:num->real->bool) n) | n IN (:num)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE THEN MATCH_MP_TAC COUNTABLE_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; LIFT_EQ] THEN EXISTS_TAC `s:real` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; IN_IMAGE] THEN
  USE_THEN "BAD" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC);;

let P2AJ_CHART_BALL_OPEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b'' U (phi:A->real^N) t c rr.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\ a' < t /\ t <= b''
     ==> open_in (p2a_vtop V t) {y | y IN U INTER W /\ dist(phi y,c) < rr}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b'':real`; `t:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b''`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b''`; `(U:A->bool,phi:A->real^N)`]
                MFDD_CHART_CONTINUOUS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b''`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b''`; `(U:A->bool,phi:A->real^N)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{y:A | y IN U INTER W /\ dist((phi:A->real^N) y,c) < rr} =
    W INTER {y | y IN topspace(subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'') U) /\ phi y IN ball(c,rr)}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b''`; `U:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_BALL; SUBSET] THEN
    DISCH_TAC THEN X_GEN_TAC `y:A` THEN
    MP_TAC(ISPECL [`c:real^N`; `(phi:A->real^N) y`] DIST_SYM) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^N)topology` THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL]);;

(* The fat boxes of the boxes j < nb as a function of the time.             *)

let p2aj_kfat = new_definition
 `p2aj_kfat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
            (nb:num) (W:num->A->bool) (A0:num->real) (b:num->real) (eta:real)
            (Fs:num->A->bool) (R:num->A->real) (t:real) =
    {y | ?j. j < nb /\ A0 j + eta / &2 <= t /\ t <= b j /\ y IN p2aj_fat V W b Fs R j}`;;

let P2AJ_KFAT_CBOX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm
     ==> p2a_cbox V (p2aj_kfat V nb W A0 b eta Fs R)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AJ_FAT_CBOX) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; p2aj_kfat]);;

(* The location property for the fat boxes, from chart balls of radius 3R  *)
(* of the box charts at times strictly inside the fat time ranges.         *)

let P2AJ_LOC_BOX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm b0 (c:real->A).
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\
     (!tau. &0 < tau /\ tau <= b0
            ==> ?j k. j < nb /\ k IN Fs j /\ A0 j + eta / &2 < tt - tau /\ tt - tau < b j /\
                      c tau IN FST(chart_at (p2a_vatlas V (b j)) k) INTER W j /\
                      dist(SND(chart_at (p2a_vatlas V (b j)) k) (c tau),
                           SND(chart_at (p2a_vatlas V (b j)) k) k) < &3 * R j k)
     ==> p2aj_loc V tt b0 (\tau y. y IN p2aj_kfat V nb W A0 b eta Fs R (tt - tau)) c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  REWRITE_TAC[p2aj_loc] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `c:real->A`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`] P2AJ_MB_REGION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `j:num`; `k:A`] P2AJ_MB_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{y:A | y IN FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j /\
            dist(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) y,SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k) < &3 * (R:num->A->real) j k}`;
    `tt - (b:num->real) j`; `tt - ((A0:num->real) j + eta / &2)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AJ_CHART_BALL_OPEN THEN
    MAP_EVERY EXISTS_TAC [`(A0:num->real) j`; `(b:num->real) j`] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[p2aj_kfat; IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2aj_fat; IN_ELIM_THM] THEN EXISTS_TAC `k:A` THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]);;

(* Replacing the last piece [s1^2,s0^2] of a p2a_admx curve by a chart curve *)
(* in a region chart (strict window), with a new end point.                 *)

let P2AJ_END_REPLACE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) b (g:real->A) W a' b'' U (phi:A->real^N) (Y:real^1->real^N) s1 s0 sa sb P.
     p2a_svs V /\ p2a_admx V tt x b g /\ p2a_pc1x V tt g (&0) b P /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s0 /\ s0 pow 2 = b /\ sa < s1 /\ s0 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     g(s1 pow 2) IN U INTER W /\ Y(lift s1) = phi(g(s1 pow 2)) /\ ~(s1 pow 2 IN P) /\
     (!s. s1 <= s /\ s <= s0
          ==> Y(lift s) IN IMAGE phi (U INTER W) /\ Y differentiable (at (lift s)) /\
              (\v. vector_derivative Y (at v)) continuous (at (lift s)))
     ==> ?P'. p2a_admx V tt x b
                (\tau. if tau <= s1 pow 2 then g tau
                       else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) /\
              p2axs_pc1b V tt
                (\tau. if tau <= s1 pow 2 then g tau
                       else chart_inv (U INTER W,phi) (Y(lift(sqrt tau))))
                (&0) b P' {s | s IN P /\ s <= s1 pow 2} /\
              p2a_L_length V tt
                (\tau. if tau <= s1 pow 2 then g tau
                       else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b =
              p2a_L_length V tt g b -
              real_integral (real_interval[s1 pow 2,b]) (p2a_L_integrand V tt g b) +
              p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt Y s1 s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `s0 pow 2 = b`)) THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 < s0 pow 2 /\ a' < b''` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `Y:real^1->real^N`; `s1:real`; `s0:real`; `sa:real`;
                 `sb:real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt(s1 pow 2)))) =
                (g:real->A)(s1 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b'':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x (s1 pow 2) (g:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AXR_ADMX_RESTRICT THEN EXISTS_TAC `s0 pow 2` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau)))`;
                 `g:real->A`;
                 `\tau. if tau <= s1 pow 2 then (g:real->A) tau
                        else chart_inv (U INTER W,phi:A->real^N)
                                       ((Y:real^1->real^N)(lift(sqrt tau)))`;
                 `s0 pow 2`; `s1 pow 2`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `tau:real` THEN
    DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `g:real->A`; `s0 pow 2`; `s1 pow 2`]
                P2AXR_LENGTH_SPLIT_X) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `g:real->A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau)))`;
                 `s0 pow 2`; `s1 pow 2`; `P:real->bool`; `P:real->bool`] P2AXS_ENDREP_PC1B) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[P2AXS_PC1X_PC1B]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `P':real->bool`) THEN EXISTS_TAC `P':real->bool` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* (b1), one box: replacing the last piece of a late curve of a converging  *)
(* sequence by the BVP solution to the end point of the limit costs at most *)
(* ep in L-length (BVP minimality against the curve and continuity of the  *)
(* BVP length in the end points).                                           *)

let P2AJ_B1_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' b' C T1 Fs R r lam Gm Rm tt (x:A) b (g:num->real->A) Lb Rm0 (gamma:real->A)
    (Pf:num->real->bool) sA sB sa sb s1 s0 k N0 Eb delta rho
    (sol:real->real->real^N->real^N->real^1->real^N) ep.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     &0 <= Lb /\ &0 <= Rm0 /\ Rm <= Rm0 /\
     (!n. p2a_admx V tt x b (g n) /\ p2a_L_length V tt (g n) b <= Lb /\
          (!tau. &0 <= tau /\ tau <= b
                 ==> --(sqrt tau * Rm0) <= p2a_L_integrand V tt (g n) b tau) /\
          p2a_pc1x V tt (g n) (&0) b (Pf n) /\ ~(s1 pow 2 IN Pf n)) /\
     &0 < sA /\ sA <= s1 /\ s1 < s0 /\ s0 <= sB /\ s0 pow 2 = b /\ k IN Fs /\
     sa < sA /\ sB < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b') /\
     (!s. sA <= s /\ s <= sB ==> b' - T1 <= tt - s pow 2) /\
     (!n s. N0 <= n /\ s1 <= s /\ s <= s0
            ==> g n (s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
                dist(SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k) /\
     (!n s s'. N0 <= n /\ s1 <= s /\ s <= s' /\ s' <= s0
               ==> dist(SND (chart_at (p2a_vatlas V b') k) (g n (s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) pow 2
                   <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     (!s. s1 <= s /\ s <= s0
          ==> gamma(s pow 2) IN FST (chart_at (p2a_vatlas V b') k) INTER W /\
              dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2)),SND (chart_at (p2a_vatlas V b') k) k) <= &2 * R k /\
              ((\n. SND (chart_at (p2a_vatlas V b') k) (g n (s pow 2))) --> SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) sequentially) /\
     (!s s'. s1 <= s /\ s <= s' /\ s' <= s0
             ==> dist(SND (chart_at (p2a_vatlas V b') k) (gamma(s' pow 2)),SND (chart_at (p2a_vatlas V b') k) (gamma(s pow 2))) pow 2
                 <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0))) /\
     p2ak_bvpd (ball(SND (chart_at (p2a_vatlas V b') k) k,&3 * R k)) (p2a_rlocal V W b' (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))) tt
               (cball(SND (chart_at (p2a_vatlas V b') k) k,&2 * R k)) Eb sA sB delta rho sol /\
     s0 - s1 <= delta /\
     (s0 - s1) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm0)) <= (rho / &4) pow 2 /\
     &2 / lam * (Lb + &4 * b * sqrt b * Rm0) <= Eb /\ &0 < ep
     ==> ?N. !n. N <= n
             ==> ?P'. p2a_admx V tt x b
                        (\tau. if tau <= s1 pow 2 then g n tau
                               else chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                                      (sol s1 s0 (SND (chart_at (p2a_vatlas V b') k) (g n (s1 pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma b))
                                           (lift(sqrt tau)))) /\
                      p2axs_pc1b V tt
                        (\tau. if tau <= s1 pow 2 then g n tau
                               else chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                                      (sol s1 s0 (SND (chart_at (p2a_vatlas V b') k) (g n (s1 pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma b))
                                           (lift(sqrt tau))))
                        (&0) b P' {s | s IN Pf n /\ s <= s1 pow 2} /\
                      chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                        (sol s1 s0 (SND (chart_at (p2a_vatlas V b') k) (g n (s1 pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma b)) (lift s0)) =
                      gamma b /\
                      p2a_L_length V tt
                        (\tau. if tau <= s1 pow 2 then g n tau
                               else chart_inv (FST (chart_at (p2a_vatlas V b') k) INTER W,SND (chart_at (p2a_vatlas V b') k))
                                      (sol s1 s0 (SND (chart_at (p2a_vatlas V b') k) (g n (s1 pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma b))
                                           (lift(sqrt tau)))) b
                      <= p2a_L_length V tt (g n) b + ep /\
                      (!s. s1 <= s /\ s <= s0
                           ==> sol s1 s0 (SND (chart_at (p2a_vatlas V b') k) (g n (s1 pow 2))) (SND (chart_at (p2a_vatlas V b') k) (gamma b)) (lift s)
                               IN ball(SND (chart_at (p2a_vatlas V b') k) k,&3 * R k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm0)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ &0 < s1 /\ &0 < (R:A->real) k /\ a' < b' /\ sa < s1 /\ s0 < sb`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s0 pow 2 = b`)) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bvpd]) THEN
  FIRST_X_ASSUM(LABEL_TAC "C" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `s1n:num->real`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "B" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  (* the limit end points *)
  SUBGOAL_THEN
   `(gamma:real->A) b IN U INTER W /\
    (phi:A->real^N)(gamma b) IN cball(phi k,&2 * (R:A->real) k) /\
    phi(gamma(s1 pow 2)) IN cball(phi k,&2 * R k) /\
    norm(phi(gamma b) - phi(gamma(s1 pow 2))) <= rho / &4 /\
    ((\n. phi((g:num->real->A) n (s1 pow 2))) --> phi(gamma(s1 pow 2))) sequentially /\
    ((\n. phi((g:num->real->A) n b)) --> phi(gamma b)) sequentially`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `s0 pow 2 = b`)) THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s1:real`; `s0:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      not(can (find_term ((=) `g:num->real->A`)) (concl th)) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `s0 pow 2 = b`)) THEN
    REWRITE_TAC[dist] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s0 - s1) * E` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `y2 = (phi:A->real^N)((gamma:real->A) b)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (* late curves start close to the limit *)
  SUBGOAL_THEN
   `?N1. N0 <= N1 /\
         !n. N1 <= n ==> norm((phi:A->real^N)((g:num->real->A) n (s1 pow 2)) -
                              phi((gamma:real->A)(s1 pow 2))) < rho / &4`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `rho / &4` o REWRITE_RULE[LIM_SEQUENTIALLY] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th) &&
      can (find_term ((=) `s1 pow 2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N0 + N2:num` THEN
    REWRITE_TAC[LE_ADD] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the BVP data of the late curves *)
  SUBGOAL_THEN
   `!n. N1 <= n
        ==> (phi:A->real^N)((g:num->real->A) n (s1 pow 2)) IN cball(phi k,&2 * (R:A->real) k) /\
            norm(y2 - phi(g n (s1 pow 2))) <= rho /\
            norm(phi(g n b) - phi(g n (s1 pow 2))) <= rho /\
            (g:num->real->A) n (s1 pow 2) IN U INTER W`
  (LABEL_TAC "DN") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `s1:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `s1:real`; `s0:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `s0 pow 2 = b`)) THEN
    REWRITE_TAC[dist] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(NORM_ARITH `!y2 z d w r. norm(y2 - z:real^N) <= d /\ norm(w - z) < d /\
                                            &2 * d <= r ==> norm(y2 - w) <= r`) THEN
      MAP_EVERY EXISTS_TAC [`(phi:A->real^N)((gamma:real->A)(s1 pow 2))`; `rho / &4`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s0 - s1) * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &4) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* n-independent facts *)
  SUBGOAL_THEN
   `(!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
    (!s. s1 <= s /\ s <= s0 ==> b' - T1 <= tt - s pow 2) /\
    ball((phi:A->real^N) k,&3 * (R:A->real) k) SUBSET IMAGE phi (U INTER W) /\
    p2a_lsmooth (ball((phi:A->real^N) k,&3 * (R:A->real) k)) sa sb
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball((phi:A->real^N) k,&3 * (R:A->real) k) SUBSET IMAGE phi (U INTER W)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball((phi:A->real^N) k,&3 * (R:A->real) k)` THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `sB:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the late curves: shifted data *)
  SUBGOAL_THEN
   `(!m. (phi:A->real^N)((g:num->real->A) (m + N1) (s1 pow 2)) IN
         cball(phi k,&2 * (R:A->real) k) /\
         norm(y2 - phi(g (m + N1) (s1 pow 2))) <= rho /\
         norm(phi(g (m + N1) b) - phi(g (m + N1) (s1 pow 2))) <= rho) /\
    ((\m. (phi:A->real^N)((g:num->real->A) (m + N1) (s1 pow 2))) -->
     phi((gamma:real->A)(s1 pow 2))) sequentially /\
    ((\m. (phi:A->real^N)((g:num->real->A) (m + N1) b)) --> y2) sequentially /\
    norm(y2 - (phi:A->real^N)((gamma:real->A)(s1 pow 2))) <= rho`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN USE_THEN "DN" (MP_TAC o SPEC `m + N1:num`) THEN
      ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]];
      MP_TAC(ISPECL [`\n. (phi:A->real^N)((g:num->real->A) n (s1 pow 2))`;
                     `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`; `N1:num`] SEQ_OFFSET) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. (phi:A->real^N)((g:num->real->A) n b)`; `y2:real^N`; `N1:num`]
                    SEQ_OFFSET) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of the BVP length in the end points *)
  SUBGOAL_THEN
   `?M. !m. M <= m
            ==> p2a_cL (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)) tt
                  ((sol:real->real->real^N->real^N->real^1->real^N) s1 s0
                     (phi((g:num->real->A) (m + N1) (s1 pow 2))) y2) s1 s0
                <= p2a_cL (p2a_rlocal V W b' (U INTER W,phi)) tt
                     (sol s1 s0 (phi(g (m + N1) (s1 pow 2))) (phi(g (m + N1) b))) s1 s0 + ep`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "C" (MP_TAC o SPECL
      [`s1:real`; `s0:real`; `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`; `y2:real^N`;
       `\m:num. (s1:real)`; `\m:num. (s0:real)`;
       `\m. (phi:A->real^N)((g:num->real->A) (m + N1) (s1 pow 2))`; `\m:num. (y2:real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
    USE_THEN "C" (MP_TAC o SPECL
      [`s1:real`; `s0:real`; `(phi:A->real^N)((gamma:real->A)(s1 pow 2))`; `y2:real^N`;
       `\m:num. (s1:real)`; `\m:num. (s0:real)`;
       `\m. (phi:A->real^N)((g:num->real->A) (m + N1) (s1 pow 2))`;
       `\m. (phi:A->real^N)((g:num->real->A) (m + N1) b)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `ep / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `M2:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `ep / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
    EXISTS_TAC `M1 + M2:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M1:num`)) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `M1 + M2 <= m:num` THEN ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M2:num`)) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `M1 + M2 <= m:num` THEN ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) y2 = (gamma:real->A) b` ASSUME_TAC THENL
   [EXPAND_TAC "y2" THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a late curve *)
  EXISTS_TAC `M + N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 <= n:num /\ N0 <= n:num /\ M <= n - N1:num /\ (n - N1) + N1 = n:num`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `M + N1 <= n:num` THEN UNDISCH_TAC `N0 <= N1:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "DN" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - N1:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `M:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "B" (MP_TAC o SPECL [`s1:real`; `s0:real`;
    `(phi:A->real^N)((g:num->real->A) n (s1 pow 2))`; `y2:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s0
                    ==> (g:num->real->A) n (s pow 2) IN U INTER W /\
                        (phi:A->real^N)(g n (s pow 2)) IN cball(phi k,&6 * (R:A->real) k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`; `T1:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `Lb:real`; `Rm0:real`;
                 `k:A`; `s1:real`; `s0:real`; `sa:real`; `sb:real`] P2AJ_BXD_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2ak_sq (ball((phi:A->real^N) k,&3 * (R:A->real) k)) s1 s0
                  (\v. phi((g:num->real->A) n (drop v pow 2)))
                  (\v. vector_derivative (\v. phi(g n (drop v pow 2))) (at v))
                  K (K INTER real_interval[s1,s0])` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_SQ_MONO THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_BALL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball((phi:A->real^N) k,&3 * (R:A->real) k)`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`; `tt:real`;
                 `cball((phi:A->real^N) k,&2 * (R:A->real) k)`; `Eb:real`; `sA:real`; `sB:real`;
                 `delta:real`; `rho:real`; `sol:real->real->real^N->real^N->real^1->real^N`;
                 `sa:real`; `sb:real`; `s1:real`; `s0:real`;
                 `\v:real^1. (phi:A->real^N)((g:num->real->A) n (drop v pow 2))`;
                 `\v. vector_derivative
                        (\v:real^1. (phi:A->real^N)((g:num->real->A) n (drop v pow 2)))
                        (at v)`;
                 `K:real->bool`; `(K:real->bool) INTER real_interval[s1,s0]`] P2AK_BVPD_LE) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `b:real`; `(g:num->real->A) n`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `(sol:real->real->real^N->real^N->real^1->real^N) s1 s0
                    (phi((g:num->real->A) n (s1 pow 2))) y2`;
                 `s1:real`; `s0:real`; `sa:real`; `sb:real`; `(Pf:num->real->bool) n`]
                P2AJ_END_REPLACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      can (find_term ((=) `y2:real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `y2:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                  MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE)];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P':real->bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Clause (b1) for a subsequence with converging L-lengths. *)

(* (b1) for a subsequence with converging L-lengths: a p2a_adm1 curve to the *)
(* end point of the limit, in the fat boxes, of L-length at most the        *)
(* lengths of the late curves plus ep (a late curve with its last piece     *)
(* replaced by a BVP solution, then smoothed with location control).        *)

let P2AJ_B1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (gs:num->real->A) Lb tau0 sub gamma
    Lstar ep.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 <= Lb /\ &0 < tau0 /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
          !tau. &0 < tau /\ tau <= tau0
                ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ gs n tau IN C j) /\
     p3_subseq sub /\ gamma (&0) = x /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
     (!e. &0 < e
          ==> ?N. !n. N <= n ==> abs(p2a_L_length V tt (gs (sub n)) tau0 - Lstar) < e) /\
     &0 < ep
     ==> ?gamma'. p2a_adm1 V tt x tau0 gamma' /\ gamma' tau0 = gamma tau0 /\
                  (!tau. &0 < tau /\ tau <= tau0
                         ==> gamma' tau IN p2aj_kfat V nb W A0 b eta Fs R (tt - tau)) /\
                  ?N. !n. N <= n
                          ==> p2a_L_length V tt gamma' tau0 <=
                              p2a_L_length V tt (gs (sub n)) tau0 + ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau0` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sqrt tau0` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the end box and its chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `Lb:real`; `tau0:real`; `sub:num->num`;
                 `gamma:real->A`; `s0:real`] P2AJ_LOCAL_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `sa:real`
    (X_CHOOSE_THEN `sb:real` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
    not(is_forall(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `?sA sB. sa < sA /\ sA < s0 /\ s0 < sB /\ sB < sb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(sa + s0) / &2`; `(s0 + sb) / &2`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. sa < s /\ s < sb ==> (A0:num->real) j < tt - s pow 2 /\ tt - s pow 2 < (b:num->real) j) /\
    (!s. sa < s /\ s < sb ==> A0 j < tt - s pow 2 /\ tt - s pow 2 <= b j) /\
    (!s. sA <= s /\ s <= sB ==> b j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2) /\
    (!s. sa < s /\ s < sb ==> A0 j + eta / &2 < tt - s pow 2)`
  (CONJUNCTS_THEN2 (LABEL_TAC "WS") (CONJUNCTS_THEN2 (LABEL_TAC "WL")
    (CONJUNCTS_THEN2 (LABEL_TAC "T1W") (LABEL_TAC "WE")))) THENL
   [REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th) && can (find_term ((=) `eta:real`)) (concl th))) THEN
    ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) /\ &0 < (R:num->A->real) j k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* BVP data on the ball of radius 3R *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`; `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`] P2A_REGION_LRICCI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR]; STRIP_TAC] THEN
  SUBGOAL_THEN `ball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&3 * (R:num->A->real) j k) SUBSET
                IMAGE (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))) (FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&6 * (R:num->A->real) j k)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&3 * (R:num->A->real) j k)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&3 * (R:num->A->real) j k)`; `(A0:num->real) j`;
                 `(b:num->real) j`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((W:num->A->bool) j) ((b:num->real) j)
                    (FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER W j,SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)))`;
                 `tt:real`; `cball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&2 * (R:num->A->real) j k)`; `(&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1`;
                 `sA:real`; `sB:real`] P2AK_BVPD_EXISTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))) (FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC P2AK_LRICCI_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))) (FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "WS" (MP_TAC o SPEC `sB:real`) THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "WS" (MP_TAC o SPEC `sA:real`) THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (X_CHOOSE_THEN `rho:real`
      (X_CHOOSE_THEN `sol:real->real->real^N->real^N->real^1->real^N` ASSUME_TAC)))] THEN
  SUBGOAL_THEN `&0 < delta /\ &0 < rho` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bvpd")) (concl th))) THEN
    REWRITE_TAC[p2ak_bvpd] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the singular points of the curves *)
  SUBGOAL_THEN `?Pf. !n. p2a_pc1x (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) n) (&0) tau0 (Pf n)`
  (X_CHOOSE_TAC `Pf:num->real->bool`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    REWRITE_TAC[p2a_admx] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the start of the last piece *)
  MP_TAC(SPECL [`r1:real`; `s0 - sA`; `delta:real`; `delta:real`; `(rho / &4) pow 2`;
                `r pow 2`; `(&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm))`] P2AJ_RR_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `rr:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`s0 - rr`; `s0:real`; `\n. (Pf:num->real->bool) ((sub:num->num) n)`]
                P2AJ_AVOID_COUNTABLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN ASM_MESON_TAC[p2a_pc1x]];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `&0 < s1 /\ sA < s1 /\ sA <= s1 /\ sa < s1 /\ s0 <= sB /\ s0 < sb /\ s1 pow 2 <= tau0 /\
    abs(s1 - s0) < r1 /\ s0 - s1 <= delta /\
    (s0 - s1) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= (rho / &4) pow 2 /\ (s0 - s1) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= r pow 2 /\ &0 <= s1 /\
    s1 pow 2 < tau0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(s0 - s1) * (&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) <= &2 * rr * ((&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * rr) * ((&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `s1 pow 2 < s0 pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the facts on the subsequence *)
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 ((gs:num->real->A) ((sub:num->num) n)) /\
        p2a_L_length V tt (gs (sub n)) tau0 <= Lb /\
        (!tau. &0 <= tau /\ tau <= tau0
               ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt (gs (sub n)) tau0 tau) /\
        p2a_pc1x V tt (gs (sub n)) (&0) tau0 ((Pf:num->real->bool) (sub n)) /\
        ~(s1 pow 2 IN Pf (sub n))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
      can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(sub:num->num) n`)) (concl th) &&
      can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s0
        ==> (gamma:real->A)(s pow 2) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)) /\
            !O. open_in (p2a_vtop V (tt - s pow 2)) O /\ gamma(s pow 2) IN O
                ==> ?N. !n. N <= n ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN O`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s0 pow 2 = tau0`)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(gamma:real->A)(s1 pow 2) IN FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j /\
    dist(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) (gamma(s1 pow 2)),SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k) < (R:num->A->real) j k`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r1:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s0 ==> (b:num->real) j - (b j - (a:num->real) j + eta / &2) <= tt - s pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "T1W" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`; `gs:num->real->A`; `Lb:real`;
                 `Rm:real`; `sub:num->num`; `gamma:real->A`; `k:A`; `s1:real`; `s0:real`;
                 `sa:real`; `sb:real`] P2AJ_BOX_PIECE_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                 `(C:num->A->bool) j`; `(b:num->real) j - (a:num->real) j + eta / &2`;
                 `(Fs:num->A->bool) j`; `(R:num->A->real) j`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `tt:real`; `x:A`; `tau0:real`;
                 `\n. (gs:num->real->A) ((sub:num->num) n)`; `Lb:real`; `Rm:real`;
                 `gamma:real->A`; `\n. (Pf:num->real->bool) ((sub:num->num) n)`;
                 `sA:real`; `sB:real`; `sa:real`; `sb:real`; `s1:real`; `s0:real`; `k:A`;
                 `N0:num`; `(&2 / lam * (Lb + &4 * tau0 * sqrt tau0 * Rm)) + &1`; `delta:real`; `rho:real`;
                 `sol:real->real->real^N->real^N->real^1->real^N`; `ep / &4`] P2AJ_B1_PIECE) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "B1P"))] THEN
  (* a late curve with converged length *)
  FIRST_X_ASSUM(MP_TAC o SPEC `ep / &4` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lstar:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `NL:num`)] THEN
  USE_THEN "B1P" (MP_TAC o SPEC `N2 + NL:num`) THEN REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':real->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `c = \tau. if tau <= s1 pow 2 then (gs:num->real->A) ((sub:num->num) (N2 + NL)) tau
              else chart_inv (FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) INTER (W:num->A->bool) j,SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)))
                     ((sol:real->real->real^N->real^N->real^1->real^N) s1 s0
                        (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) (gs (sub (N2 + NL)) (s1 pow 2)))
                        (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A) tau0)) (lift(sqrt tau)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (* the location property of the modified curve *)
  SUBGOAL_THEN
   `p2aj_loc (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt tau0
      (\tau y. y IN p2aj_kfat V nb W A0 b eta Fs R (tt - tau)) (c:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AJ_LOC_BOX THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a:num->real`; `C:num->A->bool`; `r:real`; `lam:real`;
                          `Gm:real`; `Rm:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) (N2 + NL)` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th) &&
        can (find_term ((=) `C:num->A->bool`)) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < nb:num` THEN ARITH_TAC; STRIP_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bxd] o check (fun th ->
        not(is_forall(concl th)) &&
        can (find_term ((=) `(C:num->A->bool) i`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(gs:num->real->A) ((sub:num->num) (N2 + NL)) tau` o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
          can (find_term ((=) `(C:num->A->bool) i`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `k':A` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k':A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th) &&
        can (find_term ((=) `(Fs:num->A->bool) i`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `k':A`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `k:A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`s1:real`; `s0:real`; `tau:real`] P2A_SQRT_BETWEEN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th) &&
      can (find_term ((=) `sol:real->real->real^N->real^N->real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `(W:num->A->bool) j`; `(A0:num->real) j`; `(b:num->real) j`;
                   `FST (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`; `SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A))`;
                   `(sol:real->real->real^N->real^N->real^1->real^N) s1 s0
                      (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gs:num->real->A) ((sub:num->num) (N2 + NL)) (s1 pow 2)))
                      (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A) tau0)) (lift(sqrt tau))`]
                  P2A_CHART_PIECE_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PAIR] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(sol:real->real->real^N->real^N->real^1->real^N) s1 s0
                   (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gs:num->real->A) ((sub:num->num) (N2 + NL)) (s1 pow 2)))
                   (SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) ((gamma:real->A) tau0)) (lift(sqrt tau)) IN
                 ball(SND (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) ((b:num->real) j)) (k:A)) k,&3 * (R:num->A->real) j k)` THEN
    REWRITE_TAC[IN_BALL] THEN DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[DIST_SYM]) THEN
    CONJ_TAC THENL
     [USE_THEN "WE" (MP_TAC o SPEC `sqrt tau`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "WS" (MP_TAC o SPEC `sqrt tau`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the end point of the modified curve *)
  SUBGOAL_THEN `(c:real->A) tau0 = (gamma:real->A) tau0` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(tau0 <= s1 pow 2) /\ sqrt tau0 = s0` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s0 pow 2 = tau0`)) THEN
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* smoothing with location control *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `tau0:real`; `c:real->A`; `P':real->bool`;
                 `{s | s IN (Pf:num->real->bool) ((sub:num->num) (N2 + NL)) /\ s <= s1 pow 2}`;
                 `ep / &4`; `\tau (y:A). y IN p2aj_kfat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) nb W A0 b eta Fs R (tt - tau)`]
                P2AJ_SMOOTHING_X_LOC) THEN
  SUBGOAL_THEN `~(tau0 <= s1 pow 2) /\ &0 < ep / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2AJ_LOC_Q o check (fun th ->
      can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aj_loc")) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `NL:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `NL:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `N2 + NL:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `NL:num`)) (concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Assembly of MT Lemma 7.2 in the view-X form. *)

(* ------------------------------------------------------------------------- *)
(* Assembly of MT Lemma 7.2 in the view-X form: the multi-box datum from the *)
(* cbox, the subsequence (refined so that the L-lengths converge), the     *)
(* clauses (a), (b1), (b2), and (c) with the infimum over adm curves.       *)
(* ------------------------------------------------------------------------- *)

let P2AJ_RFS_P2A = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     rfs_vtop V = p2a_vtop V /\ rfs_vatlas V = p2a_vatlas V /\ rfs_vmetric V = p2a_vmetric V`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vtop; rfs_vatlas; rfs_vmetric; p2a_vtop; p2a_vatlas;
              p2a_vmetric]);;

(* Further subsequences keep the slice limit.                                *)

let P2AJ_SUBSEQ_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gs:num->real->A) tau0 sub gamma rr.
     p3_subseq sub /\ p3_subseq rr /\
     (!tau. &0 <= tau /\ tau <= tau0
            ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                    ==> ?N. !n. N <= n ==> gs (sub n) tau IN O)
     ==> p3_subseq (sub o rr) /\
         (!tau. &0 <= tau /\ tau <= tau0
                ==> gamma tau IN topspace(p2a_vtop V (tt - tau)) /\
                    !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                        ==> ?N. !n. N <= n ==> gs ((sub o rr) n) tau IN O)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_subseq; o_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPEC `rr:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `N <= n:num` THEN ARITH_TAC);;

(* A lower bound of the L-length of the curves in the boxes.                 *)

let P2AJ_MB_L_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) nb W A0 a b C eta Fs R r lam Gm Rm (g:real->A) tau0.
     p2aj_mb V tt x nb W A0 a b C eta Fs R r lam Gm Rm /\ &0 < tau0 /\
     p2a_admx V tt x tau0 g /\
     (!tau. &0 < tau /\ tau <= tau0
            ==> ?j. j < nb /\ a j <= tt - tau /\ tt - tau < b j /\ g tau IN C j)
     ==> --(sqrt tau0 * Rm) * tau0 <= p2a_L_length V tt g tau0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL [`&0`; `tau0:real`; `--(sqrt tau0 * Rm)`] REAL_INTEGRAL_CONST) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,tau0]) (\t:real. --(sqrt tau0 * Rm))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[p2a_admx]; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_MONO_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AJ_MB_LINT_LOWER THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                        `b:num->real`; `C:num->A->bool`; `eta:real`; `Fs:num->A->bool`;
                        `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `C:num->A->bool`)) (concl th) &&
    can (find_term ((=) `g:real->A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_IMP_LE]);;

(* A bounded real sequence has a converging subsequence.                     *)

let P2AJ_L_CONV_SUBSEQ = prove
 (`!(f:num->real) lo hi.
     (!n. lo <= f n /\ f n <= hi)
     ==> ?rr l. p3_subseq rr /\
                !e. &0 < e ==> ?N. !n. N <= n ==> abs(f(rr n) - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift lo`; `lift hi`] COMPACT_INTERVAL) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. lift((f:num->real) n)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `rr:num->num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`rr:num->num`; `drop l`] THEN ASM_REWRITE_TAC[p3_subseq] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "-->")) (concl th))) THEN
  REWRITE_TAC[o_THM; DIST_REAL; GSYM drop; LIFT_DROP] THEN SIMP_TAC[]);;

(* The infimum of the L-lengths of adm curves to q, for a sequence of admx  *)
(* curves that is minimizing against adm curves (P2AXS_SMOOTHING_X: the    *)
(* infimum over admx curves is the same).                                    *)

let P2AJ_LAM_EXISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (x:A) tau0 (gs:num->real->A) q lo sub.
     p2a_svs V /\ p2a_atlas_lc V /\ p3_subseq sub /\
     (!n. p2a_admx V tt x tau0 (gs n) /\ gs n tau0 = q /\
          lo <= p2a_L_length V tt (gs n) tau0) /\
     (!gamma' eta. p2a_adm V tt x tau0 gamma' /\ gamma' tau0 = q /\ &0 < eta
                   ==> ?N. !n. N <= n
                           ==> p2a_L_length V tt (gs n) tau0 <=
                               p2a_L_length V tt gamma' tau0 + eta)
     ==> ?Lam. (!e. &0 < e
                    ==> ?N. !n. N <= n ==> p2a_L_length V tt (gs (sub n)) tau0 <= Lam + e) /\
               (!gamma'. p2a_admx V tt x tau0 gamma' /\ gamma' tau0 = q
                         ==> Lam <= p2a_L_length V tt gamma' tau0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GS") (LABEL_TAC "MIN"))))) THEN
  ABBREV_TAC
   `S = {p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt g tau0 | g | p2a_adm V tt (x:A) tau0 g /\ g tau0 = q}` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!y. y IN S ==> lo - &1 <= y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `tau0:real`; `(gs:num->real->A) 0`; `&1`]
                    P2AXS_SMOOTHING_X) THEN
      ANTS_TAC THENL [USE_THEN "GS" (MP_TAC o SPEC `0`) THEN ASM_SIMP_TAC[REAL_LT_01]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) tau0` THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real->A` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[p2a_adm1]; ALL_TAC] THEN
      USE_THEN "GS" (MP_TAC o SPEC `0`) THEN ASM_SIMP_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
      USE_THEN "MIN" (MP_TAC o SPECL [`g:real->A`; `&1`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
      USE_THEN "GS" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `N:num`) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN S ==> inf S <= y` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real->bool` INF) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `lo - &1` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `inf (S:real->bool)` THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real->bool`; `inf (S:real->bool) + e / &2`] INF_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `lo - &1` THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?g:real->A. p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 g /\ g tau0 = q /\
                              p2a_L_length V tt g tau0 < inf S + e / &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real) IN S` THEN UNDISCH_TAC `y < inf S + e / &2` THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "MIN" (MP_TAC o SPECL [`g:real->A`; `e / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N:num`)) (concl th))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `p3_subseq sub` THEN REWRITE_TAC[p3_subseq] THEN
      DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP MONOTONE_BIGGER) THEN
      UNDISCH_TAC `N <= n:num` THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `gamma':real->A` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AK_LE_ADD_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `tau0:real`; `gamma':real->A`; `e:real`]
                  P2AXS_SMOOTHING_X) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) tau0` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real->A` THEN
    ASM_MESON_TAC[p2a_adm1]]);;

(* MT Lemma 7.2 in the view-X form, for any dimension (a), (b1), (b2), (c). *)

let P2AJ_LEMMA_7_2_VIEW_X_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (x:A) tt tau0 K (gs:num->real->A) Lb.
     p2a_svs V /\ p2a_atlas_lc V /\
     &0 < tau0 /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
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
                                      ==> mfd_dist (p2a_vtop V (tt - tau),
                                                    p2a_vatlas V (tt - tau))
                                                   (p2a_vmetric V (tt - tau))
                                                   (gs (sub n) tau) (gamma tau) < eta)) /\
            !q. (!n. gs n tau0 = q) /\
                (!gamma' eta. p2a_adm V tt x tau0 gamma' /\ gamma' tau0 = q /\ &0 < eta
                              ==> ?N. !n. N <= n
                                      ==> p2a_L_length V tt (gs n) tau0 <=
                                          p2a_L_length V tt gamma' tau0 + eta)
                ==> p2a_min V tt x tau0 gamma /\ p2a_pc1 V tt gamma (&0) tau0 {} /\
                    gamma tau0 = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `K:real->A->bool`] P2AJ_MB_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nb:num` (X_CHOOSE_THEN `W:num->A->bool` (X_CHOOSE_THEN `A0:num->real`
    (X_CHOOSE_THEN `a:num->real` (X_CHOOSE_THEN `b:num->real` (X_CHOOSE_THEN `C:num->A->bool`
    (X_CHOOSE_THEN `eta0:real` (X_CHOOSE_THEN `Fs:num->A->bool` (X_CHOOSE_THEN `R:num->A->real`
    (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Gm:real`
    (X_CHOOSE_THEN `Rm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KC"))))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2aj_mb]) THEN
  (* the strict cover of the curves *)
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 ((gs:num->real->A) n) /\
        p2a_L_length V tt (gs n) tau0 <= max Lb (&0) /\
        !tau. &0 < tau /\ tau <= tau0
              ==> ?j. j < nb /\ (a:num->real) j <= tt - tau /\ tt - tau < (b:num->real) j /\
                      gs n tau IN (C:num->A->bool) j`
  (LABEL_TAC "GSH") THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K:real->A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_admx")) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2AJ_STRICT_TOP THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tau0:real`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x tau0 ((gs:num->real->A) n)` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < nb:num` THEN ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "KC" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K:real->A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the limit, along a subsequence with converging L-lengths *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                 `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta0:real`;
                 `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                 `Rm:real`; `gs:num->real->A`; `max Lb (&0)`; `tau0:real`] P2AJ_MB_LIMIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub0:num->num` (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. --(sqrt tau0 * Rm) * tau0 <= p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) n) tau0`
  (LABEL_TAC "LLOW") THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC P2AJ_MB_L_LOWER THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`; `a:num->real`;
                          `b:num->real`; `C:num->A->bool`; `eta0:real`; `Fs:num->A->bool`;
                          `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    USE_THEN "GSH" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub0:num->num) n)) tau0`;
                 `--(sqrt tau0 * Rm) * tau0`; `max Lb (&0)`] P2AJ_L_CONV_SUBSEQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    USE_THEN "LLOW" (MP_TAC o SPEC `(sub0:num->num) n`) THEN
    USE_THEN "GSH" (MP_TAC o SPEC `(sub0:num->num) n`) THEN REAL_ARITH_TAC;
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `rr:num->num` (X_CHOOSE_THEN `Lstar:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `gs:num->real->A`; `tau0:real`; `sub0:num->num`;
                 `gamma:real->A`; `rr:num->num`] P2AJ_SUBSEQ_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `sub = (sub0:num->num) o (rr:num->num)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?N. !n. N <= n
                       ==> abs(p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) n)) tau0 -
                               Lstar) < e`
  ASSUME_TAC THENL
   [EXPAND_TAC "sub" THEN REWRITE_TAC[o_THM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `sub:num->num` THEN EXISTS_TAC `gamma:real->A` THEN
  EXISTS_TAC `p2aj_kfat (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) nb W A0 b eta0 Fs R` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* (a) *)
    MATCH_MP_TAC P2AJ_KFAT_CBOX THEN
    MAP_EVERY EXISTS_TAC [`tt:real`; `x:A`; `a:num->real`; `C:num->A->bool`; `r:real`;
                          `lam:real`; `Gm:real`; `Rm:real`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta0:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `gs:num->real->A`; `max Lb (&0)`; `tau0:real`; `sub:num->num`;
                   `gamma:real->A`; `tau:real`] P2AJ_LIM_STRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta0:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `j:num`; `(b:num->real) j`] P2AJ_FAT_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
      STRIP_TAC] THEN
    REWRITE_TAC[p2aj_kfat; IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bxd")) (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < nb:num` THEN ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    (* (b1) and (b2) *)
    X_GEN_TAC `ep:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AJ_B1 THEN
      MAP_EVERY EXISTS_TAC [`a:num->real`; `C:num->A->bool`; `r:real`; `lam:real`; `Gm:real`;
                            `Rm:real`; `max Lb (&0)`; `Lstar:real`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                     `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta0:real`;
                     `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                     `Rm:real`; `gs:num->real->A`; `max Lb (&0)`; `tau0:real`; `sub:num->num`;
                     `gamma:real->A`] P2AJ_B2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `ep:real`) THEN ASM_REWRITE_TAC[]];
    (* (c) *)
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `tau0:real`; `gs:num->real->A`; `q:A`;
                   `--(sqrt tau0 * Rm) * tau0`; `sub:num->num`] P2AJ_LAM_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
      USE_THEN "GSH" (MP_TAC o SPEC `n:num`) THEN USE_THEN "LLOW" (MP_TAC o SPEC `n:num`) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `x:A`; `nb:num`; `W:num->A->bool`; `A0:num->real`;
                   `a:num->real`; `b:num->real`; `C:num->A->bool`; `eta0:real`;
                   `Fs:num->A->bool`; `R:num->A->real`; `r:real`; `lam:real`; `Gm:real`;
                   `Rm:real`; `tau0:real`; `gs:num->real->A`; `max Lb (&0)`; `q:A`;
                   `sub:num->num`; `gamma:real->A`; `Lam:real`] P2AJ_MB_7_2_C) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[p2aj_lim] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* The statement (three dimensions, Perelman's setting).                     *)

let P2A_LEMMA_7_2_VIEW_X = prove
 (`!u:A->bool. P2A_LEMMA_7_2_VIEW_X_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LEMMA_7_2_VIEW_X_STATEMENT; P2AJ_RFS_P2A] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AJ_LEMMA_7_2_VIEW_X_GEN THEN
  MAP_EVERY EXISTS_TAC [`K:real->A->bool`; `Lb:real`] THEN ASM_REWRITE_TAC[]);;

