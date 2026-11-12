(* ========================================================================= *)
(* pc_p2a_flow3: the flow level of the Part 2A L-geometry, third file, at    *)
(* N = 3: FL6 P2A_FLOW_THM_8_1 (MT Thm 8.1 for complete flows of bounded     *)
(* curvature) from C1 FIX (P2AT_THM_8_1_VIEW_FIX, pc_p2a_t81u), FL0 and FL2. *)
(* The theorem here is an implication from the statement constant FL2, which *)
(* pc_p2a_flfin discharges.                                                  *)
(* ========================================================================= *)

needs "src/pc_p2a_flow2.ml";;
needs "src/pc_p2a_t81u.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* FL6 (MT Thm 8.1 for complete flows of bounded curvature) from C1 FIX     *)
(* (P2AT_THM_8_1_VIEW_FIX, pc_p2a_t81u), FL0 (P2AW_FLOW_VIEW_3, pc_p2a_wk1) *)
(* and FL2: the ball persists as a region (FL0), its closure is compact     *)
(* (inside the closed ball, completeness at b), and every point of B has a  *)
(* minimizer of length 2 sqrt(tau0) lx <= 2 sqrt(tau0) l0.                  *)
(* ------------------------------------------------------------------------- *)

(* The closure of a ball of a complete metric is compact.                    *)

let P2AU_BALL_CLOSURE_COMPACT = prove
 (`!top atlas (g:A->real^N^N) p r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top
     ==> compact_in top (top closure_of (mfd_ball (top,atlas) g p r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) p r` THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE]]);;

(* FL6 from FL2.                                                             *)

let P2AU_FLOW_THM_8_1 = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n ==> P2A_FLOW_THM_8_1_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_FLOW_THM_8_1_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "FL2") THEN
  MAP_EVERY X_GEN_TAC [`taub:real`; `l0:real`; `V0:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`taub:real`; `l0:real`; `V0:real`]
    (REWRITE_RULE[P2A_THM_8_1_VIEW_FIX_STATEMENT] (SPEC `u:A->bool` P2AT_THM_8_1_VIEW_FIX))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))) THEN
  EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `r:real`; `tau0:real`;
                       `B:A->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(SPECL [`u:A->bool`; `n:3->bool`] P2AW_FLOW_VIEW_3) THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `a:real`; `b:real`; `g:real->A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "REG") (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b) /\
                mfd_complete (top,atlas) (g b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t <= b
        ==> rfs_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                                    (g:real->A->real^3^3)) t = top /\
            rfs_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = atlas /\
            rfs_vmetric (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = g t`
  (LABEL_TAC "VP") THENL
   [REWRITE_TAC[GSYM P2A_VIEW_PROJ_3; P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "VP" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  USE_THEN "VP" (MP_TAC o SPEC `b - tau0`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_atlas_lc (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3))` ASSUME_TAC THENL
   [REWRITE_TAC[P2A_ATLAS_LC_FLOW_VIEW]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_vball (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p r =
    mfd_ball (top,atlas) (g b) p r`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[P2A_T81_VBALL_RFS]; ALL_TAC] THEN
  (* every point of B has a minimizer of length at most 2 sqrt(tau0) l0 *)
  SUBGOAL_THEN
   `!q. q IN B
        ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                               (g:real->A->real^3^3)) b p tau0 gamma /\
                    gamma tau0 = q /\
                    p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau0
                    <= &2 * sqrt tau0 * l0`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    USE_THEN "FL2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `q:A`;
                                   `tau0:real`] o REWRITE_RULE[P2A_FLOW_MIN_EXISTS_STATEMENT]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2A_MIN_LX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:A` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `l0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[p2a_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      ASM_SIMP_TAC[SQRT_POS_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  (* the remaining hypotheses of C1 in rewritten form *)
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3))
                           (mfd_ball (top,atlas) ((g:real->A->real^3^3) b) p r)
                           (b - r pow 2) b` ASSUME_TAC THENL
   [USE_THEN "REG" MATCH_MP_TAC THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of
                  (mfd_ball (top,atlas) ((g:real->A->real^3^3) b) p r))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_BALL_CLOSURE_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. b - r pow 2 < s /\ s <= b /\ y IN mfd_ball (top,atlas) ((g:real->A->real^3^3) b) p r
          ==> p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) s y <= inv(r pow 2)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "VP" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[p3_vrm] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "mfd_ball" th &&
      p2au_mentions "mfd_rm_norm" th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. mfd_has_volume (top,atlas) ((g:real->A->real^3^3) (b - tau0)) B v /\
                    V0 <= v` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "C1" (MP_TAC o SPECL
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `p:A`; `b:real`; `r:real`; `tau0:real`; `B:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

