(* ========================================================================= *)
(* Unit pc_p2c_sing3: Lemma 11.23 for the maximal extension at the singular  *)
(* time (P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT).  Points of Omega with      *)
(* R_gl > r0^(-2) have canonical neighbourhoods at times close to T whose    *)
(* curvature is comparable to R(x); by Lemma 11.2 forward they lie in a      *)
(* compact sublevel set of R_gl in Omega, and the core SNGL_LIMIT_CANON of   *)
(* pc_p2c_sing2 applies to the maximal extension view.                       *)
(* ========================================================================= *)

needs "src/pc_p2c_sing2.ml";;
needs "src/pc_p2b_tube.ml";;
needs "src/pc_p3_c172d.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Forward bounds.  If R(z, t0) <= D at a time t0 of the last                *)
(* slab close enough to T, then R(z, s) stays below 2((D + 1) + r0^(-2)) up *)
(* to T, z lies in Omega and R_gl(z) obeys the same bound.                   *)
(* ------------------------------------------------------------------------- *)

let SNGL_FWD_BOUND = prove
 (`!(hs:(A)rfs_history) C eps r0 t0 D z s.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\ &0 <= D /\
     hs_time hs (hs_count hs) <= t0 /\ t0 <= s /\ s < rfs_horizon hs /\
     rfs_horizon hs - t0 <= inv(&16 * max C (&2) * ((D + &1) + inv(r0 pow 2))) /\
     z IN topspace(hs_top hs (hs_count hs)) /\
     mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t0) z <= D
     ==> mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) z
         <= &2 * ((D + &1) + inv(r0 pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sngl_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t0 < rfs_horizon(hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  ABBREV_TAC `top = hs_top hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `atlas = hs_atlas hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `g = hs_metric hs (hs_count(hs:(A)rfs_history))` THEN
  ABBREV_TAC `Tn = hs_time hs (hs_count(hs:(A)rfs_history))` THEN
  SUBGOAL_THEN `&0 <= t0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count(hs:(A)rfs_history)`] APX_HS_TIME_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(r0 pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POW_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t0)` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `BB = {z | z IN topspace top /\ mfd_scalar atlas ((g:real->A->real^3^3) t0) z < D + &1}` THEN
  SUBGOAL_THEN `open_in top (BB:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN ASM_SIMP_TAC[SNGL_SCALAR_SUBLEVEL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN BB` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view hs) (BB:A->bool) t0 s` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_LAST_PERSISTS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `sngl_fwd (hs:(A)rfs_history) C r0` THEN REWRITE_TAC[sngl_fwd] THEN
  DISCH_THEN(MP_TAC o SPECL [`BB:A->bool`; `t0:real`; `s:real`; `D + &1`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    X_GEN_TAC `y:A` THEN EXPAND_TAC "BB" THEN SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let SNGL_FWD_LIMIT = prove
 (`!(hs:(A)rfs_history) C eps r0 gl t0 D z.
     sngl_hyp hs C eps r0 /\ sngl_fwd hs C r0 /\
     open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
     rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
       (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
     &0 <= D /\ hs_time hs (hs_count hs) <= t0 /\ t0 < rfs_horizon hs /\
     rfs_horizon hs - t0 <= inv(&16 * max C (&2) * ((D + &1) + inv(r0 pow 2))) /\
     z IN topspace(hs_top hs (hs_count hs)) /\
     mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t0) z <= D
     ==> z IN p3_omega hs /\
         mfd_scalar (hs_atlas hs (hs_count hs)) gl z <= &2 * ((D + &1) + inv(r0 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN p3_omega hs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `t0:real`;
                   `D:real`] SNGL_FWD_SUBLEVEL) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[sngl_hyp]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`; `p3_omega(hs:(A)rfs_history)`;
                 `rfs_horizon(hs:(A)rfs_history)`; `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                 `gl:A->real^3^3`; `z:A`] P3E_LIMIT_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "lim")] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "lim" (MP_TAC o SPEC
    `mfd_scalar (hs_atlas hs (hs_count hs)) gl (z:A) - &2 * ((D + &1) + inv(r0 pow 2))`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
  USE_THEN "d" (MP_TAC o SPEC `max t0 (rfs_horizon(hs:(A)rfs_history) - d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `t0:real`; `D:real`;
                 `z:A`; `max t0 (rfs_horizon(hs:(A)rfs_history) - d / &2)`] SNGL_FWD_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Views that agree before T0 have the same strong canonical                 *)
(* neighbourhoods at times s < T0 (a strong neck at s only looks at times    *)
(* <= s); the maximal extension agrees with the history view before T.       *)
(* ------------------------------------------------------------------------- *)

let SNGL_NECK_AGREE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V' T0 eps x s e.
     (!t. t < T0 ==> rfs_vtop V' t = rfs_vtop V t /\ rfs_vatlas V' t = rfs_vatlas V t /\
                     rfs_vmetric V' t = rfs_vmetric V t) /\
     s < T0 /\ rfs_strong_neck V eps x s e
     ==> rfs_strong_neck V' eps x s e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT; REAL_LT_01] THEN
  USE_THEN "ag" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s x = rfs_vscalar V s x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2B9_RFS_VSCALAR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s x` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P2B9_RFS_VSCALAR] THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "ag" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "sl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t / R <= &0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
    USE_THEN "ag" (MP_TAC o SPEC `s + t / R`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let SNGL_CANON_AGREE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V' T0 C eps x s U.
     (!t. t < T0 ==> rfs_vtop V' t = rfs_vtop V t /\ rfs_vatlas V' t = rfs_vatlas V t /\
                     rfs_vmetric V' t = rfs_vmetric V t) /\
     s < T0 /\ rfs_strong_canonical V C eps x s U
     ==> rfs_strong_canonical V' C eps x s U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ag") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[SNGL_STRONG_CANON_ALT] THEN
  USE_THEN "ag" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') ==> (a \/ b ==> a' \/ b)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SNGL_NECK_AGREE THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `T0:real`] THEN
  ASM_REWRITE_TAC[]);;

let SNGL_MAXEXT_AGREE = prove
 (`!(hs:(A)rfs_history) Om gl t.
     t < rfs_horizon hs
     ==> rfs_vtop (p3_maxext hs Om gl) t = rfs_vtop (rfs_view hs) t /\
         rfs_vatlas (p3_maxext hs Om gl) t = rfs_vatlas (rfs_view hs) t /\
         rfs_vmetric (p3_maxext hs Om gl) t = rfs_vmetric (rfs_view hs) t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(t = rfs_horizon(hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p3_maxext; rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let SNGL_MAXEXT_END = prove
 (`!(hs:(A)rfs_history) Om gl.
     rfs_vtop (p3_maxext hs Om gl) (rfs_horizon hs) = subtopology (hs_top hs (hs_count hs)) Om /\
     rfs_vatlas (p3_maxext hs Om gl) (rfs_horizon hs) =
       restrict_atlas (hs_atlas hs (hs_count hs)) Om /\
     rfs_vmetric (p3_maxext hs Om gl) (rfs_horizon hs) =
       restrict_metric (hs_atlas hs (hs_count hs)) Om gl`,
  REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* ------------------------------------------------------------------------- *)
(* Curvature comparison on strong canonical neighbourhoods:                  *)
(* R(y) <= max C 2 * R(x) on U (necks: P3H_NECK_SCALAR; caps: the ratio      *)
(* clause; C-components: P2BT_C_COMPONENT_RATIO; round components:           *)
(* P2BT_ROUND_RATIO), and U lies in the slice.                               *)
(* ------------------------------------------------------------------------- *)

let SNGL_CANON_RATIO = prove
 (`?eps2. &0 < eps2 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      C eps x s U.
       p2c_regular_view V /\ &1 < C /\ &0 < eps /\ eps <= eps2 /\
       &0 < rfs_vscalar V s x /\ rfs_strong_canonical V C eps x s U
       ==> U SUBSET topspace(rfs_vtop V s) /\
           !y. y IN U ==> rfs_vscalar V s y <= max C (&2) * rfs_vscalar V s x`,
  MP_TAC(SPEC `&1 / &2` P3H_NECK_SCALAR) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `en:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))) THEN
  EXISTS_TAC `min en (&1 / &100)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s x` THEN
  SUBGOAL_THEN `!r. r <= &2 ==> r * R <= max C (&2) * R` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_strong_canonical (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) C eps x s U` THEN
  REWRITE_TAC[SNGL_STRONG_CANON_ALT] THEN STRIP_TAC THENL
   [(* neck *)
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                   `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                            `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    USE_THEN "ns" (MP_TAC o SPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `eps:real`; `x:A`; `s:real`; `&1`; `e:real^3->A`; `&0`; `y0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s + &0 / R = s /\ &1 / (&1 - &0) = &1` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_SUB_RZERO; REAL_INV_1;
                  REAL_MUL_LID];
      DISCH_TAC] THEN
    SUBGOAL_THEN `rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s
                    ((e:real^3->A) y0) / R <= &3 / &2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * R` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    (* cap *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
    SUBGOAL_THEN
     `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s) U /\
      (!y. y IN U ==> &0 < mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) y) /\
      rfs_sup_lt {mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) y2 /
                  mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) y1 | y1 IN U /\ y2 IN U} C`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rat"))) THENL
     [UNDISCH_TAC `rfs_cap (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,
                     rfs_vatlas V s) (rfs_vmetric V s) C eps U Y` THEN
      REWRITE_TAC[rfs_cap] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "rat" (MP_TAC o REWRITE_RULE[rfs_sup_lt]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC
     `mfd_scalar (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (rfs_vmetric V s) y /
      mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) x`))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`y:A`; `x:A`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * R` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d * R` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    (* C-component *)
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN ASM_MESON_TAC[rfs_c_component];
      ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `s:real`; `x:A`] SNGL_REGULAR_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `U SUBSET topspace(rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)` MP_TAC
      THENL [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN ASM_MESON_TAC[rfs_c_component];
             ASM SET_TAC[]];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vmetric (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `C:real`; `U:A->bool`; `x:A`; `y:A`] P2BT_C_COMPONENT_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `C * R <= max C (&2) * R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= C * R` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    (* round component *)
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN
      ASM_MESON_TAC[rfs_round_component];
      ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `s:real`; `x:A`] SNGL_REGULAR_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `U SUBSET topspace(rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)` MP_TAC
      THENL [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN
             ASM_MESON_TAC[rfs_round_component];
             ASM SET_TAC[]];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `rfs_vmetric (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                   `eps:real`; `U:A->bool`; `x:A`; `y:A`] P2BT_ROUND_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * R` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The typed disjunction for the maximal extension.  Omega                   *)
(* persists in the maximal extension over the last slab; for x in Omega with *)
(* R_gl(x) > r0^(-2) the canonical neighbourhoods of x at times close to T   *)
(* lie in the compact sublevel set K = {R_gl <= c} of Omega, and the core    *)
(* SNGL_LIMIT_CANON applies at T.                                            *)
(* ------------------------------------------------------------------------- *)

(* Same content as P3H_PERSISTS_ALT (pc_p3_c177c, outside this closure).  *)

let SNGL_PERSISTS_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
             open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]);;

let SNGL_MAXEXT_PERSISTS = prove
 (`!(hs:(A)rfs_history) Om gl a x.
     rfs_history_ok hs /\ open_in (hs_top hs (hs_count hs)) Om /\ x IN Om /\
     p2c_regular_view (p3_maxext hs Om gl) /\ hs_time hs (hs_count hs) <= a
     ==> rfs_persists (p3_maxext hs Om gl) Om a (rfs_horizon hs)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNGL_PERSISTS_ALT] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = rfs_horizon(hs:(A)rfs_history)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[SNGL_MAXEXT_END] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p3_maxext (hs:(A)rfs_history) Om gl`; `rfs_horizon(hs:(A)rfs_history)`;
                     `x:A`] SNGL_REGULAR_SLICE) THEN
      REWRITE_TAC[SNGL_MAXEXT_END] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
        SIMP_TAC[]];
      REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < rfs_horizon(hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Om:A->bool`; `gl:A->real^3^3`; `s:real`]
                SNGL_MAXEXT_AGREE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let SNGL_MAXEXT_TYPED = prove
 (`!u:A->bool.
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
     P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> ?Kc eps0. &2 <= Kc /\ &0 < eps0 /\
           !C eps (hs:(A)rfs_history) r0 gl.
             &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
             rfs_pinched (rfs_view hs) /\
             (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                    inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                    ==> p3_canon_at (rfs_view hs) C eps x t) /\
             open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
             rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
               (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
             ==> !x. x IN p3_omega hs /\
                     inv(r0 pow 2) < mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                     ==> (?e. rfs_strong_neck (p3_maxext hs (p3_omega hs) gl) (&2 * eps) x
                                              (rfs_horizon hs) e) \/
                         (?U Y. rfs_cap (rfs_vtop (p3_maxext hs (p3_omega hs) gl)
                                                  (rfs_horizon hs),
                                         rfs_vatlas (p3_maxext hs (p3_omega hs) gl)
                                                    (rfs_horizon hs))
                                        (rfs_vmetric (p3_maxext hs (p3_omega hs) gl)
                                                     (rfs_horizon hs))
                                        (&2 * C) (Kc * eps) U Y /\ x IN Y) \/
                         (?U. x IN U /\
                              rfs_c_component
                                (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs),
                                 rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                (&2 * C) U) \/
                         (?U. x IN U /\
                              rfs_round_component
                                (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs),
                                 rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                                (Kc * eps) U)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P2C_LEMMA_11_2_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_LEMMA_11_2_FROM_DB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `u:A->bool` SNGL_FWD_FROM) THEN
  ANTS_TAC THENL [MATCH_MP_TAC SNGL_P2_L112 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw"))) THEN
  MP_TAC(ISPEC `u:A->bool` SNGL_BWD_FROM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bw"))) THEN
  MP_TAC(SPEC `u:A->bool` SNGL_LIMIT_CANON) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e3:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core"))))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] SNGL_CANON_RATIO) THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio"))) THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `min (min e1 e2) (min e3 e4)`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                       `gl:A->real^3^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cn") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `sngl_hyp (hs:(A)rfs_history) C eps r0` ASSUME_TAC THENL
   [REWRITE_TAC[sngl_hyp] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sngl_fwd (hs:(A)rfs_history) C r0 /\ sngl_bwd hs C r0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "fw" MATCH_MP_TAC; USE_THEN "bw" MATCH_MP_TAC] THEN
    EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_MAXEXT_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_MAXEXT_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` SNGL_LAST_STAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
  SUBGOAL_THEN `&0 <= hs_time hs (hs_count(hs:(A)rfs_history))` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_POS THEN ASM_REWRITE_TAC[ARITH_RULE `n <= n + 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(hs_top hs (hs_count hs))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  (* constants *)
  ABBREV_TAC `Rx = mfd_scalar (hs_atlas hs (hs_count hs)) gl (x:A)` THEN
  ABBREV_TAC `D = max C (&2) * (Rx + &1)` THEN
  ABBREV_TAC `c = &2 * ((D + &1) + inv(r0 pow 2)) + Rx` THEN
  SUBGOAL_THEN `&0 <= D /\ Rx <= c /\ &2 * ((D + &1) + inv(r0 pow 2)) <= c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* R(x, t) converges to Rx *)
  MP_TAC(ISPECL [`hs_top hs (hs_count(hs:(A)rfs_history))`;
                 `hs_atlas hs (hs_count(hs:(A)rfs_history))`; `p3_omega(hs:(A)rfs_history)`;
                 `rfs_horizon(hs:(A)rfs_history)`; `hs_metric hs (hs_count(hs:(A)rfs_history))`;
                 `gl:A->real^3^3`; `x:A`] P3E_LIMIT_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `min (&1) (Rx - inv(r0 pow 2))`) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dx:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cx"))) THEN
  (* the window *)
  ABBREV_TAC `wf = inv(&16 * max C (&2) * ((D + &1) + inv(r0 pow 2)))` THEN
  SUBGOAL_THEN `&0 < wf` ASSUME_TAC THENL
   [EXPAND_TAC "wf" THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = min (min dx wf)
                        (rfs_horizon hs - hs_time hs (hs_count(hs:(A)rfs_history)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= dx /\ eta <= wf /\
                hs_time hs (hs_count(hs:(A)rfs_history)) <= rfs_horizon hs - eta`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the compact set *)
  ABBREV_TAC `K = {y | y IN p3_omega hs /\
                       mfd_scalar (hs_atlas hs (hs_count hs)) gl (y:A) <= c}` THEN
  SUBGOAL_THEN `compact_in (hs_top hs (hs_count hs)) (K:A->bool) /\
                K SUBSET p3_omega hs /\ (x:A) IN K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SNGL_OMEGA_PROPER THEN
      MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the core at T for the maximal extension *)
  USE_THEN "core" (MP_TAC o SPECL
    [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl`; `C:real`; `eps:real`;
     `rfs_horizon(hs:(A)rfs_history)`; `x:A`; `eta:real`; `p3_omega(hs:(A)rfs_history)`;
     `K:A->bool`]) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SNGL_MAXEXT_PERSISTS THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SNGL_MAXEXT_END; COMPACT_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] SNGL_LAST_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "cx" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `inv(r0 pow 2) <= mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s)
                                (x:A) /\
    mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) x <= Rx + &1`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "cn" (MP_TAC o SPECL [`s:real`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3_canon_at] THEN DISCH_THEN(X_CHOOSE_TAC `U:A->bool`) THEN
  EXISTS_TAC `U:A->bool` THEN
  USE_THEN "ratio" (MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `C:real`; `eps:real`;
                                    `x:A`; `s:real`; `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb")) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SNGL_CANON_AGREE THEN
    MAP_EVERY EXISTS_TAC [`rfs_view (hs:(A)rfs_history)`; `rfs_horizon(hs:(A)rfs_history)`] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SNGL_MAXEXT_AGREE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `mfd_scalar (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) s) (y:A) <= D`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max C (&2) * mfd_scalar (hs_atlas hs (hs_count hs))
                                        (hs_metric hs (hs_count hs) s) (x:A)` THEN
    CONJ_TAC THENL [USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "D" THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `gl:A->real^3^3`;
                 `s:real`; `D:real`; `y:A`] SNGL_FWD_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN ASM SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem, for the typed MAXEXT statement with p3_canon_typed V    *)
(* (2C) (2 eps) (Kc eps): it is the typed core SNGL_MAXEXT_TYPED itself.     *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_23_MAXEXT_ROUTE = prove
 (`!u:A->bool. P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT; P2C_LEMMA_11_23_MAXEXT_STATEMENT;
              p3_canon_typed] THEN
  STRIP_TAC THEN MP_TAC(SPEC `u:A->bool` SNGL_MAXEXT_TYPED) THEN ASM_REWRITE_TAC[]);;

