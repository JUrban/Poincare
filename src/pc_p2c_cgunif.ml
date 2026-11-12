(* ========================================================================= *)
(* Unit pc_p2c_cgunif (Part 2C, used in the pc_p2c_cg route): uniform        *)
(* geometry of a sequence of pointed Riemannian 3-manifolds (top k, atlas k, *)
(* h k, x k) whose balls B(x k,A) eventually have compact closure, carry     *)
(* bounds of every lrm_deriv_norm2 l, and with a volume lower bound at the   *)
(* base point.  Curvature and Ricci bounds, volume upper and lower bounds    *)
(* (CMP_RELVOL), injectivity radius bounds (from the hypothesis              *)
(* P2C_REQ_CGT_STATEMENT, which is CMP_T2_CGT of pc_cmp_cgt), packing and    *)
(* nets, normal charts with C^m bounds (P2C_GAUGE).                          *)
(* ========================================================================= *)

needs "src/pc_p2c_gauge.ml";;
needs "src/pc_cmp_relvol.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_geo_normal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The scaled sequence (p2cu_seq) and its curvature bounds on the balls B(x  *)
(* k,A): |Rm| <= K and Ric >= -2 K (in the form used by CMP_RELVOL).         *)
(* ------------------------------------------------------------------------- *)

let p2cu_seq = new_definition
 `p2cu_seq (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
           (h:num->A->real^3^3) (x:num->A) <=>
    (!k. hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
         riemannian_metric (atlas k) (h k) /\ x k IN topspace (top k)) /\
    (!A. &0 < A
         ==> ?N. !k. N <= k
                     ==> compact_in (top k)
                           (top k closure_of mfd_ball (top k,atlas k) (h k) (x k) A)) /\
    (!A l. &0 < A
           ==> ?C N. !k y. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                           ==> lrm_deriv_norm2 l
                                 (metric_local (atlas k) (chart_at (atlas k) y) (h k))
                                 (SND(chart_at (atlas k) y) y) <= C) /\
    (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
       !k. N <= k
           ==> ?v. mfd_has_volume (top k,atlas k) (h k)
                                  (mfd_ball (top k,atlas k) (h k) (x k) r0) v /\
                   kappa * r0 pow 3 <= v)`;;

let P2CU_BALL_SUBSET = prove
 (`!top atlas (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas
     ==> mfd_ball (top,atlas) g x r SUBSET topspace top`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

(* Balls around points of B(x,A) lie in larger balls around x. *)

let P2CU_BALL_SHIFT = prove
 (`!top atlas (g:A->real^N^N) x y A r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x A
     ==> mfd_ball (top,atlas) g y r SUBSET mfd_ball (top,atlas) g x (A + r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_TRANS];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2CU_RM_BOUND = prove
 (`!top atlas (h:num->A->real^3^3) x A.
     p2cu_seq top atlas h x /\ &0 < A
     ==> ?K N. &0 < K /\
               !k y. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                     ==> mfd_rm_norm (atlas k) (h k) y <= K`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`A:real`; `0`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_TAC `N:num`)) THEN
  MAP_EVERY EXISTS_TAC [`sqrt(abs C) + &1`; `N:num`] THEN
  SUBGOAL_THEN `&0 <= sqrt(abs C)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  MATCH_MP_TAC P2C_RM_NORM_LE THEN
  EXISTS_TAC `(top:num->A topology) k` THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
    ASM_REAL_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `C:real` THEN ASM_SIMP_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `sqrt(abs C) pow 2` THEN CONJ_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

let P2CU_RICCI_BOUND = prove
 (`!top atlas (h:num->A->real^3^3) x A.
     p2cu_seq top atlas h x /\ &0 < A
     ==> ?K N. &0 < K /\
               !k y w. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                       ==> --(&(dimindex(:3) - 1) * K) * (w dot (h k y ** w)) <=
                           mfd_ricci (atlas k) (h k) y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`] P2CU_RM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `(y:A) IN topspace((top:num->A topology) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `y:A`; `--K:real`; `w:real^3`]
                CMPZ_MFD_RICCI_SEC_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                   `(h:num->A->real^3^3) k`; `y:A`; `u:real^3`; `v:real^3`]
                  MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Volumes.  Balls with compact closure have volumes; subsets of B(x k,A)    *)
(* have volume at most V_{-K}(A) (CMP_RELVOL); balls B(y,r) around points y  *)
(* of B(x k,A) have volume at least a constant c(A,r) > 0 (CMP_RELVOL with   *)
(* the volume lower bound at the base point).                                *)
(* ------------------------------------------------------------------------- *)

let P2CU_CLOSURE_COMPACT_MONO = prove
 (`!top (s:A->bool) t.
     compact_in top (top closure_of t) /\ s SUBSET t
     ==> compact_in top (top closure_of s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `top closure_of (t:A->bool)` THEN
  ASM_SIMP_TAC[CLOSURE_OF_MONO; CLOSED_IN_CLOSURE_OF]);;

let P2CU_BALL_HAS_VOLUME = prove
 (`!top atlas (g:A->real^N^N) y r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top (top closure_of mfd_ball (top,atlas) g y r)
     ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) y r`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_ball (top,atlas) (g:A->real^N^N) y r`;
                 `top closure_of mfd_ball (top,atlas) (g:A->real^N^N) y r`; `w:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; MFD_BALL_OPEN; CLOSURE_OF_SUBSET;
               P2CU_BALL_SUBSET] THEN
  MESON_TAC[]);;

let P2CU_BALL_SYM = prove
 (`!top atlas (g:A->real^N^N) x y r.
     smooth_manifold_atlas top atlas /\ y IN mfd_ball (top,atlas) g x r
     ==> x IN mfd_ball (top,atlas) g y r`,
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]);;

let P2CU_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) x r s.
     r <= s ==> mfd_ball (top,atlas) g x r SUBSET mfd_ball (top,atlas) g x s`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

let P2CU_VMODEL_POS = prove
 (`!K t. &0 <= K /\ &0 < t ==> &0 < cmp_vmodel (:3) (--K) t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--K:real`; `t:real`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPECL [`&0`; `t:real`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`--K:real`; `t:real`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

let P2CU_VOL_UPPER = prove
 (`!top atlas (h:num->A->real^3^3) x A.
     p2cu_seq top atlas h x /\ &0 < A
     ==> ?V N. !k S v. N <= k /\ S SUBSET mfd_ball (top k,atlas k) (h k) (x k) A /\
                       mfd_has_volume (top k,atlas k) (h k) S v
                       ==> v <= V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`] P2CU_RICCI_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `A:real` o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MAP_EVERY EXISTS_TAC [`cmp_vmodel (:3) (--K) A`; `N1 + N2:num`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `compact_in ((top:num->A topology) k)
                  (top k closure_of mfd_ball (top k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                                             ((h:num->A->real^3^3) k) ((x:num->A) k) A)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `(x:num->A) k`; `A:real`]
                P2CU_BALL_HAS_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  TRANS_TAC REAL_LE_TRANS `w:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                          `(h:num->A->real^3^3) k`; `S:A->bool`;
                          `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) A`]
                        MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                  `(h:num->A->real^3^3) k`; `(x:num->A) k`; `K:real`; `A:real`; `A:real`;
                  `A:real`; `w:real`; `w:real`]
                 (REWRITE_RULE[CMP_RELVOL_STATEMENT] (ISPECL [`(:A)`; `(:3)`] CMP_RELVOL))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[]]]);;

let P2CU_VOL_LOWER = prove
 (`!top atlas (h:num->A->real^3^3) x A r.
     p2cu_seq top atlas h x /\ &0 < A /\ &0 < r
     ==> ?c N. &0 < c /\
               !k y. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                     ==> ?v. mfd_has_volume (top k,atlas k) (h k)
                                            (mfd_ball (top k,atlas k) (h k) y r) v /\
                             c <= v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2cu_seq]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `kappa:real`
    (X_CHOOSE_THEN `N0:num` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v0")))))) THEN
  ABBREV_TAC `R = A + r0 + r` THEN
  SUBGOAL_THEN `&0 < R /\ r <= R /\ A + r0 <= R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A + R:real`] P2CU_RICCI_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `A + R:real` o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N2:num`)] THEN
  MAP_EVERY EXISTS_TAC
   [`kappa * r0 pow 3 * cmp_vmodel (:3) (--K) r / cmp_vmodel (:3) (--K) R`;
    `N0 + N1 + N2:num`] THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:3) (--K) r /\ &0 < cmp_vmodel (:3) (--K) R`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CU_VMODEL_POS THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN
   `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y R SUBSET mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) ((x:num->A) k) (A + R) /\
    mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) (x k) r0 SUBSET mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) y R /\
    mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) y r SUBSET mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) y R`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[];
      TRANS_TAC SUBSET_TRANS
       `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                 ((h:num->A->real^3^3) k) y (A + r0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2CU_BALL_SYM THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in ((top:num->A topology) k)
                  (top k closure_of mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y R)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) (A + R)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in ((top:num->A topology) k)
                  (top k closure_of mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y R` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `y:A`; `r:real`] P2CU_BALL_HAS_VOLUME) THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `y:A`; `R:real`] P2CU_BALL_HAS_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `v1:real`) THEN
  EXISTS_TAC `v1:real` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "v0" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `v0 <= v2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                          `(h:num->A->real^3^3) k`;
                          `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                                    ((h:num->A->real^3^3) k) ((x:num->A) k) r0`;
                          `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                                    ((h:num->A->real^3^3) k) y R`]
                        MFD_HAS_VOLUME_MONO) THEN
    UNDISCH_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) ((x:num->A) k) r0 SUBSET
                 mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) y R` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                `(h:num->A->real^3^3) k`; `y:A`; `K:real`; `R:real`; `r:real`;
                `R:real`; `v1:real`; `v2:real`]
               (REWRITE_RULE[CMP_RELVOL_STATEMENT] (ISPECL [`(:A)`; `(:3)`] CMP_RELVOL))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
      UNDISCH_TAC `compact_in ((top:num->A topology) k)
                     (top k closure_of mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y R)` THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        UNDISCH_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) ((h:num->A->real^3^3) k) y R SUBSET
                     mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k) (h k) ((x:num->A) k) (A + R)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `kappa * r0 pow 3 * cmp_vmodel (:3) (--K) r / cmp_vmodel (:3) (--K) R =
                (kappa * r0 pow 3 * cmp_vmodel (:3) (--K) r) / cmp_vmodel (:3) (--K) R`
  SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `v2 * cmp_vmodel (:3) (--K) r` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity radius bounds on B(x k,A) from the hypothesis                 *)
(* P2C_REQ_CGT_STATEMENT (CMP_T2_CGT of pc_cmp_cgt), packing of separated    *)
(* sets, and finite nets with x k first.                                     *)
(* ------------------------------------------------------------------------- *)

let P2CU_INJ = prove
 (`!top atlas (h:num->A->real^3^3) x A.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x /\ &0 < A
     ==> ?i0 N. &0 < i0 /\ i0 < &1 /\
                !k y. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                      ==> mfd_inj_ball (top k,atlas k) (h k) y i0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A + &1`] P2CU_RM_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`; `&1`] P2CU_VOL_LOWER) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `A + &1` o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N3:num`)] THEN
  UNDISCH_TAC `P2C_REQ_CGT_STATEMENT (:A)` THEN REWRITE_TAC[P2C_REQ_CGT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`K:real`; `&1`; `c:real`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cgt")))) THEN
  MAP_EVERY EXISTS_TAC [`i0:real`; `N1 + N2 + N3:num`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN
   `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
             ((h:num->A->real^3^3) k) y (&1) SUBSET
    mfd_ball (top k,atlas k) (h k) ((x:num->A) k) (A + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "cgt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
    MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,(atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) ((x:num->A) k) (A + &1)` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM SET_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Finite families of disjoint sets with volumes at least c. *)

let P2CU_DISJOINT_VOLUME = prove
 (`!top atlas (g:A->real^N^N) (B:A->A->bool) c Ts.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ FINITE Ts /\
     (!y. y IN Ts ==> ?v. mfd_has_volume (top,atlas) g (B y) v /\ c <= v) /\
     (!y z. y IN Ts /\ z IN Ts /\ ~(y = z) ==> DISJOINT (B y) (B z))
     ==> ?v. mfd_has_volume (top,atlas) g (UNIONS (IMAGE B Ts)) v /\ &(CARD Ts) * c <= v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b ==> c ==> d ==> e`] THEN
  DISCH_TAC THEN SPEC_TAC(`Ts:A->bool`,`Ts:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; CARD_CLAUSES; REAL_MUL_LZERO; REAL_LE_REFL;
                MFD_HAS_VOLUME_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `Ts:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vol") (LABEL_TAC "dis")) THEN
  REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "vol" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT];
      REPEAT STRIP_TAC THEN USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "vol" (MP_TAC o SPEC `y:A`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u + w:real` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IMAGE_CLAUSES; UNIONS_INSERT; GSYM REAL_OF_NUM_SUC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!z. z IN Ts ==> DISJOINT ((B:A->A->bool) y) (B z)` MP_TAC THENL
     [REPEAT STRIP_TAC THEN REMOVE_THEN "dis" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
      SET_TAC[]];
    ASM_REAL_ARITH_TAC]);;

let P2CU_PACKING = prove
 (`!top atlas (h:num->A->real^3^3) x A r.
     p2cu_seq top atlas h x /\ &0 < A /\ &0 < r
     ==> ?P N. !k S. N <= k /\ S SUBSET mfd_ball (top k,atlas k) (h k) (x k) A /\
                     (!y z. y IN S /\ z IN S /\ ~(y = z)
                            ==> r <= mfd_dist (top k,atlas k) (h k) y z)
                     ==> FINITE S /\ CARD S <= P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`; `r / &2`] P2CU_VOL_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low")))) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A + r / &2`] P2CU_VOL_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real` (X_CHOOSE_THEN `N2:num` (LABEL_TAC "up"))) THEN
  X_CHOOSE_TAC `P:num` (SPEC `V / c` REAL_ARCH_SIMPLE) THEN
  MAP_EVERY EXISTS_TAC [`P:num`; `N1 + N2:num`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `S:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `!Ts. Ts SUBSET S /\ FINITE Ts ==> CARD(Ts:A->bool) <= P` (LABEL_TAC "card") THENL
   [X_GEN_TAC `Ts:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                   `(h:num->A->real^3^3) k`;
                   `\y:A. mfd_ball ((top:num->A topology) k,
                                    (atlas:num->((A->bool)#(A->real^3))->bool) k)
                                   ((h:num->A->real^3^3) k) y (r / &2)`;
                   `c:real`; `Ts:A->bool`] P2CU_DISJOINT_VOLUME) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "low" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `p:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "sep" (MP_TAC o SPECL [`y:A`; `z:A`]) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`(top:num->A topology) k`;
                       `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                       `(h:num->A->real^3^3) k`; `y:A`; `p:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
        MP_TAC(ISPECL [`(top:num->A topology) k`;
                       `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                       `(h:num->A->real^3^3) k`; `z:A`; `p:A`] MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v <= V` ASSUME_TAC THENL
     [USE_THEN "up" MATCH_MP_TAC THEN
      EXISTS_TAC `k:num` THEN
      EXISTS_TAC `UNIONS (IMAGE (\y:A. mfd_ball ((top:num->A topology) k,
                                    (atlas:num->((A->bool)#(A->real^3))->bool) k)
                                   ((h:num->A->real^3^3) k) y (r / &2)) Ts)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&(CARD(Ts:A->bool)) * c <= V` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(CARD(Ts:A->bool)) <= V / c` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`SUC P`; `S:A->bool`] CHOOSE_SUBSET_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Ts:A->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "card" (MP_TAC o SPEC `Ts:A->bool`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN REMOVE_THEN "card" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* Nets: P points, x k first, all in B(x k,A), whose r-balls cover B(x k,A). *)

let P2CU_NET = prove
 (`!top atlas (h:num->A->real^3^3) x A r.
     p2cu_seq top atlas h x /\ &0 < A /\ &0 < r
     ==> ?P N. !k. N <= k
                   ==> ?y. y 0 = x k /\
                           (!s. y s IN mfd_ball (top k,atlas k) (h k) (x k) A) /\
                           (!p. p IN mfd_ball (top k,atlas k) (h k) (x k) A
                                ==> ?s. s < P /\ mfd_dist (top k,atlas k) (h k) (y s) p < r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`; `r:real`] P2CU_PACKING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` (X_CHOOSE_THEN `N:num` (LABEL_TAC "pack"))) THEN
  MAP_EVERY EXISTS_TAC [`P + 1`; `N:num`] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  ABBREV_TAC `Bk = mfd_ball ((top:num->A topology) k,
                             (atlas:num->((A->bool)#(A->real^3))->bool) k)
                            ((h:num->A->real^3^3) k) ((x:num->A) k) A` THEN
  ABBREV_TAC `dk = mfd_dist ((top:num->A topology) k,
                             (atlas:num->((A->bool)#(A->real^3))->bool) k)
                            ((h:num->A->real^3^3) k)` THEN
  SUBGOAL_THEN `(x:num->A) k IN Bk` ASSUME_TAC THENL
   [EXPAND_TAC "Bk" THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!S. S SUBSET Bk /\
                    (!y z. y IN S /\ z IN S /\ ~(y = z) ==> r <= (dk:A->A->real) y z)
                    ==> FINITE S /\ CARD(S:A->bool) <= P`
  (LABEL_TAC "pk") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "pack" MATCH_MP_TAC THEN
    EXISTS_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["Bk"; "dk"] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(S:A->bool) SUBSET Bk` THEN EXPAND_TAC "Bk" THEN SIMP_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `!y z. y IN S /\ z IN S /\ ~(y = z) ==> r <= (dk:A->A->real) (y:A) z` THEN
    EXPAND_TAC "dk" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. ?S. (x:num->A) k IN S /\ S SUBSET Bk /\
                        (!y z. y IN S /\ z IN S /\ ~(y = z) ==> r <= (dk:A->A->real) y z) /\
                        CARD S = n` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `1` THEN EXISTS_TAC `{(x:num->A) k}` THEN
      ASM_REWRITE_TAC[IN_SING; CARD_SING; SING_SUBSET] THEN MESON_TAC[];
      EXISTS_TAC `P:num` THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "pk" (MP_TAC o SPEC `S:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `S0:A->bool` STRIP_ASSUME_TAC) (LABEL_TAC "max"))) THEN
  REMOVE_THEN "pk" (MP_TAC o SPEC `S0:A->bool`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S0:A->bool) HAS_SIZE m` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!p. p IN Bk ==> ?z. z IN (S0:A->bool) /\ (dk:A->A->real) z p < r` ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    SUBGOAL_THEN `~((p:A) IN (S0:A->bool))` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(top:num->A topology) k`;
                     `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                     `(h:num->A->real^3^3) k`; `p:A`] MFD_DIST_REFL) THEN
      EXPAND_TAC "dk" THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
        DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "max" (MP_TAC o SPEC `m + 1`) THEN REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    EXISTS_TAC `(p:A) INSERT (S0:A->bool)` THEN
    ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; INSERT_SUBSET; ADD1] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(ISPECL [`(top:num->A topology) k`;
                     `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                     `(h:num->A->real^3^3) k`; `y:A`; `z:A`] MFD_DIST_SYM) THEN
      EXPAND_TAC "dk" THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (is_forall o concl) o
                    check (fun th -> can (find_term ((=) `p:A`)) (concl th))) THEN
      EXPAND_TAC "dk" THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (is_forall o concl) o
                    check (fun th -> can (find_term ((=) `p:A`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\s. if s = 0 then (x:num->A) k else if s <= m then (f:num->A) (s - 1)
                  else x k` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    UNDISCH_TAC `(S0:A->bool) SUBSET Bk` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `i + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0) /\ (i + 1) - 1 = i`] THEN
    SUBGOAL_THEN `i + 1 <= m` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Normal charts w |-> exp_y(E w) for an orthonormal frame E on               *)
(* an injectivity ball of radius r: the image of ball(0,r) is the metric     *)
(* ball B(y,r), d(y, exp_y(E w)) = |w|, injectivity, and with |Rm| <= K,      *)
(* K r^2 <= 1 the two-sided Lipschitz bounds d <= sqrt 2 |w1 - w2| on        *)
(* ball(0,r) and |w1 - w2| <= sqrt 2 d on ball(0,r/4) (via the pullback      *)
(* metric cmp_expmetric, 1/2 <= G <= 2, and lengths of lifted curves).       *)
(* ------------------------------------------------------------------------- *)

(* A copy of RFA_FRAME_EXISTS (pc_rfa_slmfd), proved here so that this unit  *)
(* does not load the Ricci-flow slice units.                                 *)

let P2CU_FRAME_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) g x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top
     ==> ?E:real^N^N. mfd_orthonormal_frame g x E`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                               (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`] LRG_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:A->real^N^N) x = transp M ** (M:real^N^N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(M:real^N^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  ASM_REWRITE_TAC[mfd_orthonormal_frame] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID; GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID]);;

let P2CU_NCH_FACTS = prove
 (`!top atlas (g:A->real^N^N) y E r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_orthonormal_frame g y E /\ mfd_inj_ball (top,atlas) g y r
     ==> mfd_param top atlas (ball(vec 0,r)) (\w. mfd_exp (top,atlas) g y (E ** w)) /\
         IMAGE (\w. mfd_exp (top,atlas) g y (E ** w)) (ball(vec 0,r)) =
         mfd_ball (top,atlas) g y r /\
         (!w. norm w < r
              ==> E ** w IN mfd_exp_dom (top,atlas) g y /\
                  mfd_joinable (top,atlas) y (mfd_exp (top,atlas) g y (E ** w)) /\
                  mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g y (E ** w)) = norm w) /\
         (!w1 w2. norm w1 < r /\ norm w2 < r /\
                  mfd_exp (top,atlas) g y (E ** w1) = mfd_exp (top,atlas) g y (E ** w2)
                  ==> w1 = w2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`] GEON_FRAME_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `r:real`] MFD_EXP_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w. norm w < r ==> (E:real^N^N) ** w IN mfd_tball (g:A->real^N^N) y r`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) y`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[mfd_inj_ball; SUBSET]; ASM_REWRITE_TAC[]] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
    MATCH_MP_TAC MFD_EXP_DIST THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** w1 = E ** w2` MP_TAC THENL
     [MATCH_MP_TAC CMPS_INJ_BALL_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `y:A`; `r:real`] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV]]]);;

(* Lower bounds for distances from lower bounds for curve lengths. *)

let P2CU_DIST_GE = prove
 (`!top atlas (g:A->real^N^N) p q L.
     mfd_joinable (top,atlas) p q /\
     (!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = p /\ gamma(&1) = q
              ==> L <= mfd_length atlas g gamma (&0) (&1))
     ==> L <= mfd_dist (top,atlas) g p q`,
  REWRITE_TAC[mfd_dist; mfd_joinable] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_INF THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)` THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `l:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The pullback metric of a normal chart, as a riemannian metric on the     *)
(* open set ball(0,r), with 1/2 <= G <= 2 (CMP_EXP_PULLBACK).                *)

let P2CU_EXPMETRIC_FACTS = prove
 (`!top atlas (g:A->real^N^N) y E r K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_orthonormal_frame g y E /\ mfd_inj_ball (top,atlas) g y r /\
     &0 < r /\ &0 <= K /\ K * r pow 2 <= &1 /\
     (!z. z IN mfd_ball (top,atlas) g y r ==> mfd_rm_norm atlas g z <= K)
     ==> metric_field (ball(vec 0,r)) (cmp_expmetric (top,atlas) g y E) /\
         riemannian_metric (open_set_atlas (ball(vec 0,r))) (cmp_expmetric (top,atlas) g y E) /\
         cmp_expmetric (top,atlas) g y E (vec 0) = mat 1 /\
         (!w v. norm w < r
                ==> inv(&2) * norm v pow 2 <= v dot (cmp_expmetric (top,atlas) g y E w ** v) /\
                    v dot (cmp_expmetric (top,atlas) g y E w ** v) <= &2 * norm v pow 2) /\
         (!w. w IN ball(vec 0,r)
              ==> cmp_expmetric (top,atlas) g y E w =
                  mpullback (SND(chart_at atlas (mfd_exp (top,atlas) g y (E ** w))) o
                             (\w. mfd_exp (top,atlas) g y (E ** w)))
                            (metric_local atlas
                               (chart_at atlas (mfd_exp (top,atlas) g y (E ** w))) g) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                `y:A`; `E:real^N^N`; `K:real`; `r:real`]
               (REWRITE_RULE[CMP_EXP_PULLBACK_STATEMENT]
                 (ISPECL [`(:A)`; `(:N)`] CMP_EXP_PULLBACK))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_inj_ball]; STRIP_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; OPEN_BALL; NORM_POW_2] THEN
  X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w) IN topspace top`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CMPP_EXPMETRIC_LOCAL THEN ASM_SIMP_TAC[]);;

let P2CU_NCH_LIP_UPPER = prove
 (`!top atlas (g:A->real^N^N) y E r K w1 w2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_orthonormal_frame g y E /\ mfd_inj_ball (top,atlas) g y r /\
     &0 < r /\ &0 <= K /\ K * r pow 2 <= &1 /\
     (!z. z IN mfd_ball (top,atlas) g y r ==> mfd_rm_norm atlas g z <= K) /\
     norm w1 < r /\ norm w2 < r
     ==> mfd_joinable (top,atlas) (mfd_exp (top,atlas) g y (E ** w1))
                                  (mfd_exp (top,atlas) g y (E ** w2)) /\
         mfd_dist (top,atlas) g (mfd_exp (top,atlas) g y (E ** w1))
                                (mfd_exp (top,atlas) g y (E ** w2))
         <= sqrt(&2) * norm(w1 - w2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "param") (K ALL_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`; `K:real`]
                P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "bnd") (LABEL_TAC "pb"))))) THEN
  SUBGOAL_THEN `segment[w1:real^N,w2] SUBSET ball(vec 0,r)` (LABEL_TAC "segb") THENL
   [MP_TAC(ISPECL [`vec 0:real^N`; `r:real`] CONVEX_BALL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball(vec 0:real^N,r),(\x:real^N. x)) IN open_set_atlas (ball(vec 0,r))`
  (LABEL_TAC "inat") THENL [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^N,r)))
                                      (open_set_atlas (ball(vec 0,r)))`
  (LABEL_TAC "osa") THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,r))`;
                 `open_set_atlas (ball(vec 0:real^N,r))`;
                 `ball(vec 0:real^N,r)`; `\x:real^N. x`; `w1:real^N`; `w2:real^N`]
                GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IMAGE_ID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seg") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (K ALL_TAC))) THEN
  ABBREV_TAC `c = \t. chart_inv (ball(vec 0:real^N,r),(\x:real^N. x)) (w1 + t % (w2 - w1))` THEN
  SUBGOAL_THEN `(c:real->real^N) (&0) = w1 /\ c (&1) = w2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[] THENL
     [USE_THEN "seg" (MP_TAC o SPEC `&0`); USE_THEN "seg" (MP_TAC o SPEC `&1`)] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    SIMP_TAC[VECTOR_ARITH `w1 + w2 - w1:real^N = w2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,r))`;
                 `open_set_atlas (ball(vec 0:real^N,r))`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                 `ball(vec 0:real^N,r)`; `\x:real^N. x`; `w1:real^N`; `w2:real^N`;
                 `inv(&2)`; `&2`; `ball(vec 0:real^N,r)`] GRGD_SEGMENT_LENGTH_UPPER) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IMAGE_ID; SUBSET_REFL] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^N,r)`; `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                   `z:real^N`] RFB_OPEN_SET_METRIC_LOCAL) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "bnd" MATCH_MP_TAC THEN ASM_MESON_TAC[IN_BALL_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `ball(vec 0:real^N,r)`;
                 `\w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                 `c:real->real^N`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "pb" (MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(\w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)) o (c:real->real^N)`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(\w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)) o (c:real->real^N)`;
                 `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
  REWRITE_TAC[o_THM; GSYM dist] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2CU_INV_SQRT2 = prove
 (`&0 < inv(sqrt(&2)) /\ inv(sqrt(&2)) <= &1 /\ sqrt(&2) * inv(sqrt(&2)) = &1`,
  SUBGOAL_THEN `&1 <= sqrt(&2)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC]);;

(* Curves inside B(y,r) lift to the chart and are not shorter than        *)
(* |w1 - w2| / sqrt 2.                                                       *)

let P2CU_NCH_CURVE_IN = prove
 (`!top atlas (g:A->real^N^N) y E r K w1 w2 gamma.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_orthonormal_frame g y E /\ mfd_inj_ball (top,atlas) g y r /\
     &0 < r /\ &0 <= K /\ K * r pow 2 <= &1 /\
     (!z. z IN mfd_ball (top,atlas) g y r ==> mfd_rm_norm atlas g z <= K) /\
     norm w1 < r /\ norm w2 < r /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     gamma(&0) = mfd_exp (top,atlas) g y (E ** w1) /\
     gamma(&1) = mfd_exp (top,atlas) g y (E ** w2) /\
     (!t. t IN real_interval[&0,&1] ==> gamma t IN mfd_ball (top,atlas) g y r)
     ==> inv(sqrt(&2)) * norm(w1 - w2) <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "param") (CONJUNCTS_THEN2 (LABEL_TAC "img")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "inj")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`; `K:real`]
                P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "bnd") (LABEL_TAC "pb"))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (ball(vec 0:real^N,r)))
                                      (open_set_atlas (ball(vec 0,r)))`
  (LABEL_TAC "osa") THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(ball(vec 0:real^N,r),(\x:real^N. x)) IN open_set_atlas (ball(vec 0,r))`
  (LABEL_TAC "inat") THENL [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `ball(vec 0:real^N,r)`;
                 `\w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)`;
                 `gamma:real->A`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "cc1")
    (LABEL_TAC "lift"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `ball(vec 0:real^N,r)`;
                 `\w:real^N. mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w)`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                 `c:real->real^N`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "pb" (MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) =
                mfd_length atlas g ((\w:real^N. mfd_exp (top,atlas) g y ((E:real^N^N) ** w)) o
                                    (c:real->real^N)) (&0) (&1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[o_THM; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "lift" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real->real^N) (&0) = w1 /\ c (&1) = w2` STRIP_ASSUME_TAC THENL
   [USE_THEN "lift" (MP_TAC o SPEC `&0`) THEN USE_THEN "lift" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL; IN_BALL_0] THEN
    REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,r))`;
                 `open_set_atlas (ball(vec 0:real^N,r))`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                 `c:real->real^N`; `&0`; `&1`;
                 `ball(vec 0:real^N,r)`; `\x:real^N. x`;
                 `inv(&2)`; `&2`; `ball(vec 0:real^N,r)`] GRGD_CHART_LENGTH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:real^N`; `v:real^N`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ball(vec 0:real^N,r)`;
                     `cmp_expmetric (top,atlas) (g:A->real^N^N) y E`;
                     `z:real^N`] RFB_OPEN_SET_METRIC_LOCAL) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "bnd" MATCH_MP_TAC THEN ASM_MESON_TAC[IN_BALL_0];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      USE_THEN "lift" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[dist; SQRT_INV] THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC);;

(* Curves from a point of B(y,r/4) that leave B(y,r) have length >= 3r/4. *)

let P2CU_NCH_CURVE_OUT = prove
 (`!top atlas (g:A->real^N^N) y r gamma t.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     mfd_joinable (top,atlas) y (gamma(&0)) /\
     mfd_dist (top,atlas) g y (gamma(&0)) < r / &4 /\
     t IN real_interval[&0,&1] /\ ~(gamma t IN mfd_ball (top,atlas) g y r)
     ==> &3 * r / &4 <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `t:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `&0`; `t:real`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y ((gamma:real->A) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `r <= mfd_dist (top,atlas) (g:A->real^N^N) y ((gamma:real->A) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~((gamma:real->A) t IN mfd_ball (top,atlas) (g:A->real^N^N) y r)` THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `(gamma:real->A) (&0)`; `(gamma:real->A) t`]
                MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2CU_NCH_LIP_LOWER = prove
 (`!top atlas (g:A->real^N^N) y E r K w1 w2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_orthonormal_frame g y E /\ mfd_inj_ball (top,atlas) g y r /\
     &0 < r /\ &0 <= K /\ K * r pow 2 <= &1 /\
     (!z. z IN mfd_ball (top,atlas) g y r ==> mfd_rm_norm atlas g z <= K) /\
     norm w1 < r / &4 /\ norm w2 < r / &4
     ==> norm(w1 - w2) <=
         sqrt(&2) * mfd_dist (top,atlas) g (mfd_exp (top,atlas) g y (E ** w1))
                                           (mfd_exp (top,atlas) g y (E ** w2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `E:real^N^N`; `r:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "dist") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `norm(w1:real^N) < r /\ norm(w2:real^N) < r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "dist" (MP_TAC o SPEC `w1:real^N`) THEN
  USE_THEN "dist" (MP_TAC o SPEC `w2:real^N`) THEN
  REMOVE_THEN "dist" (K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC P2CU_INV_SQRT2 THEN
  SUBGOAL_THEN
   `inv(sqrt(&2)) * norm(w1 - w2:real^N) <=
    mfd_dist (top,atlas) g (mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w1))
                           (mfd_exp (top,atlas) g y (E ** w2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_DIST_GE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS; MFD_JOINABLE_SYM]; ALL_TAC] THEN
    X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `!t. t IN real_interval[&0,&1] ==>
          (gamma:real->A) t IN mfd_ball (top,atlas) (g:A->real^N^N) y r`
    THENL
     [MATCH_MP_TAC P2CU_NCH_CURVE_IN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `y:A`; `E:real^N^N`; `r:real`; `K:real`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y:A`; `r:real`; `gamma:real->A`; `t:real`]
                    P2CU_NCH_CURVE_OUT) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm(w1 - w2:real^N) < r / &2` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`w1:real^N`; `--w2:real^N`] NORM_TRIANGLE) THEN
        REWRITE_TAC[NORM_NEG; GSYM VECTOR_SUB] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(sqrt(&2)) * norm(w1 - w2:real^N) <= norm(w1 - w2)` ASSUME_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[NORM_POS_LE];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt(&2)`; `inv(sqrt(&2)) * norm(w1 - w2:real^N)`;
                 `mfd_dist (top,atlas) g (mfd_exp (top,atlas) (g:A->real^N^N) y ((E:real^N^N) ** w1))
                                         (mfd_exp (top,atlas) g y (E ** w2))`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[SQRT_POS_LE; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* Uniform normal charts for the sequence: a radius rho and a curvature bound *)
(* K with K rho^2 <= 1 such that eventually every y in B(x k,A) has an       *)
(* injectivity ball of radius rho and |Rm| <= K on B(y,rho), and for every m *)
(* the normal coordinate metrics have C^m distance at most B(m) from the     *)
(* flat metric on ball(0,rho/2) (P2C_GAUGE).                                *)
(* ------------------------------------------------------------------------- *)

let P2CU_FINITE_MAX = prove
 (`!(f:num->num) m. ?N. !l. l <= m ==> f l <= N`,
  GEN_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `(f:num->num) 0` THEN REWRITE_TAC[LE] THEN MESON_TAC[LE_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `MAX N ((f:num->num)(SUC m))` THEN
    REWRITE_TAC[LE] THEN ASM_MESON_TAC[ARITH_RULE `a <= N ==> a <= MAX N b`;
                                       ARITH_RULE `b <= MAX N b`]]);;

let P2CU_CHARTS = prove
 (`!top atlas (h:num->A->real^3^3) x A.
     P2C_REQ_CGT_STATEMENT (:A) /\ p2cu_seq top atlas h x /\ &0 < A
     ==> ?rho K N0. &0 < rho /\ rho < &1 /\ &0 <= K /\ K * rho pow 2 <= &1 /\
           (!k y. N0 <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A
                  ==> mfd_inj_ball (top k,atlas k) (h k) y rho /\
                      (!z. z IN mfd_ball (top k,atlas k) (h k) y rho
                           ==> mfd_rm_norm (atlas k) (h k) z <= K)) /\
           !m. ?B N. !k y E. N <= k /\ y IN mfd_ball (top k,atlas k) (h k) (x k) A /\
                             mfd_orthonormal_frame (h k) y E
                             ==> metric_field (ball(vec 0,rho))
                                   (cmp_expmetric (top k,atlas k) (h k) y E) /\
                                 !w. norm w < rho / &2
                                     ==> lck_dist2 m (\z. mat 1)
                                           (cmp_expmetric (top k,atlas k) (h k) y E) w <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `A:real`] P2CU_INJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `A + &1` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `&0 < A + &1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cf:num->real` (X_CHOOSE_TAC `Nf:num->num`)) THEN
  ABBREV_TAC `K = sqrt(abs((Cf:num->real) 0))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rho = min (i0 / &2) (inv(K + &1))` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < &1 /\ rho <= i0 /\ K * rho pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(K + &1) /\ inv(K + &1) * (K + &1) = &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho /\ rho <= i0 / &2 /\ rho <= inv(K + &1)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `rho * (K + &1) <= &1` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `inv(K + &1) * (K + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
    TRANS_TAC REAL_LE_TRANS `&1 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k y z. (N1:num) + (Nf:num->num) 0 <= k /\ y IN mfd_ball ((top:num->A topology) k,
                                            (atlas:num->((A->bool)#(A->real^3))->bool) k)
                                           ((h:num->A->real^3^3) k) ((x:num->A) k) A /\
            z IN mfd_ball (top k,atlas k) (h k) y rho
            ==> z IN mfd_ball (top k,atlas k) (h k) (x k) (A + &1)`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
                GEN_REWRITE_RULE I [p2cu_seq]) THEN
    MATCH_MP_TAC(SET_RULE `!s t u:A->bool. z IN s /\ s SUBSET t /\ t SUBSET u ==> z IN u`) THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,
                          (atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) y rho` THEN
    EXISTS_TAC `mfd_ball ((top:num->A topology) k,
                          (atlas:num->((A->bool)#(A->real^3))->bool) k)
                         ((h:num->A->real^3^3) k) ((x:num->A) k) (A + rho)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `K:real`; `(N1:num) + (Nf:num->num) 0`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
                GEN_REWRITE_RULE I [p2cu_seq]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `i0:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2C_RM_NORM_LE THEN
      EXISTS_TAC `(top:num->A topology) k` THEN
      ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "K" THEN SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sub" MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(SPECL [`m:num`; `\l. sqrt(abs((Cf:num->real) l))`; `rho:real`; `rho / &2`]
               (REWRITE_RULE[P2C_GAUGE_STATEMENT] (ISPEC `(:A)` P2C_GAUGE))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "gauge")) THEN
  X_CHOOSE_TAC `Nm:num` (SPECL [`Nf:num->num`; `m:num`] P2CU_FINITE_MAX) THEN
  MAP_EVERY EXISTS_TAC [`B:real`; `(N1:num) + (Nf:num->num) 0 + (Nm:num)`] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`; `E:real^3^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o CONJUNCT1 o
              GEN_REWRITE_RULE I [p2cu_seq]) THEN
  SUBGOAL_THEN `mfd_inj_ball ((top:num->A topology) k,
                              (atlas:num->((A->bool)#(A->real^3))->bool) k)
                             ((h:num->A->real^3^3) k) y rho`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `i0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "gauge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET];
    ASM_MESON_TAC[mfd_inj_ball];
    MAP_EVERY X_GEN_TAC [`z:A`; `l:num`] THEN STRIP_TAC THEN
    SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "sub" MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC]]);;

