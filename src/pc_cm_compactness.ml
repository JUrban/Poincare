(* ========================================================================= *)
(* Unit pc_cm_compactness: the chain unit of                                 *)
(* CM_CHAIN_CM_COMPACTNESS_STATEMENT (pc_cm_stmts), Colding-Minicozzi 2008,  *)
(* Prop 2.2 with Prop A.3 and (1.19).                                        *)
(*                                                                           *)
(* First small facts on weak partials, traces and re-indexing.  Then the     *)
(* assembly: CM_COMPACTNESS_STATEMENT follows from the four internal         *)
(* statements of pc_cmc_defs: CMC_XFER (standard chart, rotations),          *)
(* CMC_TIGHT (a rotation making the energy tight at infinity),               *)
(* CMC_PLANAR_BUBBLES (the planar bubble theorem) and CMC_SPHERE (bubbles    *)
(* are maps of S^2, constant or harmonic spheres).  Route: rotate the maps,  *)
(* pass to the standard chart, apply the planar theorem, turn the planar     *)
(* bubbles into maps of S^2, rotate back, drop the constant bubbles (zero    *)
(* trace) and re-index the others by 1..m.  The area is half the trace of G. *)
(* Last the chain theorem CM_CHAIN_CM_COMPACTNESS from CMCX_XFER             *)
(* (pc_cmc_xfer), CMC_TIGHT and CMC_SPHERE (pc_cmc_sphere) and               *)
(* CMC_PLANAR_BUBBLES (pc_cmc_tree).                                         *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;
needs "src/pc_cmc_tree.ml";;
needs "src/pc_cmc_sphere.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Small facts: weak partials and traces of constant maps, re-indexing.      *)
(* ------------------------------------------------------------------------- *)

(* The chosen global weak partial is a.e. any weak partial in L^2.          *)

let CMC_WD_EQ = prove
 (`!(u:real^2->real^K) i v.
     wan_wpd (:real^2) i u v /\ v IN lspace (:real^2) (&2)
     ==> negligible {x | ~(wan_wd (:real^2) i u x = v x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd (:real^2) i (u:real^2->real^K) IN lspace (:real^2) (&2) /\
                wan_wpd (:real^2) i (u:real^2->real^K) (wan_wd (:real^2) i u)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `i:num`; `u:real^2->real^K`;
                 `wan_wd (:real^2) i (u:real^2->real^K)`; `v:real^2->real^K`]
                WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

(* Constant planar maps have zero weak partials, hence zero trace integrals. *)

let CMC_WD_CONST = prove
 (`!(c:real^K) i.
     negligible {x:real^2 | ~(wan_wd (:real^2) i (\x:real^2. c) x = vec 0)}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^2. c:real^K`; `i:num`; `\x:real^2. vec 0:real^K`] CMC_WD_EQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. c:real^K`; `i:num`] WAN_WPD_C1) THEN
    SIMP_TAC[OPEN_UNIV; CONTINUOUSLY_DIFFERENTIABLE_CONST; PARTIAL_DERIVATIVE_CONST];
    MATCH_MP_TAC LSPACE_0 THEN REAL_ARITH_TAC]);;

let CMC_PTR_CONST = prove
 (`!(G:real^K->real^K^K) Q E (c:real^K).
     cmc_ptr G Q E (\x:real^2. c) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_ptr] THEN
  SUBGOAL_THEN
   `integral E (\x:real^2. lift(cmc_tden G Q (\x:real^2. c:real^K) x)) =
    integral E (\x. vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x:real^2 | ~(wan_wd (:real^2) 1 (\x:real^2. c:real^K) x = vec 0)} UNION
                {x:real^2 | ~(wan_wd (:real^2) 2 (\x:real^2. c:real^K) x = vec 0)}` THEN
    REWRITE_TAC[NEGLIGIBLE_UNION_EQ; CMC_WD_CONST] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[cmc_tden; LIFT_EQ; LIFT_NUM] THEN
    SUBGOAL_THEN `cmc_gram (G:real^K->real^K^K) (\x:real^2. c:real^K) x = mat 0`
    (fun th -> REWRITE_TAC[th; DET_0; LIFT_NUM]) THEN
    SIMP_TAC[cmc_gram; CART_EQ; LAMBDA_BETA; MAT_0_COMPONENT] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2] THEN
    ASM_REWRITE_TAC[DOT_LZERO];
    REWRITE_TAC[INTEGRAL_0; DROP_VEC]]);;

(* Re-indexing the non-constant bubbles by 1..m.                             *)

let CMC_REINDEX = prove
 (`!(P:num->bool) m.
     ?n (f:num->num).
        (!k. 1 <= k /\ k <= n ==> f k <= m /\ P(f k)) /\
        !ff. (!i. i <= m /\ ~P i ==> ff i = &0)
            ==> sum(1..n) (\k. ff(f k)) = sum(0..m) ff`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `{i | i <= m /\ (P:num->bool) i}` FINITE_INDEX_NUMSEG) THEN
  SUBGOAL_THEN `FINITE {i | i <= m /\ (P:num->bool) i}` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..m` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`CARD {i | i <= m /\ (P:num->bool) i}`; `f:num->num`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:num->num) k IN {i | i <= m /\ (P:num->bool) i}` MP_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_NUMSEG];
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  X_GEN_TAC `ff:num->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `ff:num->real`;
                 `1..CARD {i | i <= m /\ (P:num->bool) i}`] SUM_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ARITH_TAC; ASM_MESON_TAC[LE_0]]);;

(* ------------------------------------------------------------------------- *)
(* The assembly theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The chart picture of a rotated map of S^2: planar map, energy, area and  *)
(* traces (CMC_XFER: rotation invariance, then the standard chart).          *)

let CMC_ROTATED_FACTS = prove
 (`!S (G:real^K->real^K^K) d (R:real^3^3) (v:real^3->real^K).
     CMC_XFER_STATEMENT (:K) /\ cm_target S G d /\
     orthogonal_matrix R /\ det R = &1 /\ cm_smap S v
     ==> cmc_pmap S (\y. v(R ** stereo2_n_inv y)) /\
         cm_sen G v = wan_gdir (:real^2) G (\y. v(R ** stereo2_n_inv y)) / &2 /\
         cm_sarea G v = cmc_ptr G G (:real^2) (\y. v(R ** stereo2_n_inv y)) / &2 /\
         (!Q:real^K->real^K^K.
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
            (!z. transp(Q z) = Q z)
            ==> cm_strace G Q v = cmc_ptr G Q (:real^2) (\y. v(R ** stereo2_n_inv y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "XC") (CONJUNCTS_THEN2 (LABEL_TAC "XR") ASSUME_TAC)) THEN
  REMOVE_THEN "XR" (MP_TAC o SPECL [`v:real^3->real^K`; `R:real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (LABEL_TAC "TR")))) THEN
  REMOVE_THEN "XC" (MP_TAC o SPEC `\y:real^3. (v:real^3->real^K)(R ** y)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TC")))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Q:real^K->real^K^K` THEN DISCH_TAC THEN
  REMOVE_THEN "TR" (MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
  REMOVE_THEN "TC" (MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

let CMC_SUBSEQ_COMPOSE = prove
 (`!(s:num->num) (t:num->num).
     (!m n. m < n ==> s m < s n) /\ (!m n. m < n ==> t m < t n)
     ==> !j k. j < k ==> s(t j) < s(t k)`,
  MESON_TAC[]);;

let CMC_ASSEMBLY = prove
 (`CMC_XFER_STATEMENT (:K) /\ CMC_TIGHT_STATEMENT (:K) /\
   CMC_PLANAR_BUBBLES_STATEMENT (:K) /\ CMC_SPHERE_STATEMENT (:K)
   ==> CM_COMPACTNESS_STATEMENT (:K)`,
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC(CONJUNCT2 th)) THEN
  REWRITE_TAC[CMC_TIGHT_STATEMENT; CMC_PLANAR_BUBBLES_STATEMENT;
              CMC_SPHERE_STATEMENT; CM_COMPACTNESS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TI")
    (CONJUNCTS_THEN2 (LABEL_TAC "PB") (LABEL_TAC "SP"))) THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN
   `!(u:real^3->real^K) (R:real^3^3).
       orthogonal_matrix R /\ det R = &1 /\ cm_smap S u
       ==> cm_smap S (\y. u(R ** y)) /\
           cm_sen G (\y. u(R ** y)) = cm_sen G u /\
           cm_sarea G (\y. u(R ** y)) = cm_sarea G u /\
           !Q:real^K->real^K^K.
              smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
              (!z. transp(Q z) = Q z)
              ==> cm_strace G Q (\y. u(R ** y)) = cm_strace G Q u`
  (LABEL_TAC "XR") THENL
   [UNDISCH_TAC `CMC_XFER_STATEMENT (:K)` THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(u:real^3->real^K) (R:real^3^3).
       orthogonal_matrix R /\ det R = &1 /\ cm_sharmonic S G u
       ==> cm_sharmonic S G (\y. u(R ** y))`
  (LABEL_TAC "XH") THENL
   [UNDISCH_TAC `CMC_XFER_STATEMENT (:K)` THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "TI" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TI"))) THEN
  REMOVE_THEN "PB" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eB:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PB"))) THEN
  REMOVE_THEN "SP" (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SP") THEN
  EXISTS_TAC `min eT eB` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`e0:real`; `E0:real`; `u:num->real^3->real^K`; `eta:num->real`;
                       `TT:real^K->bool`] THEN
  STRIP_TAC THEN
  (* Tightness after a subsequence s and a rotation R. *)
  REMOVE_THEN "TI" (MP_TAC o SPECL [`e0:real`; `E0:real`; `u:num->real^3->real^K`;
                                    `eta:num->real`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->num` (X_CHOOSE_THEN `R:real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TG")))))) THEN
  MP_TAC(SPEC `R:real^3^3` CMC_ROT_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* The chart pictures of the rotated maps. *)
  SUBGOAL_THEN
   `!j. cmc_pmap S (\y. (u:num->real^3->real^K) ((s:num->num) j) (R ** stereo2_n_inv y)) /\
        cm_sen G (u ((s:num->num) j)) = wan_gdir (:real^2) G (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)) / &2 /\
        cm_sarea G (u ((s:num->num) j)) =
        cmc_ptr G G (:real^2) (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)) / &2 /\
        (!Q:real^K->real^K^K.
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
            (!z. transp(Q z) = Q z)
            ==> cm_strace G Q (u ((s:num->num) j)) =
                cmc_ptr G Q (:real^2) (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)))`
  (LABEL_TAC "CH") THENL
   [GEN_TAC THEN MATCH_MP_TAC CMC_ROTATED_FACTS THEN EXISTS_TAC `d:real` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* The planar bubble theorem. *)
  REMOVE_THEN "PB" (MP_TAC o SPECL
    [`e0:real`; `&2 * E0`; `\j y. (u:num->real^3->real^K) ((s:num->num) j) (R ** stereo2_n_inv y)`;
     `\j. (eta:num->real) ((s:num->num) j)`; `TT:real^K->bool`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC HMD_REALLIM_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CMC_STEREO_SPHERE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN USE_THEN "CH" (STRIP_ASSUME_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `cm_sen G ((u:num->real^3->real^K) ((s:num->num) j)) <= E0` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC
         `cm_sen G ((u:num->real^3->real^K) ((s:num->num) j)) =
          wan_gdir (:real^2) G (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)) / &2` THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC CMC_AH_CHART THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "CH" (STRIP_ASSUME_TAC o SPEC `j:num`) THEN
    SUBGOAL_THEN
     `cm_sen G ((u:num->real^3->real^K) ((s:num->num) j)) - inv(&((s:num->num) j) + &1) <
      cm_sarea G (u ((s:num->num) j))`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&((s:num->num) j) + &1) <= inv(&N)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE; LE_1] THEN
      MP_TAC(ISPEC `s:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `cm_sen G ((u:num->real^3->real^K) ((s:num->num) j)) =
      wan_gdir (:real^2) G (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)) / &2` THEN
    UNDISCH_TAC
     `cm_sarea G ((u:num->real^3->real^K) ((s:num->num) j)) =
      cmc_ptr G G (:real^2) (\y. u ((s:num->num) j) (R ** stereo2_n_inv y)) / &2` THEN
    UNDISCH_TAC `inv(&N) < e / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `m:num`
    (X_CHOOSE_THEN `b:num->real^2->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "BH") (LABEL_TAC "BL")))))) THEN
  (* The bubbles as maps of S^2. *)
  SUBGOAL_THEN
   `?v:num->real^3->real^K.
       !i. i <= m
           ==> cm_smap S (v i) /\ (!y. y IN sphere(vec 0,&1) ==> v i y IN TT) /\
               (!x. v i (stereo2_n_inv x) = b i x) /\
               ((?c. !x. b i x = c) \/ cm_sharmonic S G (v i))`
  (X_CHOOSE_THEN `v:num->real^3->real^K` (LABEL_TAC "VV")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN USE_THEN "SP" MATCH_MP_TAC THEN
    USE_THEN "BH" (MP_TAC o C MATCH_MP (ASSUME `(i:num) <= m`)) THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i Q:real^K->real^K^K.
       i <= m /\
       smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
       (!z. transp(Q z) = Q z)
       ==> cm_strace G Q (\y. (v:num->real^3->real^K) i (transp(R:real^3^3) ** y)) =
           cmc_ptr G Q (:real^2) (b i)`
  (LABEL_TAC "VT") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "VV" (MP_TAC o C MATCH_MP (ASSUME `(i:num) <= m`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
    USE_THEN "XR" (MP_TAC o SPECL [`(v:num->real^3->real^K) i`; `transp(R:real^3^3)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `mat 1:real^3^3`;
                   `(v:num->real^3->real^K) i`] CMC_ROTATED_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; DET_I]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= m
        ==> cm_sarea G (\y. (v:num->real^3->real^K) i (transp(R:real^3^3) ** y)) =
            cmc_ptr G G (:real^2) (b i) / &2`
  (LABEL_TAC "VA") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "VV" (MP_TAC o C MATCH_MP (ASSUME `(i:num) <= m`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
    USE_THEN "XR" (MP_TAC o SPECL [`(v:num->real^3->real^K) i`; `transp(R:real^3^3)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `mat 1:real^3^3`;
                   `(v:num->real^3->real^K) i`] CMC_ROTATED_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; DET_I]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Drop the constant bubbles and re-index. *)
  MP_TAC(ISPECL [`\i. ~(?c:real^K. !x:real^2. (b:num->real^2->real^K) i x = c)`; `m:num`]
                CMC_REINDEX) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `f:num->num`
    (CONJUNCTS_THEN2 (LABEL_TAC "FI") (LABEL_TAC "FS")))) THEN
  SUBGOAL_THEN
   `!i Q. i <= m /\ (?c:real^K. !x:real^2. (b:num->real^2->real^K) i x = c)
          ==> cmc_ptr G Q (:real^2) (b i) = &0`
  (LABEL_TAC "B0") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `c:real^K` o CONJUNCT2) THEN
    SUBGOAL_THEN `(b:num->real^2->real^K) i = \x. c` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; REWRITE_TAC[CMC_PTR_CONST]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\j. (s:num->num) ((t:num->num) j)`; `n:num`;
    `\k y. (v:num->real^3->real^K) ((f:num->num) k) (transp(R:real^3^3) ** y)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMC_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "FI" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `1 <= k /\ k <= n`)) THEN
    USE_THEN "XH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "VV" (MP_TAC o C MATCH_MP (ASSUME `(f:num->num) k <= m`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`k:num`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "FI" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `1 <= k`) (ASSUME `(k:num) <= n`))) THEN
    USE_THEN "VV" (MP_TAC o C MATCH_MP (ASSUME `(f:num->num) k <= m`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    (* areas *)
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\j. cmc_ptr G G (:real^2)
                      (\y. (u:num->real^3->real^K) ((s:num->num)((t:num->num) j)) (R ** stereo2_n_inv y)) *
                    inv(&2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      USE_THEN "CH" (MP_TAC o SPEC `(t:num->num) j`) THEN SIMP_TAC[real_div];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum(1..n) (\k. cm_sarea G (\y. (v:num->real^3->real^K) ((f:num->num) k)
                                       (transp(R:real^3^3) ** y))) =
      sum(0..m) (\i. cmc_ptr G G (:real^2) ((b:num->real^2->real^K) i)) * inv(&2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL] THEN
      USE_THEN "FS" (MP_TAC o SPEC
        `\i. cmc_ptr G G (:real^2) ((b:num->real^2->real^K) i) * inv(&2)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_MUL_LZERO]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      USE_THEN "FI" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `1 <= k /\ k <= n`)) THEN
      USE_THEN "VA" (MP_TAC o C MATCH_MP (ASSUME `(f:num->num) k <= m`)) THEN
      SIMP_TAC[real_div];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_RMUL THEN
    USE_THEN "BL" (MP_TAC o SPEC `G:real^K->real^K^K`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    (* traces *)
    X_GEN_TAC `Q:real^K->real^K^K` THEN STRIP_TAC THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\j. cmc_ptr G Q (:real^2)
                      (\y. (u:num->real^3->real^K) ((s:num->num)((t:num->num) j)) (R ** stereo2_n_inv y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      USE_THEN "CH" (MP_TAC o SPEC `(t:num->num) j`) THEN
      DISCH_THEN(MP_TAC o SPEC `Q:real^K->real^K^K` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum(1..n) (\k. cm_strace G Q (\y. (v:num->real^3->real^K) ((f:num->num) k)
                                         (transp(R:real^3^3) ** y))) =
      sum(0..m) (\i. cmc_ptr G Q (:real^2) ((b:num->real^2->real^K) i))`
    SUBST1_TAC THENL
     [USE_THEN "FS" (MP_TAC o SPEC
        `\i. cmc_ptr G Q (:real^2) ((b:num->real^2->real^K) i)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      USE_THEN "FI" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `1 <= k /\ k <= n`)) THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "BL" (MP_TAC o SPEC `Q:real^K->real^K^K`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The chain theorem.  Of the hypotheses of the chain term the               *)
(* proof uses CM_EPS_REG, CM_REPLACEMENT and CM_REMOVABLE; the transfer to  *)
(* the standard chart (CMCX_XFER) is unconditional.                          *)
(* ------------------------------------------------------------------------- *)

let CM_CHAIN_CM_COMPACTNESS = prove
 (`!kk:K->bool. CM_CHAIN_CM_COMPACTNESS_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CHAIN_CM_COMPACTNESS_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC CMC_ASSEMBLY THEN REWRITE_TAC[CMCX_XFER] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMC_TIGHT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMC_PLANAR_BUBBLES THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMC_SPHERE THEN ASM_REWRITE_TAC[]]);;

let CM_CHAIN_CM_COMPACTNESS_UNIV = prove
 (`CM_CHAIN_CM_COMPACTNESS_STATEMENT (:K)`,
  REWRITE_TAC[CM_CHAIN_CM_COMPACTNESS]);;

