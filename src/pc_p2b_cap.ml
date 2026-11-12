(* ========================================================================= *)
(* Unit pc_p2b_cap (Part 2B, MT Prop 9.79): the cap case of the open form    *)
(* P2_PROP_9_79_OPEN and the volume and ball infrastructure it needs.        *)
(*                                                                           *)
(* - integrals and volumes on a restricted manifold; volumes under a local   *)
(*   diffeomorphism (naturality and comparison);                             *)
(* - the core exit argument; balls with R <= r^-2 in caps; nested balls;     *)
(* - suprema over balls: right continuity, a radius with sup = r^-2;         *)
(* - the ball clause (7) of caps transferred through psi, one ball at a time *)
(*   (P2BC_C7_POINT), with Bishop-Gromov (CMP_RELVOL), and with one constant *)
(*   (P2BC_CLAUSE7);                                                         *)
(* - necks and charts of a cap through psi; source bounds and margins; the   *)
(*   target clauses of a cap;                                                *)
(* - the common core P2BC_OPEN_CAP_COMMON, the cap case P2BC_OPEN_CAP and    *)
(*   the open form of MT Prop 9.79.                                          *)
(* ========================================================================= *)

needs "src/pc_p2b_979s.ml";;
needs "src/pc_grg_area.ml";;
needs "src/pc_cmp_defs.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_cmp_relvol.ml";;
needs "src/pc_rfa_slcut.ml";;

prioritize_real();;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Integrals on the restricted manifold (subtopology top W, restrict_atlas  *)
(* atlas W) with the restricted metric agree with those on the manifold,    *)
(* for sets S inside the open set W.                                         *)
(* ------------------------------------------------------------------------- *)

let P2BC_INTEGRAND_RESTRICT = prove
 (`!top atlas (g:A->real^N^N) W f (U:A->bool) (phi:A->real^N) y.
     smooth_manifold_atlas top atlas /\ open_in top W /\ (U,phi) IN atlas /\
     y IN IMAGE phi (U INTER W)
     ==> mfd_chart_integrand (restrict_atlas atlas W) (restrict_metric atlas W g) f
                             (U INTER W,phi) y =
         mfd_chart_integrand atlas g f (U,phi) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[mfd_chart_integrand; mfd_density] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `x:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `g:A->real^N^N`; `x:A`]
                METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Two chart partitions with the same pieces and the same chart integrands  *)
(* on each piece give the same integral data.                               *)

let P2BC_PARTITION_DATA_EQ = prove
 (`!(c:num->(A->bool)#(A->real^N)) (c':num->(A->bool)#(A->real^N)) E
    (Fa:num->real^N->real^1) Fb v.
     (!n. IMAGE (SND(c n)) (E n) = IMAGE (SND(c' n)) (E n) /\
          !y. y IN IMAGE (SND(c n)) (E n) ==> Fa n y = Fb n y)
     ==> ((!n. Fa n absolutely_integrable_on IMAGE (SND(c n)) (E n)) /\
          real_summable (from 0)
            (\n. drop(integral (IMAGE (SND(c n)) (E n)) (\y. lift(norm(Fa n y))))) /\
          ((\n. drop(integral (IMAGE (SND(c n)) (E n)) (Fa n))) real_sums v) (from 0) <=>
          (!n. Fb n absolutely_integrable_on IMAGE (SND(c' n)) (E n)) /\
          real_summable (from 0)
            (\n. drop(integral (IMAGE (SND(c' n)) (E n)) (\y. lift(norm(Fb n y))))) /\
          ((\n. drop(integral (IMAGE (SND(c' n)) (E n)) (Fb n))) real_sums v) (from 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) (E n))
                       (\y. lift(norm((Fa:num->real^N->real^1) n y))))) =
    (\n. drop(integral (IMAGE (SND((c':num->(A->bool)#(A->real^N)) n)) (E n))
                       (\y. lift(norm((Fb:num->real^N->real^1) n y))))) /\
    (\n. drop(integral (IMAGE (SND(c n)) (E n)) (Fa n))) =
    (\n. drop(integral (IMAGE (SND(c' n)) (E n)) (Fb n)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THENL
   [EXISTS_TAC `(Fa:num->real^N->real^1) n`; EXISTS_TAC `(Fb:num->real^N->real^1) n`] THEN
  ASM_SIMP_TAC[]);;

let P2BC_INTEGRAL_RESTRICT = prove
 (`!top atlas (g:A->real^N^N) W f S v.
     smooth_manifold_atlas top atlas /\ open_in top W /\ S SUBSET W
     ==> (mfd_has_integral (subtopology top W,restrict_atlas atlas W)
            (restrict_metric atlas W g) f S v <=>
          mfd_has_integral (top,atlas) g f S v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_integral] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c':num->(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PE") (LABEL_TAC "PDU")) THEN
    SUBGOAL_THEN
     `?c:num->(A->bool)#(A->real^N).
        !n. ~((E:num->A->bool) n = {})
            ==> c n IN atlas /\ c' n = (FST(c n) INTER W,SND(c n))`
    (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)` (LABEL_TAC "CC")) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
      ASM_CASES_TAC `(E:num->A->bool) n = {}` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PE" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
      REWRITE_TAC[ASSUME `~((E:num->A->bool) n = {})`] THEN
      SPEC_TAC(`(c':num->(A->bool)#(A->real^N)) n`,`k:(A->bool)#(A->real^N)`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
      MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
      DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(U0:A->bool,psi:A->real^N)` THEN ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. ~((E:num->A->bool) n = {})
          ==> (c:num->(A->bool)#(A->real^N)) n IN atlas /\
              E n SUBSET FST(c n) INTER W /\
              (c':num->(A->bool)#(A->real^N)) n = (FST(c n) INTER W,SND(c n))`
     (LABEL_TAC "CE") THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "CC" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `n:num` th)
        (ASSUME `~((E:num->A->bool) n = {})`))) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "PE" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `n:num`) THEN
      REWRITE_TAC[ASSUME `(c':num->(A->bool)#(A->real^N)) n =
                          (FST((c:num->(A->bool)#(A->real^N)) n) INTER W,SND(c n))`; FST];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
    SUBGOAL_THEN
     `!n. IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n) =
          IMAGE (SND((c':num->(A->bool)#(A->real^N)) n)) (E n) /\
          !y. y IN IMAGE (SND(c n)) (E n)
              ==> mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y =
                  mfd_chart_integrand (restrict_atlas atlas W) (restrict_metric atlas W g) f
                                      (c' n) y`
    (LABEL_TAC "PIECE") THENL
     [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `(E:num->A->bool) n = {}` THENL
       [ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]; ALL_TAC] THEN
      USE_THEN "CE" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `n:num` th)
        (ASSUME `~((E:num->A->bool) n = {})`))) THEN
      ASM_REWRITE_TAC[SND] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `W:A->bool`; `f:A->real`;
                     `FST((c:num->(A->bool)#(A->real^N)) n)`;
                     `SND((c:num->(A->bool)#(A->real^N)) n)`;
                     `y:real^N`] P2BC_INTEGRAND_RESTRICT) THEN
      REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)` THEN
      UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n) INTER W` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_chart_partition] THEN USE_THEN "PDU" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `(E:num->A->bool) n = {}` THENL
       [REWRITE_TAC[ASSUME `(E:num->A->bool) n = {}`; EMPTY_SUBSET; IMAGE_CLAUSES;
                    LEBESGUE_MEASURABLE_EMPTY];
        ALL_TAC] THEN
      USE_THEN "CE" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `n:num` th)
        (ASSUME `~((E:num->A->bool) n = {})`))) THEN
      REWRITE_TAC[ASSUME `(c:num->(A->bool)#(A->real^N)) n IN atlas`] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n) INTER W` THEN
        SET_TAC[];
        USE_THEN "PE" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `n:num`) THEN
        REWRITE_TAC[ASSUME `(c':num->(A->bool)#(A->real^N)) n =
                            (FST((c:num->(A->bool)#(A->real^N)) n) INTER W,SND(c n))`; SND]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:num->(A->bool)#(A->real^N)`; `c':num->(A->bool)#(A->real^N)`;
                   `E:num->A->bool`;
                   `\n. mfd_chart_integrand atlas (g:A->real^N^N) f
                          ((c:num->(A->bool)#(A->real^N)) n)`;
                   `\n. mfd_chart_integrand (restrict_atlas atlas W)
                          (restrict_metric atlas W (g:A->real^N^N)) f
                          ((c':num->(A->bool)#(A->real^N)) n)`;
                   `v:real`] P2BC_PARTITION_DATA_EQ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [USE_THEN "PIECE" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PE") (LABEL_TAC "PDU")) THEN
    SUBGOAL_THEN `!n. (E:num->A->bool) n SUBSET W` (LABEL_TAC "EW") THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:A->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "PDU" (SUBST1_TAC o SYM o CONJUNCT2) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?c':num->(A->bool)#(A->real^N).
        !n. c' n = (FST((c:num->(A->bool)#(A->real^N)) n) INTER W,SND(c n))`
    (X_CHOOSE_THEN `c':num->(A->bool)#(A->real^N)` (LABEL_TAC "CD")) THENL
     [EXISTS_TAC `\n. (FST((c:num->(A->bool)#(A->real^N)) n) INTER W,SND(c n))` THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c':num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
    SUBGOAL_THEN
     `!n. IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n) =
          IMAGE (SND((c':num->(A->bool)#(A->real^N)) n)) (E n) /\
          !y. y IN IMAGE (SND(c n)) (E n)
              ==> mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y =
                  mfd_chart_integrand (restrict_atlas atlas W) (restrict_metric atlas W g) f
                                      (c' n) y`
    (LABEL_TAC "PIECE") THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "CD" (fun th -> REWRITE_TAC[th; SND]) THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_CASES_TAC `(E:num->A->bool) n = {}` THENL
       [UNDISCH_TAC `y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)` THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `W:A->bool`; `f:A->real`;
                     `FST((c:num->(A->bool)#(A->real^N)) n)`;
                     `SND((c:num->(A->bool)#(A->real^N)) n)`;
                     `y:real^N`] P2BC_INTEGRAND_RESTRICT) THEN
      REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PE" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[ASSUME `~((E:num->A->bool) n = {})`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)` THEN
      USE_THEN "EW" (MP_TAC o SPEC `n:num`) THEN
      UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_chart_partition] THEN USE_THEN "PDU" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `n:num` THEN USE_THEN "CD" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
      ASM_CASES_TAC `(E:num->A->bool) n = {}` THENL
       [REWRITE_TAC[ASSUME `(E:num->A->bool) n = {}`; EMPTY_SUBSET; IMAGE_CLAUSES;
                    LEBESGUE_MEASURABLE_EMPTY];
        ALL_TAC] THEN
      USE_THEN "PE" (STRIP_ASSUME_TAC o
        REWRITE_RULE[ASSUME `~((E:num->A->bool) n = {})`] o SPEC `n:num`) THEN
      REWRITE_TAC[ASSUME `~((E:num->A->bool) n = {})`;
        ASSUME `lebesgue_measurable (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                           ((E:num->A->bool) n))`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
        EXISTS_TAC `FST((c:num->(A->bool)#(A->real^N)) n)` THEN
        REWRITE_TAC[PAIR; ASSUME `(c:num->(A->bool)#(A->real^N)) n IN atlas`];
        USE_THEN "EW" (MP_TAC o SPEC `n:num`) THEN
        UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:num->(A->bool)#(A->real^N)`; `c':num->(A->bool)#(A->real^N)`;
                   `E:num->A->bool`;
                   `\n. mfd_chart_integrand atlas (g:A->real^N^N) f
                          ((c:num->(A->bool)#(A->real^N)) n)`;
                   `\n. mfd_chart_integrand (restrict_atlas atlas W)
                          (restrict_metric atlas W (g:A->real^N^N)) f
                          ((c':num->(A->bool)#(A->real^N)) n)`;
                   `v:real`] P2BC_PARTITION_DATA_EQ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [USE_THEN "PIECE" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Volumes under a local diffeomorphism psi : U -> U' (onto an open set):   *)
(* the volume of IMAGE psi S is the volume of S for the pullback metric on  *)
(* the restricted manifold, and C^0 comparison of the pullback with g      *)
(* compares the volumes (MFD_HAS_VOLUME_COMPARE_QF on the restricted        *)
(* manifold).  P2BC_FRECHET_LOCAL is GEOI_FRECHET_DERIVATIVE_LOCAL of      *)
(* pc_geo_lisom (whose closure has 17 further units).                       *)
(* ------------------------------------------------------------------------- *)

let P2BC_VOLUME_RESTRICT = prove
 (`!top atlas (g:A->real^N^N) W S v.
     smooth_manifold_atlas top atlas /\ open_in top W /\ S SUBSET W
     ==> (mfd_has_volume (subtopology top W,restrict_atlas atlas W)
            (restrict_metric atlas W g) S v <=>
          mfd_has_volume (top,atlas) g S v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_volume] THEN
  MATCH_MP_TAC P2BC_INTEGRAL_RESTRICT THEN ASM_REWRITE_TAC[]);;

let P2BC_RESTRICT_FACTS = prove
 (`!top atlas top' atlas' (U:A->bool) (U':B->bool) psi psi'.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
     mfd_diffeo top atlas U top' atlas' U' psi psi'
     ==> smooth_manifold_atlas (subtopology top U) (restrict_atlas atlas U) /\
         smooth_manifold_atlas (subtopology top' U') (restrict_atlas atlas' U') /\
         topspace(subtopology top U) = U /\ topspace(subtopology top' U') = U' /\
         mfd_diffeo (subtopology top U) (restrict_atlas atlas U)
                    (topspace(subtopology top U))
                    (subtopology top' U') (restrict_atlas atlas' U')
                    (topspace(subtopology top' U')) psi psi'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  SUBGOAL_THEN `topspace(subtopology top (U:A->bool)) = U /\
                topspace(subtopology top' (U':B->bool)) = U'`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `U':B->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`]
                APX_MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

let P2BC_VOLUME_PB = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) S v.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U
     ==> (mfd_has_volume (top',atlas') g' (IMAGE psi S) v <=>
          mfd_has_volume (subtopology top U,restrict_atlas atlas U)
            (mfd_pullback_metric (restrict_atlas atlas U) (restrict_atlas atlas' U') psi
               (restrict_metric atlas' U' g')) S v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas' U')
                  (restrict_metric atlas' U' (g':B->real^N^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) S SUBSET U'` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (psi:A->B) U` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `U':B->bool`; `IMAGE (psi:A->B) S`; `v:real`]
                P2BC_VOLUME_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_ISOMETRY THEN EXISTS_TAC `psi':B->A` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas atlas U)
      (mfd_pullback_metric (restrict_atlas atlas U) (restrict_atlas atlas' U') (psi:A->B)
         (restrict_metric atlas' U' (g':B->real^N^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `subtopology top' (U':B->bool)`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]);;

let P2BC_FRECHET_LOCAL = prove
 (`!(f:real^M->real^N) h s x.
        open s /\ x IN s /\ (!y. y IN s ==> f y = h y)
        ==> frechet_derivative f (at x) = frechet_derivative h (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ !y:real^M. dist(y,x) < d ==> (f:real^M->real^N) y = h y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `h:real^M->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]);;

let P2BC_METRIC_LOCAL_AT_TRANS = prove
 (`!top atlas (U0:A->bool) (phi0:A->real^N) (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ (U0,phi0) IN atlas /\ x IN U0
     ==> metric_local atlas (U0,phi0) G (phi0 x) =
         transp(matrix(frechet_derivative (chart_trans (U0,phi0) (chart_at atlas x))
                                          (at (phi0 x)))) ** G x **
         matrix(frechet_derivative (chart_trans (U0,phi0) (chart_at atlas x))
                                   (at (phi0 x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U0:A->bool,phi0:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `G:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U0:A->bool`; `phi0:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `G:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `chart_trans (U0:A->bool,phi0:A->real^N) (V,psi) (phi0 x) = psi x`
  SUBST1_TAC THENL
   [REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U0:A->bool,phi0:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

let P2BC_RPB_CHART = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g:A->real^N^N) (g':B->real^N^N) x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ x IN U
     ==> ?J. mfd_pullback_metric (restrict_atlas atlas U) (restrict_atlas atlas' U') psi
               (restrict_metric atlas' U' g') x =
             transp J ** mfd_pullback_metric atlas atlas' psi g' x ** J /\
             restrict_metric atlas U g x = transp J ** g x ** J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:A->B) x IN U'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:A->B) U SUBSET U'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`; `x:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` (X_CHOOSE_THEN `phi0:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `U':B->bool`;
                 `(psi:A->B) x`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:B->bool` (X_CHOOSE_THEN `chi0:B->real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `matrix(frechet_derivative (chart_trans (U0:A->bool,phi0:A->real^N)
                       (chart_at atlas (x:A))) (at (phi0 x)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[restrict_metric] THEN
    ASM_REWRITE_TAC[SND] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U0:A->bool`; `phi0:A->real^N`; `U:A->bool`; `g:A->real^N^N`; `x:A`]
                  MFDR_METRIC_LOCAL_RESTRICT_CHART) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P2BC_METRIC_LOCAL_AT_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) U`;
                 `mfd_pullback_metric (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) U)
                    (restrict_atlas (atlas':((B->bool)#(B->real^N))->bool) U')
                    (psi:A->B) (restrict_metric atlas' U' (g':B->real^N^N))`; `x:A`]
                METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) U`;
                 `subtopology top' (U':B->bool)`;
                 `restrict_atlas (atlas':((B->bool)#(B->real^N))->bool) U'`;
                 `psi:A->B`; `psi':B->A`; `restrict_metric atlas' U' (g':B->real^N^N)`;
                 `U0 INTER U:A->bool`; `phi0:A->real^N`; `V0 INTER U':B->bool`;
                 `chi0:B->real^N`; `x:A`] MFD_PULLBACK_METRIC_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_RESTRICT_ATLAS] THEN CONJ_TAC THENL
     [EXISTS_TAC `U0:A->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `V0:B->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U0:A->bool`; `phi0:A->real^N`;
                 `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)`; `x:A`]
                P2BC_METRIC_LOCAL_AT_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `psi:A->B`; `psi':B->A`; `g':B->real^N^N`;
                 `U0:A->bool`; `phi0:A->real^N`; `V0:B->bool`; `chi0:B->real^N`;
                 `U:A->bool`; `U':B->bool`; `x:A`] P2B9S_PB_LOCAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `frechet_derivative ((chi0:B->real^N) o (psi:A->B) o chart_inv (U0 INTER U,phi0))
                       (at ((phi0:A->real^N) x)) =
    frechet_derivative (chi0 o psi o chart_inv (U0,phi0)) (at (phi0 x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BC_FRECHET_LOCAL THEN
    EXISTS_TAC `IMAGE (phi0:A->real^N) (U0 INTER U)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN EXISTS_TAC `top:A topology` THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U0:A->bool`; `phi0:A->real^N`; `U:A->bool`; `z:A`]
                    MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REFL_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U0:A->bool`; `phi0:A->real^N`; `U:A->bool`; `x:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `V0:B->bool`; `chi0:B->real^N`; `U':B->bool`; `g':B->real^N^N`;
                 `(psi:A->B) x`] METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let P2BC_QF_CONG = prove
 (`!(J:real^N^N) (M:real^N^N) (w:real^N).
     w dot ((transp J ** M ** J) ** w) = (J ** w) dot (M ** (J ** w))`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P2BC_VOLUME_PB_COMPARE = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' S v v' lam.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\ &0 <= lam /\
     mfd_has_volume (top,atlas) g S v /\
     mfd_has_volume (top',atlas') g' (IMAGE psi S) v'
     ==> ((!y w. y IN S
                 ==> w dot (mfd_pullback_metric atlas atlas' psi g' y ** w) <=
                     lam * (w dot (g y ** w)))
          ==> v' <= lam * sqrt lam * v) /\
         ((!y w. y IN S
                 ==> w dot (g y ** w) <=
                     lam * (w dot (mfd_pullback_metric atlas atlas' psi g' y ** w)))
          ==> v <= lam * sqrt lam * v')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`] P2BC_RESTRICT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = mfd_pullback_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)
                     (restrict_atlas (atlas':((B->bool)#(B->real^3))->bool) U')
                     (psi:A->B) (restrict_metric atlas' U' (g':B->real^3^3))` THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas' U') (restrict_metric atlas' U' (g':B->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (h1:A->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `subtopology top' (U':B->bool)`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas U) (restrict_metric atlas U (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (subtopology top U,restrict_atlas atlas U)
                  (restrict_metric atlas U (g:A->real^3^3)) S v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `U:A->bool`; `S:A->bool`; `v:real`]
                  P2BC_VOLUME_RESTRICT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (subtopology top U,restrict_atlas atlas U) (h1:A->real^3^3) S v'`
  ASSUME_TAC THENL
   [EXPAND_TAC "h1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^3^3`;
                   `S:A->bool`; `v':real`] P2BC_VOLUME_PB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> ?J. (h1:A->real^3^3) y =
                transp J ** mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** J /\
                restrict_metric atlas U (g:A->real^3^3) y = transp J ** g y ** J`
  (LABEL_TAC "J") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXPAND_TAC "h1" THEN
    MATCH_MP_TAC P2BC_RPB_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THENL
   [MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                          `h1:A->real^3^3`; `restrict_metric atlas U (g:A->real^3^3)`; `S:A->bool`];
    MAP_EVERY EXISTS_TAC [`subtopology top (U:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`;
                          `restrict_metric atlas U (g:A->real^3^3)`; `h1:A->real^3^3`; `S:A->bool`]] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:A) IN S`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^3^3` (CONJUNCTS_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[P2BC_QF_CONG] THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The core exit argument and balls in caps. A C^1 curve from the closed     *)
(* core of a cap to a point outside a set W containing the closed core and   *)
(* the boundary neck e meets the central sphere of e (the frontier of the    *)
(* closed core lies there by APX_BALL_CORE_TOP and APX_TWISTED_CORE_TOP) and *)
(* from there needs length at least sqrt(1 - eps) R(z)^(-1/2) / eps to leave *)
(* the neck (APX_NECK_EXIT).  A ball B(y,r) centred in the closed core with  *)
(* R <= r^-2 on it keeps its curves of length below 2 r (up to the neck      *)
(* margin) inside W, and its closed ball lies in W (P2BC_SC_CURVES_STAY,     *)
(* P2BC_SC_CBALL_IN).  The source version P2BC_SRC_CURVES_STAY reads the     *)
(* condition in a target manifold through a local diffeomorphism psi : U ->  *)
(* U'.  The balls of the two manifolds are nested through psi                *)
(* (P2BC_BALL_IMAGE_IN, P2BC_BALL_PREIMAGE_IN).                              *)
(* ========================================================================= *)

let P2BC_DIST_APPROX = prove
 (`!top atlas (g:A->real^N^N) x y h.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) x y /\ &0 < h
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) < mfd_dist (top,atlas) g x y + h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y}`;
                 `mfd_dist (top,atlas) (g:A->real^N^N) x y + h`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y` THEN
      REWRITE_TAC[mfd_joinable] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)` THEN
      EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN X_GEN_TAC `L:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC GRGD_LENGTHS_POS_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `x:A`; `y:A`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM mfd_dist] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_MESON_TAC[]]);;

let P2BC_CURVE_IMAGE_CONNECTED = prove
 (`!top atlas (gamma:real->A) a b.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
     ==> connected_in top (IMAGE gamma (real_interval[a,b]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                  CONNECTED_IN_EUCLIDEANREAL_INTERVAL]);;

let P2BC_CURVE_MEETS_FRONTIER = prove
 (`!top atlas (gamma:real->A) a b S.
     mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
     gamma a IN S /\ ~(gamma b IN S)
     ==> ?t. t IN real_interval[a,b] /\ gamma t IN top frontier_of S`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BC_CURVE_IMAGE_CONNECTED) THEN DISCH_TAC THEN
  SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `IMAGE (gamma:real->A) (real_interval[a,b])`;
                 `S:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN CONJ_TAC THENL
     [EXISTS_TAC `(gamma:real->A) a`; EXISTS_TAC `(gamma:real->A) b`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; EXISTS_IN_IMAGE] THEN
    MESON_TAC[]]);;

let P2BC_CORE_EXIT = prove
 (`!top atlas (g:A->real^3^3) eps z e Yc W (gamma:real->A) a b.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ eps < &1 /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET W /\ IMAGE e (rfs_neck_dom eps) SUBSET W /\
     mfd_c1_curve (top,atlas) gamma a b /\
     gamma a IN top closure_of Yc /\ ~(gamma b IN W)
     ==> ?t. t IN real_interval[a,b] /\ gamma t IN IMAGE e (sphere(vec 0,&1)) /\
             sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps
             <= mfd_length atlas g gamma t b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `top closure_of (Yc:A->bool)`]
                P2BC_CURVE_MEETS_FRONTIER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN IMAGE e (sphere(vec 0:real^3,&1))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(rand(concl th)) = false &&
    can (find_term ((=) `t:real`)) (concl th) &&
    can (find_term ((=) `sphere(vec 0:real^3,&1)`)) (concl th)) o
    REWRITE_RULE[IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(y:real^3) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; apx_sval] THEN SIMP_TAC[LOG_1; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `y:real^3`;
                 `gamma:real->A`; `t:real`; `b:real`] APX_NECK_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_MESON_TAC[IN_REAL_INTERVAL];
      ASM SET_TAC[]];
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO]]);;

let P2BC_SC_ARITH = prove
 (`!eps r rho Rz L c m.
     &0 < eps /\ eps <= &1 / &4 /\ &0 < Rz /\ &0 < r /\ &0 < c /\ &0 <= m /\
     c * m pow 2 <= &8 /\
     L = sqrt(&1 - eps) * inv(sqrt Rz) * inv eps /\
     Rz / c <= inv(r pow 2) /\ L < rho /\ rho <= m * r
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `eps <= &1 / &4 ==> &0 <= &1 - eps`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 * eps pow 2 * Rz = &1 - eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE;
                 REAL_ARITH `eps <= &1 / &4 ==> &0 <= &1 - eps`] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(Rz = &0) /\ ~(eps = &0)
      ==> ((a:real) * inv Rz * inv(eps pow 2)) * eps pow 2 * Rz = a`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 < m pow 2 * r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * Rz <= c` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`Rz / c`; `inv(r pow 2)`; `r pow 2`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[real_div; REAL_ARITH `(Rz * inv c) * r = (r * Rz) * inv c`] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 * Rz < &8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(m pow 2 * r pow 2) * Rz` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m pow 2 * c` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - eps < &8 * eps pow 2` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `&1 - eps`)) THEN
    REWRITE_TAC[REAL_ARITH `L * e * R = (L * R) * e`] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 <= (&1 / &4) * eps` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BC_SC_CURVES_STAY = prove
 (`!top atlas (g:A->real^3^3) eps z e Yc W y r rho (gamma:real->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g w) /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET W /\ IMAGE e (rfs_neck_dom eps) SUBSET W /\
     y IN top closure_of Yc /\ &0 < r /\
     (!q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= inv(r pow 2)) /\
     rho <= &2 * r /\
     rho - r < sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y /\
     mfd_length atlas g gamma (&0) (&1) < rho
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) (z:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `L = sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (z:A))) * inv eps` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`;
                 `W:A->bool`; `gamma:real->A`; `&0`; `s:real`] P2BC_CORE_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `t:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `t:real`; `s:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `t:real`] MFD_LENGTH_POS_LE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `s:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN mfd_ball (top,atlas) (g:A->real^3^3) y r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    UNDISCH_TAC `(gamma:real->A) (&0) = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^3^3) gamma (&0) t` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BC_SC_ARITH THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `r:real`; `rho:real`;
                        `mfd_scalar atlas (g:A->real^3^3) z`; `L:real`; `&2`; `&2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) (gamma(t:real))` THEN
    ASM_SIMP_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2BC_SC_CBALL_IN = prove
 (`!top atlas (g:A->real^3^3) eps z e Yc W y r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g w) /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET W /\ IMAGE e (rfs_neck_dom eps) SUBSET W /\
     y IN top closure_of Yc /\ &0 < r /\
     (!q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= inv(r pow 2))
     ==> mfd_cball (top,atlas) g y r SUBSET W`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN
  X_GEN_TAC `q:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) (z:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `L = sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (z:A))) * inv eps` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `q:A`; `min r L / &2`] P2BC_DIST_APPROX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`;
                 `W:A->bool`; `y:A`; `r:real`; `r + min r L / &2`; `gamma:real->A`]
                P2BC_SC_CURVES_STAY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL]]);;

let P2BC_DIST_IN_SHORT = prove
 (`!top atlas (g:A->real^N^N) W y q rho.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y /\
              mfd_length atlas g gamma (&0) (&1) < rho
              ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN W) /\
     mfd_joinable (top,atlas) y q /\ mfd_dist (top,atlas) g y q < rho
     ==> mfd_joinable_in (top,atlas) W y q /\
         mfd_dist_in (top,atlas) g W y q <= mfd_dist (top,atlas) g y q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!h. &0 < h /\ mfd_dist (top,atlas) (g:A->real^N^N) y q + h <= rho
        ==> mfd_joinable_in (top,atlas) W y q /\
            mfd_dist_in (top,atlas) g W y q < mfd_dist (top,atlas) g y q + h`
  ASSUME_TAC THENL
   [X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `q:A`; `h:real`] P2BC_DIST_APPROX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!s. &0 <= s /\ s <= &1 ==> (gamma:real->A) s IN W` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `gamma:real->A` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `W:A->bool`; `gamma:real->A`; `&0`; `&1`]
                    MFD_DIST_IN_LE_LENGTH) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `rho - mfd_dist (top,atlas) (g:A->real^N^N) y q`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `min (rho - mfd_dist (top,atlas) (g:A->real^N^N) y q)
         (mfd_dist_in (top,atlas) g W y q - mfd_dist (top,atlas) g y q)`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
                    REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let P2BC_SRC_CURVES_STAY = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    eps z e Yc y0 r rho lam (gamma:real->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     y0 IN top closure_of Yc /\ &0 < r /\ &1 <= lam /\
     (!q. q IN mfd_ball (top',atlas') g' (psi y0) r
          ==> mfd_scalar atlas' g' q <= inv(r pow 2)) /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                lam * (v dot (g y ** v))) /\
     rho <= &5 / &4 * r /\
     sqrt lam * (rho - sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps) <= r /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y0 /\
     mfd_length atlas g gamma (&0) (&1) < rho
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) (z:A)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `U:A->bool`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) (z:A))) * inv eps` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`;
                 `U:A->bool`; `gamma:real->A`; `&0`; `t1:real`] P2BC_CORE_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN U` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t < t1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN U)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `t:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `t:real`; `t1:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `t:real`] MFD_LENGTH_POS_LE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `t1:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B)((gamma:real->A) t) IN mfd_ball (top',atlas') (g':B->real^3^3) (psi y0) r`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `t = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`)) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `g':B->real^3^3`;
                   `gamma:real->A`; `&0`; `t:real`] P2B9S_PB_LENGTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(psi:A->B) y0 = (psi o gamma) (&0) /\
                  (psi:A->B) ((gamma:real->A) t) = (psi o gamma) t`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas' (g':B->real^3^3) ((psi:A->B) o gamma) (&0) t` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sqrt lam * mfd_length atlas (g:A->real^3^3) gamma (&0) t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_LENGTH_COMPARE THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`u:real`; `v:real^3`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt lam * (rho - L)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BC_SC_ARITH THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `r:real`; `rho:real`;
                        `mfd_scalar atlas (g:A->real^3^3) z`; `L:real`; `&4`; `&5 / &4`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B)(gamma(t:real)))` THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2BC_BALL_IMAGE_IN = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    y0 rho r lam q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     (!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y0 /\
              mfd_length atlas g gamma (&0) (&1) < rho
              ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                lam * (v dot (g y ** v))) /\
     &0 < lam /\ sqrt lam * rho <= r /\
     y0 IN U /\ q IN mfd_ball (top,atlas) g y0 rho
     ==> psi q IN mfd_ball (top',atlas') g' (psi y0) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  UNDISCH_TAC `(q:A) IN mfd_ball (top,atlas) (g:A->real^3^3) y0 rho` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `U:A->bool`; `y0:A`; `q:A`; `rho:real`]
                P2BC_DIST_IN_SHORT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `U:A->bool`; `lam:real`; `y0:A`; `q:A`] P2B9S_DIST_IN_PB_LE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN
    EXISTS_TAC `IMAGE (psi:A->B) U` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `IMAGE (psi:A->B) U`; `(psi:A->B) y0`; `(psi:A->B) q`]
                MFD_DIST_LE_DIST_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt lam * mfd_dist (top,atlas) (g:A->real^3^3) y0 q < sqrt lam * rho`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt lam * mfd_dist_in (top,atlas) (g:A->real^3^3) U y0 q <=
                sqrt lam * mfd_dist (top,atlas) g y0 q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BC_BALL_PREIMAGE_IN = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    y0 r lam q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     (!gamma. mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = psi y0 /\
              mfd_length atlas' g' gamma (&0) (&1) < r
              ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U') /\
     (!y v. y IN U
            ==> v dot (g y ** v) <=
                lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     &0 < lam /\ y0 IN U /\ q IN mfd_ball (top',atlas') g' (psi y0) r
     ==> q IN U' /\ psi' q IN mfd_ball (top,atlas) g y0 (sqrt lam * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  UNDISCH_TAC `(q:B) IN mfd_ball (top',atlas') (g':B->real^3^3) ((psi:A->B) y0) r` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `U':B->bool`; `(psi:A->B) y0`; `q:B`; `r:real`]
                P2BC_DIST_IN_SHORT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:B) IN U'` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_joinable_in (top',atlas':((B->bool)#(B->real^3))->bool) U' ((psi:A->B) y0) (q:B)` THEN
    REWRITE_TAC[mfd_joinable_in] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(psi':B->A) q IN U /\ (psi:A->B) (psi' q) = q` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `U:A->bool`; `lam:real`; `y0:A`; `(psi':B->A) q`] P2B9S_DIST_IN_PB_GE) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `U:A->bool`; `y0:A`; `(psi':B->A) q`]
                MFD_DIST_LE_DIST_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt lam` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt lam * mfd_dist (top',atlas') (g':B->real^3^3) (psi(y0:A)) q <
                sqrt lam * r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt lam * mfd_dist_in (top',atlas') (g':B->real^3^3) U' (psi(y0:A)) q <=
                sqrt lam * mfd_dist (top',atlas') g' (psi y0) q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Suprema over balls.  A continuous function is uniformly continuous for    *)
(* the Riemannian distance on a compact set (P2BC_UNIF_CONT, through         *)
(* mfd_metric); lengths along a C^1 curve take every intermediate value      *)
(* (P2BC_LENGTH_IVT); hence the supremum over the open ball B(y0,r) is right *)
(* continuous in r while the balls stay in a compact set                     *)
(* (P2BC_BALL_RIGHT_CONT), and a radius r0 with sup over B(y0,r0) = r0^-2    *)
(* exists between a radius where the sup is at most r^-2 and one where it    *)
(* exceeds it (P2BC_EXACT_RADIUS).  This is the step that lets the ball      *)
(* clause (7) of a cap be applied at a radius near a given one.              *)
(* ========================================================================= *)

let P2BC_UNIF_CONT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) K y0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ continuous_map (top,euclideanreal) f
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !p q. p IN K /\ q IN K /\ mfd_joinable (top,atlas) y0 p /\
                           mfd_joinable (top,atlas) y0 q /\
                           mfd_dist (top,atlas) g p q < d
                           ==> abs(f p - f q) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed_in top {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y0 y}` ASSUME_TAC THENL
   [REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      MATCH_MP_TAC GRGD_JOINABLE_COMPLEMENT_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y0:A`] MFD_MTOPOLOGY) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y0:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `uniformly_continuous_map
      (submetric (mfd_metric (top,atlas) (g:A->real^N^N) y0)
                 (K INTER {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y0 y}),
       real_euclidean_metric) (f:A->real)`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_UNIFORMLY_CONTINUOUS_MAP THEN
    ASM_REWRITE_TAC[MTOPOLOGY_SUBMETRIC; MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
                    SUBTOPOLOGY_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[SET_RULE `(s:A->bool) INTER t INTER s = s INTER t`] THEN
      MATCH_MP_TAC CLOSED_INTER_COMPACT_IN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_map; SUBMETRIC; REAL_EUCLIDEAN_METRIC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `q:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:A`; `p:A`]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let P2BC_LENGTH_CONT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1)
     ==> (\t. mfd_length atlas g gamma (&0) t) real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_continuous_on] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) gamma (&0) (&1)`; `&0`; `&1`;
                 `&0`; `x:real`; `e:real`] REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x':real` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`; `&0`; `x:real`]
                GRGD_LENGTH_SUBINTERVAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`; `&0`; `x':real`]
                GRGD_LENGTH_SUBINTERVAL) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_REFL; REAL_ABS_0; REAL_POS; REAL_LE_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let P2BC_LENGTH_IVT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     &0 <= lam /\ lam <= mfd_length atlas g gamma (&0) (&1)
     ==> ?t. &0 <= t /\ t <= &1 /\ mfd_length atlas g gamma (&0) t = lam`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. mfd_length atlas (g:A->real^N^N) gamma (&0) t`; `&0`; `&1`;
                 `lam:real`] REAL_IVT_INCREASING) THEN
  SUBGOAL_THEN
   `(\t. mfd_length atlas (g:A->real^N^N) gamma (&0) t) real_continuous_on real_interval[&0,&1]`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC P2BC_LENGTH_CONT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POS] THEN
  REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; IN_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[GSYM mfd_length] THEN MESON_TAC[]);;

let P2BC_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) y r1 r2.
     r1 <= r2 ==> mfd_ball (top,atlas) g y r1 SUBSET mfd_ball (top,atlas) g y r2`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

let P2BC_BALL_RIGHT_CONT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) K y0 r0 rb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ continuous_map (top,euclideanreal) f /\
     &0 < r0 /\ r0 < rb /\ mfd_ball (top,atlas) g y0 rb SUBSET K
     ==> !e. &0 < e
             ==> ?h. &0 < h /\ r0 + h <= rb /\
                     !p. p IN mfd_ball (top,atlas) g y0 (r0 + h)
                         ==> ?q. q IN mfd_ball (top,atlas) g y0 r0 /\ f p < f q + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `K:A->bool`; `y0:A`] P2BC_UNIF_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC"))) THEN
  EXISTS_TAC `min (eta / &3) (min (r0 / &2) (rb - r0))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = min (eta / &3) (min (r0 / &2) (rb - r0))` THEN
  SUBGOAL_THEN `&0 < h /\ h <= eta / &3 /\ h <= r0 / &2 /\ r0 + h <= rb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:A) IN K` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y0:A`; `r0 + h`; `rb:real`] P2BC_BALL_MONO) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN mfd_ball (top,atlas) (g:A->real^N^N) y0 (r0 + h)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `mfd_dist (top,atlas) (g:A->real^N^N) y0 p < r0` THENL
   [EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y0:A`; `p:A`;
                 `r0 + h - mfd_dist (top,atlas) (g:A->real^N^N) y0 p`] P2BC_DIST_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `r0 - h`] P2BC_LENGTH_IVT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(gamma:real->A) t` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) (y0:A) (gamma(t:real)) /\
                mfd_dist (top,atlas) (g:A->real^N^N) y0 (gamma t) <= r0 - h`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) (&0) = y0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `r0 - h`)) THEN
      MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) (gamma(t:real)) (p:A) /\
                mfd_dist (top,atlas) (g:A->real^N^N) (gamma t) p <=
                mfd_length atlas g gamma t (&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) (&1) = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN K` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `rb:real`)) (concl th) && is_binary "SUBSET" (concl th))) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p (gamma(t:real)) < eta`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `(gamma:real->A) t`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "UC" (MP_TAC o SPECL [`p:A`; `(gamma:real->A) t`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let P2BC_INV_SQ_RIGHT = prove
 (`!c r. &0 < r /\ c < inv(r pow 2)
         ==> ?h. &0 < h /\ !h'. &0 < h' /\ h' <= h ==> c <= inv((r + h') pow 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c <= &0` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 < inv c` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r < sqrt(inv c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `sqrt(inv c) - r` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `h':real` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(inv c) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_REFL]]);;

let P2BC_INV_SQ_LEFT = prove
 (`!c r. &0 < r /\ inv(r pow 2) < c
         ==> ?a. &0 <= a /\ a < r /\ !rho. a < rho ==> inv(rho pow 2) < c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(r pow 2)` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv c < r pow 2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  EXISTS_TAC `sqrt(inv c)` THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  X_GEN_TAC `rho:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(inv c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(inv c) pow 2` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_REFL];
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let P2BC_EXACT_RADIUS = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) K y0 ra rb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ continuous_map (top,euclideanreal) f /\
     &0 < ra /\ ra < rb /\ mfd_ball (top,atlas) g y0 rb SUBSET K /\
     (!q. q IN mfd_ball (top,atlas) g y0 ra ==> f q <= inv(ra pow 2)) /\
     (?q. q IN mfd_ball (top,atlas) g y0 rb /\ inv(rb pow 2) < f q)
     ==> ?r0. ra <= r0 /\ r0 < rb /\
              (!q. q IN mfd_ball (top,atlas) g y0 r0 ==> f q <= inv(r0 pow 2)) /\
              sup(IMAGE f (mfd_ball (top,atlas) g y0 r0)) = inv(r0 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `T0 = {rho | ra <= rho /\ rho <= rb /\
                         !q. q IN mfd_ball (top,atlas) (g:A->real^N^N) y0 rho
                             ==> (f:A->real) q <= inv(rho pow 2)}` THEN
  SUBGOAL_THEN `(ra:real) IN T0` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!rho. rho IN T0 ==> rho <= rb` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(T0:real->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?b. !x. x IN T0 ==> x <= b` ASSUME_TAC THENL
   [EXISTS_TAC `rb:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r0 = sup T0` THEN
  SUBGOAL_THEN `ra <= r0 /\ r0 <= rb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q1. q1 IN mfd_ball (top,atlas) (g:A->real^N^N) y0 r0
                     ==> (f:A->real) q1 <= inv(r0 pow 2)`
  (LABEL_TAC "le") THENL
   [X_GEN_TAC `q1:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(f:A->real) q1`; `r0:real`] P2BC_INV_SQ_LEFT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(q1:A) IN mfd_ball (top,atlas) (g:A->real^N^N) y0 r0` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`T0:real->bool`;
                   `max a (mfd_dist (top,atlas) (g:A->real^N^N) y0 q1)`] SUP_APPROACH) THEN
    ASM_REWRITE_TAC[REAL_MAX_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(rho:real) IN T0` THEN EXPAND_TAC "T0" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q1:A`) THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rho:real`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 < rb` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `inv(rb pow 2) < (f:A->real) q` THEN REWRITE_TAC[REAL_NOT_LT] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `r0:real = rb`)) THEN
    USE_THEN "le" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `K:A->bool`; `y0:A`; `r0:real`; `rb:real`]
                P2BC_BALL_RIGHT_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(inv(r0 pow 2) - b) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b + (inv(r0 pow 2) - b) / &2`; `r0:real`] P2BC_INV_SQ_RIGHT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r0 + min h h1 IN T0` MP_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `r0 <= r0 + x <=> &0 <= x`; REAL_LE_MIN] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y0:A`; `r0 + min h h1`; `r0 + h`] P2BC_BALL_MONO) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q2:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min h h1`) THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r0 + min h h1 <= r0` MP_TAC THENL
   [EXPAND_TAC "r0" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ARITH `r0 + x <= r0 <=> x <= &0`; REAL_MIN_LE] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The ball clause (7) through psi.  For a target ball B'(psi y0, r) with    *)
(* sup R' = r^-2: its closed ball lies in U' and is compact                  *)
(* (P2BC_C7_TARGET_BALL); the source has a radius r0 near r with sup R =     *)
(* r0^-2 (P2BC_C7_SOURCE_RADIUS), where the source clause gives the volume;  *)
(* Bishop-Gromov (CMP_RELVOL) with the model volume ratio near 1             *)
(* (P2BC_VMODEL_RATIO) brings it to radius r/sqrt(lam), and volume           *)
(* comparison through psi to the target (P2BC_C7_VOLUME, P2BC_C7_POINT).     *)
(* ========================================================================= *)

let P2BC_VMODEL_RATIO = prove
 (`!K rmin B. &0 <= K /\ &0 < rmin /\ rmin <= B
     ==> !th. &0 < th
              ==> ?e. &0 < e /\
                      !r1 r2. rmin <= r1 /\ r1 <= r2 /\ r2 <= B /\ r2 - r1 < e
                              ==> (&1 - th) * cmp_vmodel (:3) (--K) r2 <=
                                  cmp_vmodel (:3) (--K) r1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `th:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`--K:real`; `B + &1`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:3) (--K) rmin` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `&0`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `B + &1`)) (concl th) &&
      not (can (find_term ((=) `has_real_derivative`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cmp_vmodel (:3) (--K)`; `real_interval[&0,B + &1]`]
                REAL_COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; real_uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `th * cmp_vmodel (:3) (--K) rmin`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r1:real`; `r2:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cmp_vmodel (:3) (--K) rmin <= cmp_vmodel (:3) (--K) r2` ASSUME_TAC THENL
   [ASM_CASES_TAC `rmin:real = r2` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `B + &1`)) (concl th) &&
      not (can (find_term ((=) `has_real_derivative`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `th * cmp_vmodel (:3) (--K) rmin <= th * cmp_vmodel (:3) (--K) r2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2BC_C7_TARGET_BALL = prove
 (`!top' atlas' (g':B->real^3^3) eps z' e' Yc' W' y' r.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
     rfs_neck (top',atlas') g' eps z' e' /\ eps <= &1 / &4 /\
     (!w. w IN IMAGE e' (sphere(vec 0,&1))
          ==> mfd_scalar atlas' g' z' / &2 <= mfd_scalar atlas' g' w) /\
     top' frontier_of (top' closure_of Yc') SUBSET IMAGE e' (sphere(vec 0,&1)) /\
     top' closure_of Yc' SUBSET W' /\ IMAGE e' (rfs_neck_dom eps) SUBSET W' /\
     y' IN top' closure_of Yc' /\ &0 < r /\
     (?B. !q. q IN mfd_ball (top',atlas') g' y' r ==> mfd_scalar atlas' g' q <= B) /\
     sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' y' r)) = inv(r pow 2)
     ==> (!q. q IN mfd_ball (top',atlas') g' y' r
              ==> mfd_scalar atlas' g' q <= inv(r pow 2)) /\
         mfd_cball (top',atlas') g' y' r SUBSET W' /\
         compact_in top' (top' closure_of mfd_ball (top',atlas') g' y' r) /\
         top' closure_of mfd_ball (top',atlas') g' y' r SUBSET W' /\
         (!gamma. mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = y' /\
                  mfd_length atlas' g' gamma (&0) (&1) < r
                  ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN W')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q. q IN mfd_ball (top',atlas') (g':B->real^3^3) y' r
                    ==> mfd_scalar atlas' g' q <= inv(r pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `inv(r pow 2)`)) THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_cball (top',atlas') (g':B->real^3^3) y' r SUBSET W'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BC_SC_CBALL_IN THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `z':B`; `e':real^3->B`; `Yc':B->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y':B) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `Yc':B->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top' closure_of mfd_ball (top',atlas') (g':B->real^3^3) y' r SUBSET
                mfd_cball (top',atlas') g' y' r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `mfd_cball (top',atlas') (g':B->real^3^3) y' r` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    UNDISCH_TAC `mfd_complete (top',atlas') (g':B->real^3^3)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':B->real^3^3`; `eps:real`; `z':B`; `e':real^3->B`; `Yc':B->bool`;
                   `W':B->bool`; `y':B`; `r:real`; `r:real`; `gamma:real->B`]
                  P2BC_SC_CURVES_STAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_REFL] THEN
      SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas' (g':B->real^3^3) z'`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let P2BC_C7_SOURCE_RADIUS = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    eps z e Yc y0 r ra r1 rb lam alpha kap.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of U) /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     y0 IN top closure_of Yc /\
     &0 < r /\ &1 <= lam /\ &0 <= alpha /\ &0 < kap /\ kap < &1 /\
     (!q. q IN mfd_ball (top',atlas') g' (psi y0) r
          ==> mfd_scalar atlas' g' q <= inv(r pow 2)) /\
     sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' (psi y0) r)) =
     inv(r pow 2) /\
     (!gamma. mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = psi y0 /\
              mfd_length atlas' g' gamma (&0) (&1) < r
              ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U') /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                lam * (v dot (g y ** v))) /\
     (!y v. y IN U
            ==> v dot (g y ** v) <=
                lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     (!y. y IN U ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha) /\
     &0 < ra /\ ra <= r1 /\ ra < rb /\ sqrt lam * r1 <= r /\ sqrt lam * r <= rb /\
     rb <= &5 / &4 * r /\
     sqrt lam * (rb - sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps) <= r /\
     inv(r pow 2) + alpha <= inv(ra pow 2) /\
     inv(rb pow 2) < (&1 - kap) * inv(r pow 2) - alpha
     ==> mfd_ball (top,atlas) g y0 rb SUBSET U /\
         (!q. q IN mfd_ball (top,atlas) g y0 r1
              ==> psi q IN mfd_ball (top',atlas') g' (psi y0) r) /\
         ?r0. ra <= r0 /\ r0 < rb /\
              (!q. q IN mfd_ball (top,atlas) g y0 r0
                   ==> mfd_scalar atlas g q <= inv(r0 pow 2)) /\
              sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y0 r0)) =
              inv(r0 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&1 <= sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r1 <= r /\ r <= rb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r1` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* source curves of length below rb stay in U *)
  SUBGOAL_THEN
   `!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y0 /\
            mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) < rb
            ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN U`
  (LABEL_TAC "SRC") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                   `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`; `y0:A`; `r:real`; `rb:real`;
                   `lam:real`; `gamma:real->A`] P2BC_SRC_CURVES_STAY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb SUBSET U` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `U:A->bool`; `y0:A`; `q:A`; `rb:real`]
                  P2BC_DIST_IN_SHORT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[mfd_joinable_in] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!q. q IN mfd_ball (top,atlas) (g:A->real^3^3) y0 r1
                    ==> (psi:A->B) q IN mfd_ball (top',atlas':((B->bool)#(B->real^3))->bool)
                                                 (g':B->real^3^3) (psi y0) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2BC_BALL_IMAGE_IN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `U:A->bool`; `U':B->bool`; `psi':B->A`;
                          `r1:real`; `lam:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "SRC" (MP_TAC o SPEC `gamma:real->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb SUBSET top closure_of U`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN mfd_ball (top,atlas) (g:A->real^3^3) y0 ra
                    ==> mfd_scalar atlas g q <= inv(ra pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:A) IN mfd_ball (top,atlas) (g:A->real^3^3) y0 r1 /\ q IN U`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `y0:A`; `ra:real`; `r1:real`] P2BC_BALL_MONO) THEN
        ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `y0:A`; `ra:real`; `rb:real`] P2BC_BALL_MONO) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(r pow 2) + alpha` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c d. abs(a - b) <= c /\ a <= d ==> b <= d + c`) THEN
    EXISTS_TAC `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) q)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q. q IN mfd_ball (top,atlas) (g:A->real^3^3) y0 rb /\
                    inv(rb pow 2) < mfd_scalar atlas g q`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2BC_EXACT_RADIUS THEN EXISTS_TAC `top closure_of (U:A->bool)` THEN
    ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS]] THEN
  MP_TAC(ISPECL [`IMAGE (mfd_scalar atlas' (g':B->real^3^3))
                        (mfd_ball (top',atlas') g' ((psi:A->B) y0) r)`;
                 `(&1 - kap) * inv(r pow 2)`] SUP_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(psi:A->B) y0` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`)) THEN
      ASM SET_TAC[];
      EXISTS_TAC `inv(r pow 2)` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 < k * x ==> (&1 - k) * x < x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `y0:A`; `r:real`; `lam:real`; `q':B`] P2BC_BALL_PREIMAGE_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(psi':B->A) q'` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y0:A`; `sqrt lam * r`; `rb:real`] P2BC_BALL_MONO) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi':B->A) q' IN U /\ (psi:A->B) (psi' q') = q'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(psi':B->A) q'` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `alpha:real`)) (concl th) &&
    not (can (find_term ((=) `kap:real`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BC_BALL_VOLUME_IN = prove
 (`!top atlas (g:A->real^N^N) U y0 rho.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top (top closure_of U) /\ open_in top U /\
     mfd_ball (top,atlas) g y0 rho SUBSET U
     ==> mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 rho)
           (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g y0 rho))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top closure_of (U:A->bool)`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_ball (top,atlas) (g:A->real^N^N) y0 rho`;
                 `top closure_of (U:A->bool)`; `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_SIMP_TAC[MFD_BALL_OPEN];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    SIMP_TAC[]]);;

let P2BC_C7_VOLUME = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    y0 r r0 r1 ra lam K d th v' rmin B e.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of U) /\ y0 IN U /\
     &0 < ra /\ ra <= r0 /\ &0 < r1 /\ &0 <= d /\ &0 <= th /\ th <= &1 /\ &1 <= lam /\
     &0 <= K /\
     mfd_ball (top,atlas) g y0 r0 SUBSET U /\ mfd_ball (top,atlas) g y0 r1 SUBSET U /\
     compact_in top (top closure_of mfd_ball (top,atlas) g y0 r0) /\
     (?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 r0) v /\
          d <= v / r0 pow 3) /\
     (!y w. y IN U ==> --(&2 * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w) /\
     (!s t. rmin <= s /\ s <= t /\ t <= B /\ t - s < e
            ==> (&1 - th) * cmp_vmodel (:3) (--K) t <= cmp_vmodel (:3) (--K) s) /\
     rmin <= r1 /\ r0 <= B /\ r0 - r1 < e /\
     (!q. q IN mfd_ball (top,atlas) g y0 r1
          ==> psi q IN mfd_ball (top',atlas') g' (psi y0) r) /\
     (!y v. y IN U
            ==> v dot (g y ** v) <=
                lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     mfd_has_volume (top',atlas') g' (mfd_ball (top',atlas') g' (psi y0) r) v'
     ==> d * (&1 - th) * ra pow 3 <= lam * sqrt lam * v'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  ABBREV_TAC `B1 = mfd_ball (top,atlas) (g:A->real^3^3) y0 r1` THEN
  ABBREV_TAC `v1 = mfd_volume (top,atlas) (g:A->real^3^3) B1` THEN
  SUBGOAL_THEN `mfd_has_volume (top,atlas) (g:A->real^3^3) B1 v1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v1"; "B1"] THEN MATCH_MP_TAC P2BC_BALL_VOLUME_IN THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (B1:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN ASM_SIMP_TAC[MFD_BALL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top' (IMAGE (psi:A->B) B1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `U':B->bool`;
                   `psi:A->B`; `psi':B->A`; `B1:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `IMAGE (psi:A->B) B1`;
                 `mfd_ball (top',atlas') (g':B->real^3^3) (psi(y0:A)) r`; `v':real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "B1" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v1' = mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) B1)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `B1:A->bool`;
                 `v1:real`; `v1':real`; `lam:real`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:A) IN B1` THEN EXPAND_TAC "B1" THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * r0 pow 3 <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `d <= v / r0 pow 3` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `ra pow 3 <= r0 pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * ra pow 3 <= d * r0 pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `mfd_ball (top,atlas) (g:A->real^3^3) y0 r0`; `v:real`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - th) * d * ra pow 3 <= v1` ASSUME_TAC THENL
   [ASM_CASES_TAC `r1 <= r0` THENL
     [ALL_TAC;
      SUBGOAL_THEN `v <= v1` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `mfd_ball (top,atlas) (g:A->real^3^3) y0 r0`;
                       `B1:A->bool`; `v:real`; `v1:real`] MFD_HAS_VOLUME_MONO) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "B1" THEN
        MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&1 - th) * (d * ra pow 3) <= d * ra pow 3` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= th * x ==> (&1 - th) * x <= x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]] THEN
    MP_TAC(ISPECL [`(:A)`; `(:3)`] CMP_RELVOL) THEN REWRITE_TAC[CMP_RELVOL_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `y0:A`; `K:real`; `r0:real`; `r1:real`; `r0:real`; `v1:real`; `v:real`]) THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`--K:real`; `r0 + &1`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (MP_TAC o SPECL [`&0`; `r0:real`])
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r1:real`; `r0:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ABBREV_TAC `V0 = cmp_vmodel (:3) (--K) r0` THEN
    ABBREV_TAC `V1 = cmp_vmodel (:3) (--K) r1` THEN
    SUBGOAL_THEN `v * ((&1 - th) * V0) <= v * V1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((&1 - th) * v) * V0 <= v1 * V0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - th) * v` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam * sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * sqrt lam * v1' <= lam * sqrt lam * v'` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BC_C7_POINT = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    eps z e Yc y0 r ra r1 rb lam alpha kap K d th rmin Bv e0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of U) /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
     (!w. w IN IMAGE (psi o e) (sphere(vec 0,&1))
          ==> mfd_scalar atlas' g' (psi z) / &2 <= mfd_scalar atlas' g' w) /\
     top' frontier_of (top' closure_of IMAGE psi Yc) SUBSET
       IMAGE (psi o e) (sphere(vec 0,&1)) /\
     top' closure_of IMAGE psi Yc SUBSET U' /\
     IMAGE (psi o e) (rfs_neck_dom eps) SUBSET U' /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                lam * (v dot (g y ** v))) /\
     (!y v. y IN U
            ==> v dot (g y ** v) <=
                lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     (!y. y IN U ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha) /\
     (!y w. y IN U ==> --(&2 * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w) /\
     (!r. &0 < r /\
          (?B. !z. z IN mfd_ball (top,atlas) g y0 r ==> mfd_scalar atlas g z <= B) /\
          sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y0 r)) = inv(r pow 2)
          ==> compact_in top (top closure_of mfd_ball (top,atlas) g y0 r) /\
              top closure_of mfd_ball (top,atlas) g y0 r SUBSET U /\
              ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 r) v /\
                  d <= v / r pow 3) /\
     (!s t. rmin <= s /\ s <= t /\ t <= Bv /\ t - s < e0
            ==> (&1 - th) * cmp_vmodel (:3) (--K) t <= cmp_vmodel (:3) (--K) s) /\
     y0 IN Yc /\ Yc SUBSET U /\ &0 < r /\
     (?B. !q. q IN mfd_ball (top',atlas') g' (psi y0) r ==> mfd_scalar atlas' g' q <= B) /\
     sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' (psi y0) r)) =
     inv(r pow 2) /\
     &1 <= lam /\ &0 <= alpha /\ &0 < kap /\ kap < &1 /\ &0 <= K /\ &0 <= d /\
     &0 <= th /\ th <= &1 /\
     &0 < ra /\ ra <= r1 /\ ra < rb /\ sqrt lam * r1 <= r /\ sqrt lam * r <= rb /\
     rb <= &5 / &4 * r /\
     sqrt lam * (rb - sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps) <= r /\
     inv(r pow 2) + alpha <= inv(ra pow 2) /\
     inv(rb pow 2) < (&1 - kap) * inv(r pow 2) - alpha /\
     rmin <= r1 /\ rb <= Bv /\ rb - r1 < e0
     ==> compact_in top' (top' closure_of mfd_ball (top',atlas') g' (psi y0) r) /\
         top' closure_of mfd_ball (top',atlas') g' (psi y0) r SUBSET U' /\
         ?v. mfd_has_volume (top',atlas') g' (mfd_ball (top',atlas') g' (psi y0) r) v /\
             d * (&1 - th) * ra pow 3 <= lam * sqrt lam * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&1 <= sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r1 <= r /\ r <= rb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r1` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(Yc:A->bool) SUBSET U`) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Yc:A->bool) SUBSET topspace top /\ IMAGE (psi:A->B) Yc SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`)) THEN
    UNDISCH_TAC `IMAGE (psi:A->B) U SUBSET U'` THEN
    UNDISCH_TAC `(Yc:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN top closure_of Yc /\ (psi:A->B) y0 IN top' closure_of IMAGE psi Yc`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `Yc:A->bool`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top':B topology`; `IMAGE (psi:A->B) Yc`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `eps:real`; `(psi:A->B) z`; `(psi:A->B) o (e:real^3->A)`;
                 `IMAGE (psi:A->B) Yc`; `U':B->bool`; `(psi:A->B) y0`; `r:real`]
                P2BC_C7_TARGET_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`; `y0:A`; `r:real`;
                 `ra:real`; `r1:real`; `rb:real`; `lam:real`; `alpha:real`; `kap:real`]
                P2BC_C7_SOURCE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d:real`)) (concl th) &&
    not (can (find_term ((=) `th:real`)) (concl th)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `inv(r0 pow 2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `(psi:A->B) y0`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3)
                (mfd_ball (top',atlas') g' ((psi:A->B) y0) r)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BC_C7_VOLUME THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
    `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y0:A`; `r:real`;
    `r0:real`; `r1:real`; `K:real`; `rmin:real`; `Bv:real`; `e0:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The ball clause (7) for the target with one constant d' > inv C, for all  *)
(* target metrics with C^0 distortion lam <= 1 + eta and scalar error alpha  *)
(* <= eta Rn / 8 (P2BC_CLAUSE7). Radii: ra = r / (sqrt lam (1 + eta)), r1 =  *)
(* r / sqrt lam, rb = sqrt lam (1 + eta) r; the numerical side conditions    *)
(* (P2BC_C7_NUMERIC) and the final constant (P2BC_C7_CONST).                 *)
(* ========================================================================= *)

let P2BC_CUBE_BOUND = prove
 (`!x. &0 <= x /\ x <= &1 / &10 ==> (&1 + x) pow 3 <= &1 + &4 * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * x <= x * (&1 / &10)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x * x) * x <= (x * x) * (&1 / &10)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(&1 + x) pow 3 = &1 + &3 * x + &3 * (x * x) + (x * x) * x /\
    x * x <= x * (&1 / &10) /\ (x * x) * x <= (x * x) * (&1 / &10) /\ &0 <= x
    ==> (&1 + x) pow 3 <= &1 + &4 * x`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BC_C7_NUMERIC = prove
 (`!eta s r Rn Rm L e0 alpha.
     &0 < eta /\ eta <= &1 / &40 /\ &1 <= s /\ s <= &1 + eta /\ &0 < Rn /\ &0 < Rm /\
     &0 < r /\ Rn / &2 <= inv(r pow 2) /\ inv(r pow 2) <= &2 * Rm /\ &0 <= L /\
     &4 * eta * sqrt(&2 / Rn) <= L /\ &8 * eta * sqrt(&2 / Rn) <= e0 /\
     &0 <= alpha /\ alpha <= eta * Rn / &8
     ==> &0 < r / (s * (&1 + eta)) /\ r / (s * (&1 + eta)) <= r / s /\
         r / (s * (&1 + eta)) < s * (&1 + eta) * r /\
         s * (r / s) <= r /\ s * r <= s * (&1 + eta) * r /\
         s * (&1 + eta) * r <= &5 / &4 * r /\
         s * (s * (&1 + eta) * r - L) <= r /\
         inv(r pow 2) + alpha <= inv((r / (s * (&1 + eta))) pow 2) /\
         inv((s * (&1 + eta) * r) pow 2) < (&1 - eta / &2) * inv(r pow 2) - alpha /\
         sqrt(&1 / (&2 * Rm)) / &2 <= r / s /\
         s * (&1 + eta) * r <= &2 * sqrt(&2 / Rn) /\
         s * (&1 + eta) * r - r / s < e0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sg = &1 + eta` THEN
  SUBGOAL_THEN `&1 < sg /\ sg <= &41 / &40 /\ &0 < s /\ s <= sg` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2 /\ r pow 2 <= &2 / Rn /\ &1 / (&2 * Rm) <= r pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`Rn / &2`; `inv(r pow 2)`] REAL_LE_INV2) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2`; REAL_INV_INV] THEN
      REWRITE_TAC[REAL_INV_DIV];
      MP_TAC(SPECL [`inv(r pow 2)`; `&2 * Rm`] REAL_LE_INV2) THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_INV_INV] THEN
      REWRITE_TAC[REAL_INV_MUL; real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r <= sqrt(&2 / Rn) /\ sqrt(&1 / (&2 * Rm)) <= r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * sg /\ sg <= s * sg /\ s * sg <= sg * sg` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg pow 3 <= &1 + &4 * eta` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eta * eta <= eta * (&1 / &40) /\ &0 <= eta * eta /\
                (eta * eta) * eta <= (eta * eta) * (&1 / &40)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_SQUARE] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sg * sg <= &1 + &3 * eta /\ &1 + &2 * eta <= sg * sg /\
                &1 <= (&1 - eta) * (sg * sg) /\ &1 - eta <= inv sg`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `inv(&1 + eta) = &1 / (&1 + eta)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 + eta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < &1 + eta`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= eta * eta ==> (&1 - eta) * (&1 + eta) <= &1`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(r pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; real_div; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `(s * sg * r) * (s * sg) = r * ((s * sg) * (s * sg))`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sg * sg` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `s * s * sg <= &1 + &4 * eta` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sg pow 3` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `sg pow 3 = sg * sg * sg`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(s * s * sg) * r <= (&1 + &4 * eta) * r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `eta * r <= eta * sqrt(&2 / Rn)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `L <= s * L` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_DIV; REAL_INV_DIV] THEN REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `(&1 + &2 * eta) * inv(r pow 2) <= ((s * sg) pow 2) * inv(r pow 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sg * sg` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * Rn <= &2 * eta * inv(r pow 2)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&2 * eta * x = eta * (&2 * x)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `inv((s * sg * r) pow 2) = inv((s * sg) pow 2) * inv(r pow 2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_INV_MUL; REAL_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `inv((s * sg) pow 2) <= &1 - eta` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sg * sg)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < sg * sg` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `inv(sg * sg) = &1 / (sg * sg)` SUBST1_TAC THENL
         [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv((s * sg) pow 2) * inv(r pow 2) <= (&1 - eta) * inv(r pow 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `eta * Rn <= &2 * eta * inv(r pow 2) /\ &0 < eta * inv(r pow 2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&2 * eta * x = eta * (&2 * x)`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r / &2` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&5 / &4 * sqrt(&2 / Rn)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&5 / &4 * r` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &5 / &4 * x <= &2 * x`) THEN
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(s * sg) * r <= (sg * sg) * r /\ r * inv sg <= r * inv s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `r * (&1 - eta) <= r * inv sg` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(sg * sg) * r <= (&1 + &3 * eta) * r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `eta * r <= eta * sqrt(&2 / Rn)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta * sqrt(&2 / Rn)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC]);;

let P2BC_C7_CONST = prove
 (`!D eta s r v.
     &0 <= D /\ &0 < eta /\ eta <= &1 / &40 /\ &1 <= s /\ s <= &1 + eta /\ &0 < r /\
     D * (r / (s * (&1 + eta))) pow 3 <= s pow 2 * s * v
     ==> D / (&1 + &16 * eta) <= v / r pow 3`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `sg = &1 + eta` THEN
  SUBGOAL_THEN `&0 < s /\ &1 < sg /\ s <= sg` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * sg` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `D * r pow 3 <= (s pow 3 * (s * sg) pow 3) * v` ASSUME_TAC THENL
   [UNDISCH_TAC `D * (r / (s * sg)) pow 3 <= s pow 2 * s * v` THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < (s * sg) pow 3` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`D * r pow 3 * inv((s * sg) pow 3)`; `s pow 2 * s * v`; `(s * sg) pow 3`]
                 REAL_LE_RMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC];
                      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(D * r pow 3 * inv((s * sg) pow 3)) * (s * sg) pow 3 = D * r pow 3`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `s pow 3 = s * s * s`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 3 * (s * sg) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s pow 3 * (s * sg) pow 3) * v < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * v < &0 <=> &0 < x * --v`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 3 * (s * sg) pow 3 <= &1 + &16 * eta` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= s pow 3 /\ s pow 3 <= &1 + &4 * eta /\ &0 <= sg pow 3 /\
                  sg pow 3 <= &1 + &4 * eta` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sg pow 3` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "sg" THEN MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "sg" THEN MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &4 * eta) * (&1 + &4 * eta) * (&1 + &4 * eta)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC `&4 * eta` P2BC_CUBE_BOUND) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `x pow 3 = x * x * x`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * r pow 3 <= (&1 + &16 * eta) * v` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s pow 3 * (s * sg) pow 3) * v` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + &16 * eta /\ &0 < r pow 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(v / r) * e = (v * e) / r`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let P2BC_CLAUSE7 = prove
 (`!top atlas (g:A->real^3^3) U Y C eps z e Rn Rm K d.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top U /\ compact_in top (top closure_of U) /\ Y SUBSET U /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Y) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Y SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     &0 < Rn /\ Rn <= Rm /\
     (!y. y IN U ==> Rn <= mfd_scalar atlas g y /\ mfd_scalar atlas g y <= Rm) /\
     &0 <= K /\
     (!y w. y IN U ==> --(&2 * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w) /\
     &0 < C /\ inv C < d /\
     (!y r. y IN Y /\ &0 < r /\
            (?B. !z. z IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g z <= B) /\
            sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) = inv(r pow 2)
            ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                    d <= v / r pow 3)
     ==> ?eta d'. &0 < eta /\ inv C < d' /\
           !top' atlas' (g':B->real^3^3) psi psi' lam alpha.
              hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
              riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
              (!w. w IN IMAGE (psi o e) (sphere(vec 0,&1))
                   ==> mfd_scalar atlas' g' (psi z) / &2 <= mfd_scalar atlas' g' w) /\
              top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                IMAGE (psi o e) (sphere(vec 0,&1)) /\
              top' closure_of IMAGE psi Y SUBSET IMAGE psi U /\
              IMAGE (psi o e) (rfs_neck_dom eps) SUBSET IMAGE psi U /\
              (!w. w IN IMAGE e (sphere(vec 0,&1))
                   ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
              &1 <= lam /\ lam <= &1 + eta /\ &0 <= alpha /\ alpha <= eta * Rn / &8 /\
              (!y v. y IN U
                     ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                         lam * (v dot (g y ** v))) /\
              (!y v. y IN U
                     ==> v dot (g y ** v) <=
                         lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
              (!y. y IN U
                   ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha)
              ==> !y' r. y' IN IMAGE psi Y /\ &0 < r /\
                         (?B. !q. q IN mfd_ball (top',atlas') g' y' r
                                  ==> mfd_scalar atlas' g' q <= B) /\
                         sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' y' r)) =
                         inv(r pow 2)
                         ==> compact_in top' (top' closure_of mfd_ball (top',atlas') g' y' r) /\
                             top' closure_of mfd_ball (top',atlas') g' y' r SUBSET
                               IMAGE psi U /\
                             ?v. mfd_has_volume (top',atlas') g'
                                   (mfd_ball (top',atlas') g' y' r) v /\
                                 d' <= v / r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv C /\ &0 < d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `inv C` THEN ASM_SIMP_TAC[REAL_LT_INV_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `th = (d - inv C) / (&2 * d)` THEN
  SUBGOAL_THEN `&0 <= th /\ th <= &1 /\ d * (&1 - th) = (d + inv C) / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &2 * d`] THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `rM = sqrt(&2 / Rn)` THEN
  ABBREV_TAC `rm = sqrt(&1 / (&2 * Rm)) / &2` THEN
  SUBGOAL_THEN `&0 < rM /\ &0 < rm /\ rm <= &2 * rM` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rM"; "rm"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> a / &2 <= &2 * b`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN
        SUBGOAL_THEN `&0 < Rm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `inv(&2 * Rm) <= inv(Rn / &2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_INV_DIV; REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `rm:real`; `&2 * rM`] P2BC_VMODEL_RATIO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `th:real`) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC)] THENL
   [EXPAND_TAC "th" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) * inv eps` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) z` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eta. &0 < eta /\ eta <= &1 / &40 /\ &4 * eta * rM <= L /\
                      &8 * eta * rM <= e0 /\ &64 * eta * inv C <= d - inv C`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &40) (min (L / (&4 * rM))
                  (min (e0 / (&8 * rM)) ((d - inv C) / (&64 * inv C))))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN
    SUBGOAL_THEN `&0 < &4 * rM /\ &0 < &8 * rM /\ &0 < &64 * inv C` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&4 * x * rM = x * (&4 * rM)`] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= b`) THEN
      SUBGOAL_THEN `min (&1 / &40) (min (L / (&4 * rM))
                     (min (e0 / (&8 * rM)) ((d - inv C) / (&64 * inv C)))) <= L / (&4 * rM)`
      MP_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
      REWRITE_TAC[REAL_ARITH `&8 * x * rM = x * (&8 * rM)`] THEN
      SUBGOAL_THEN `min (&1 / &40) (min (L / (&4 * rM))
                     (min (e0 / (&8 * rM)) ((d - inv C) / (&64 * inv C)))) <= e0 / (&8 * rM)`
      MP_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]];
      REWRITE_TAC[REAL_ARITH `&64 * x * i = x * (&64 * i)`] THEN
      SUBGOAL_THEN `min (&1 / &40) (min (L / (&4 * rM))
                     (min (e0 / (&8 * rM)) ((d - inv C) / (&64 * inv C)))) <=
                    (d - inv C) / (&64 * inv C)`
      MP_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]];
    ALL_TAC] THEN
  EXISTS_TAC `eta:real` THEN
  EXISTS_TAC `(d * (&1 - th)) / (&1 + &16 * eta)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + &16 * eta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 < eta * inv C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y':B`; `r:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> can (find_term ((=) `y':B`)) (concl th) &&
                     is_binary "IN" (concl th))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&1 <= sqrt lam /\ sqrt lam <= &1 + eta /\ sqrt lam pow 2 = lam`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eta * Rn <= Rn / &40` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `eta * Rn <= (&1 / &40) * Rn ==> eta * Rn <= Rn / &40`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) y0 IN topspace top' /\
                (psi:A->B) y0 IN top' closure_of IMAGE psi Y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `IMAGE (psi:A->B) Y`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `eps:real`; `(psi:A->B) z`; `(psi:A->B) o (e:real^3->A)`;
                 `IMAGE (psi:A->B) Y`; `IMAGE (psi:A->B) U`; `(psi:A->B) y0`; `r:real`]
                P2BC_C7_TARGET_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `Rn / &2 <= inv(r pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
        `!a b c. Rn <= b /\ abs(a - b) <= c /\ c <= eta * Rn / &8 /\
                 eta * Rn <= Rn / &40 /\ &0 < Rn ==> Rn / &2 <= a`) THEN
      EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) y0` THEN EXISTS_TAC `alpha:real` THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(r pow 2) <= &2 * Rm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `inv(r pow 2)` && is_comb(lhs(concl th)))) THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(psi:A->B) y0` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:B) IN IMAGE (psi:A->B) U` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:B. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `top' closure_of mfd_ball (top',atlas') (g':B->real^3^3) (psi(y0:A)) r` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top':B topology`;
                     `mfd_ball (top',atlas') (g':B->real^3^3) (psi(y0:A)) r`]
                    CLOSURE_OF_SUBSET) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(q:B) IN IMAGE (psi:A->B) U` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `!b c. b <= Rm /\ abs(a - b) <= c /\ c <= eta * Rn / &8 /\
             eta * Rn <= Rn / &40 /\ &0 < Rn /\ Rn <= Rm ==> a <= &2 * Rm`) THEN
    EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) p` THEN EXISTS_TAC `alpha:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real`; `sqrt lam`; `r:real`; `Rn:real`; `Rm:real`; `L:real`;
                 `e0:real`; `alpha:real`] P2BC_C7_NUMERIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. &0 < r /\
        (?B. !z. z IN mfd_ball (top,atlas) g y0 r ==> mfd_scalar atlas g z <= B) /\
        sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) (mfd_ball (top,atlas) g y0 r)) =
        inv(r pow 2)
        ==> compact_in top (top closure_of mfd_ball (top,atlas) g y0 r) /\
            top closure_of mfd_ball (top,atlas) g y0 r SUBSET U /\
            ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 r) v /\
                d <= v / r pow 3`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:A->bool`)) (concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `B':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                 `eps:real`; `z:A`; `e:real^3->A`; `Y:A->bool`; `y0:A`; `r:real`;
                 `r / (sqrt lam * (&1 + eta))`; `r / sqrt lam`;
                 `sqrt lam * (&1 + eta) * r`; `lam:real`; `alpha:real`; `eta / &2`;
                 `K:real`; `d:real`; `th:real`; `rm:real`; `&2 * rM`; `e0:real`]
                P2BC_C7_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "rm" THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "rM" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BC_C7_CONST THEN EXISTS_TAC `sqrt lam` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `d * (&1 - th) * (r / (sqrt lam * (&1 + eta))) pow 3 <=
               lam * sqrt lam * v` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Necks and charts of a cap through psi. Renormalizing the closeness from   *)
(* R(x) to R(z) (P2BC_MCLOSE_RENORM, from P2B9S_LCK_SCALE_LE and             *)
(* LCK_DIST_MONO); the necks of the cap transfer (P2BC_NECK_TRANSFER, from   *)
(* P2B9S_OPEN_NECK); the ball or twisted chart and the set identities of     *)
(* clause (1) transfer (P2BC_CHART_BALL, P2BC_CHART_TWISTED,                 *)
(* P2BC_TWISTED_TRANSFER).                                                   *)
(* ========================================================================= *)

let P2BC_MCLOSE_RENORM = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    W k k' delta delta' R0 R1.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ W SUBSET U /\
     &0 < R0 /\ &0 < R1 /\ k' <= k /\
     (&1 + R0 / R1) pow k' * delta pow 2 <= delta' pow 2 /\
     rfs_mclose k delta atlas U (\y. R0 %% g y)
       (\y. R0 %% mfd_pullback_metric atlas atlas' psi g' y)
     ==> rfs_mclose k' delta' atlas W (\y. R1 %% g y)
           (\y. R1 %% mfd_pullback_metric atlas atlas' psi g' y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `(&1 + R0 / R1) pow k' * d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&1 + R0 / R1) pow k' * delta pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &1 + x`) THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y:A`] P2B9S_PB_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  ABBREV_TAC `G0 = metric_local atlas (chart_at atlas (y:A)) (g:A->real^3^3)` THEN
  ABBREV_TAC `G1 = metric_local atlas (chart_at atlas (y:A))
                     (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3))` THEN
  ABBREV_TAC `p = SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y` THEN
  SUBGOAL_THEN `metric_field s (\z. R0 %% (G0:real^3->real^3^3) z) /\
                metric_field s (\z. R0 %% (G1:real^3->real^3^3) z)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z. R1 %% (G0:real^3->real^3^3) z) =
                (\z. (R1 / R0) %% (\z. R0 %% G0 z) z) /\
                (\z. R1 %% (G1:real^3->real^3^3) z) =
                (\z. (R1 / R0) %% (\z. R0 %% G1 z) z)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[MATRIX_CMUL_ASSOC; FUN_EQ_THM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k':num`; `s:real^3->bool`; `\z. R0 %% (G0:real^3->real^3^3) z`;
                 `\z. R0 %% (G1:real^3->real^3^3) z`; `R1 / R0`; `p:real^3`]
                P2B9S_LCK_SCALE_LE) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_INV_DIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + R0 / R1) pow k' *
              lck_dist2 k' (\z. R0 %% (G0:real^3->real^3^3) z) (\z. R0 %% G1 z) p` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 k (\z. R0 %% (G0:real^3->real^3^3) z) (\z. R0 %% G1 z) p` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
  EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]);;

let P2BC_NECK_TRANSFER = prove
 (`!eps top atlas (g:A->real^3^3) z e U R0.
     &0 < eps /\ eps < &1 / &4 /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\ &0 < R0
     ==> ?delta0. &0 < delta0 /\
           !delta top' atlas' (g':B->real^3^3) psi psi'.
              &0 < delta /\ delta <= delta0 /\
              smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% g y)
                (\y. R0 %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> rfs_neck (top',atlas') g' eps (psi z) (psi o e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z:A`; `e:real^3->A`]
                (INST_TYPE [`:B`,`:B`] P2B9S_OPEN_NECK)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dz:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NK"))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Fc = (&1 + R0 / mfd_scalar atlas (g:A->real^3^3) z) pow (rfs_kreg dz)` THEN
  SUBGOAL_THEN `&1 <= Fc` ASSUME_TAC THENL
   [EXPAND_TAC "Fc" THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `dz / Fc` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `delta <= dz` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dz / Fc` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= Fc ==> &0 < Fc`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN
    REWRITE_TAC[rfs_neck; mfd_param; mfd_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "NK" MATCH_MP_TAC THEN EXISTS_TAC `psi':B->A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (psi:A->B) U`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BC_MCLOSE_RENORM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                        `IMAGE (psi:A->B) U`; `psi':B->A`; `rfs_kreg delta`; `delta:real`;
                        `R0:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Fc * (dz / Fc) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < Fc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_POW_2; REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `Fc * (a * a) * (i * i) = (a * a) * (Fc * i) * i`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]]);;

let P2BC_IMAGE_DIFF_INJ = prove
 (`!(psi:A->B) psi' U S T.
     (!x. x IN U ==> psi'(psi x) = x) /\ S SUBSET U /\ T SUBSET U
     ==> IMAGE psi (S DIFF T) = IMAGE psi S DIFF IMAGE psi T`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN
  X_GEN_TAC `w:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:A = x'` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(x:A) IN U /\ x' IN U` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let P2BC_TWISTED_TRANSFER = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (p:real^3->A).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U
     ==> rfs_twisted_chart top' atlas' (psi o p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_twisted_chart] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(p:real^3->A) y IN U /\ p w IN U` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(psi:A->B) (p(y:real^3)) = psi (p w) <=> p y = p w` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rfs_twist`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `U':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2BC_CHART_BALL = prove
 (`!top atlas top' atlas' (g':B->real^3^3) U (psi:A->B) psi' Y eps b
    (e:real^3->A) e' z z' f f'.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
     mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
     Y = IMAGE b (ball(vec 0,&1)) /\
     IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
     IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y)) /\
     rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
     rfs_neck (top',atlas') g' eps (psi z') (psi o e')
     ==> mfd_ball_chart top' atlas' (psi o b) /\
         IMAGE (psi o b) (ball(vec 0,&2)) SUBSET IMAGE psi U /\
         IMAGE psi Y = IMAGE (psi o b) (ball(vec 0,&1)) /\
         IMAGE (psi o e) (rfs_neck_dom eps) =
           IMAGE psi U DIFF IMAGE (psi o b) (cball(vec 0,&1)) /\
         IMAGE (psi o e') (rfs_neck_dom eps) SUBSET IMAGE psi U /\
         IMAGE (psi o e') (sphere(vec 0,&1)) = IMAGE (psi o b) (sphere(vec 0,&1)) /\
         (!y. y IN annulus (&1) (&2) ==> (psi o b) y = (psi o e')(radial_ext f y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `IMAGE (psi:A->B) U`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_ball_chart];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BC_IMAGE_DIFF_INJ THEN EXISTS_TAC `psi':B->A` THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let P2BC_CHART_TWISTED = prove
 (`!top atlas top' atlas' (g':B->real^3^3) U (psi:A->B) psi' Y eps p
    (e:real^3->A) e' z z' f f'.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
     smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
     Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     IMAGE e (rfs_neck_dom eps) =
       U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
     IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))) /\
     rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
     rfs_neck (top',atlas') g' eps (psi z') (psi o e')
     ==> rfs_twisted_chart top' atlas' (psi o p) /\
         IMAGE (psi o p) (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U /\
         IMAGE psi Y = IMAGE (psi o p) (annulus (&1 / &2) (&2)) /\
         IMAGE (psi o e) (rfs_neck_dom eps) =
           IMAGE psi U DIFF IMAGE (psi o p) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
         IMAGE (psi o e') (rfs_neck_dom eps) SUBSET IMAGE psi U /\
         IMAGE (psi o e') (sphere(vec 0,&1)) = IMAGE (psi o p) (sphere(vec 0,&2)) /\
         (!y. y IN annulus (&2) (&4)
              ==> (psi o p) y = (psi o e')(radial_ext f (inv(&2) % y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC P2BC_TWISTED_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `IMAGE (psi:A->B) U`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BC_IMAGE_DIFF_INJ THEN EXISTS_TAC `psi':B->A` THEN
    EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Source bounds and margins for caps. A Ricci lower bound on a compact set  *)
(* from the curvature bound (P2BC_RICCI_LOWER, RFA_LRIC_BOUND); the margins  *)
(* of the diameter and volume clauses under C^0 distortion and a perturbed   *)
(* supremum of R (P2BC_MARGIN_DIAM, P2BC_MARGIN_VOL).                        *)
(* ========================================================================= *)

let P2BC_RICCI_LOWER = prove
 (`!top atlas (g:A->real^3^3) K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?Kr. &0 <= Kr /\
              !y w. y IN K ==> --(&2 * Kr) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `K:A->bool`] P2B9S_RMD2_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bg:real`) THEN
  EXISTS_TAC `(&3 * sqrt(max Bg (&0))) / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ARITH `&0 <= &2`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ARITH `&0 <= &3`] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local atlas (chart_at atlas (y:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`;
                 `max Bg (&0)`; `w:real^3`] (INST_TYPE [`:3`,`:N`] RFA_LRIC_BOUND)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max b (&0)`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[rfa_rmd2]];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; GSYM mfd_ricci] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 <= w dot ((g:A->real^3^3) y ** w)` MP_TAC THENL
   [ASM_CASES_TAC `w:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2BC_MARGIN_DIAM = prove
 (`!d3 Rs C. &0 <= d3 /\ &0 < Rs /\ &0 < C /\ d3 < C * inv(sqrt Rs)
     ==> ?t. &0 < t /\ t <= &1 /\
             !dl a. &0 <= dl /\ dl <= t /\ &0 <= a /\ a <= t
                    ==> sqrt(&1 + dl) * d3 < C * inv(sqrt(Rs + a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Rs` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `d3 pow 2 * Rs < C pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `d3 * sqrt Rs < C` ASSUME_TAC THENL
     [UNDISCH_TAC `d3 < C * inv(sqrt Rs)` THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `d3 pow 2 * Rs = (d3 * sqrt Rs) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `Q = C pow 2 - d3 pow 2 * Rs` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (d3 pow 2 * (Rs + &2) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * (x + &1)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t <= &1 /\ t * (&2 * (d3 pow 2 * (Rs + &2) + &1)) <= Q`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (Q / (&2 * (d3 pow 2 * (Rs + &2) + &1)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ;
             ASSUME `&0 < &2 * (d3 pow 2 * (Rs + &2) + &1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`dl:real`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(Rs + a)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ] THEN
  SUBGOAL_THEN `(sqrt(&1 + dl) * d3) * sqrt(Rs + a) = sqrt((&1 + dl) * d3 pow 2 * (Rs + a))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_ARITH `&0 <= dl ==> &0 <= &1 + dl`;
                 REAL_ARITH `&0 < Rs /\ &0 <= a ==> &0 <= Rs + a`; REAL_LE_MUL] THEN
    ASM_SIMP_TAC[POW_2_SQRT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `d3 pow 2 * (dl * Rs + a + dl * a) <= t * (d3 pow 2 * (Rs + &2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d3 pow 2 * (t * (Rs + &2))` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `dl * Rs <= t * Rs /\ dl * a <= t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * a` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BC_MARGIN_VOL = prove
 (`!v Rs C. &0 <= v /\ &0 < Rs /\ &0 < C /\ v < C * inv(sqrt Rs) pow 3
     ==> ?t. &0 < t /\ t <= &1 / &10 /\
             !dl a. &0 <= dl /\ dl <= t /\ &0 <= a /\ a <= t * Rs
                    ==> (&1 + dl) * sqrt(&1 + dl) * v < C * inv(sqrt(Rs + a)) pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Rs` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `v pow 2 * Rs pow 3 < C pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `v * sqrt Rs pow 3 < C` ASSUME_TAC THENL
     [UNDISCH_TAC `v < C * inv(sqrt Rs) pow 3` THEN
      REWRITE_TAC[REAL_POW_INV; GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `v pow 2 * Rs pow 3 = (v * sqrt Rs pow 3) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `M = v pow 2 * Rs pow 3` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t <= &1 / &10 /\ &10 * t * M < C pow 2 - M`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &10) ((C pow 2 - M) / (&10 * (M + &1)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    SUBGOAL_THEN `&0 < &10 * (M + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&10 * ((C pow 2 - M) / (&10 * (M + &1))) * M` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ARITH `&0 <= &10`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    REWRITE_TAC[REAL_ARITH `&10 * (q * i) * M = q * (M * (&10 * i))`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < q /\ q * x < q * &1 ==> q * x < q`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    REWRITE_TAC[REAL_ARITH `M * &10 * inv(&10) * i = (&10 * inv(&10)) * (M * i)`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < M + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`dl:real`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Rs + a /\ &0 < sqrt(Rs + a)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV; GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
  ABBREV_TAC `X = ((&1 + dl) * sqrt(&1 + dl) * v) * sqrt(Rs + a) pow 3` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `X pow 2 = (&1 + dl) pow 3 * M * ((Rs + a) / Rs) pow 3` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN EXPAND_TAC "M" THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `6 = 2 * 3`; GSYM REAL_POW_POW] THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; ASSUME `&0 < Rs + a`;
             REAL_ARITH `&0 <= dl ==> &0 <= &1 + dl`; ASSUME `&0 <= dl`] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `~(Rs pow 3 = &0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    UNDISCH_TAC `~(Rs pow 3 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `X pow 2 = (&1 + dl) pow 3 * M * ((Rs + a) / Rs) pow 3` THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(&1 + dl) pow 3 <= &1 + &4 * t /\ ((Rs + a) / Rs) pow 3 <= &1 + &4 * t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &4 * dl` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + t) pow 3` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC P2BC_CUBE_BOUND THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + dl) pow 3 /\ &0 <= ((Rs + a) / Rs) pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + &4 * t) * M * (&1 + &4 * t)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * t * M <= t * M / &10` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `t * t * M = t * (t * M)`; REAL_ARITH `t * M / &10 = t * (M / &10)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `t * M <= (&1 / &10) * M ==> t * M <= M / &10`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Target clauses of a cap from pointwise closeness.  The scalar bound on    *)
(* necks (P2BC_NECK_SCALAR, from APX_NECK_CURV); the core facts of both      *)
(* chart types (P2BC_CORE_FACTS_BALL and P2BC_CORE_FACTS_TWISTED); the range *)
(* of R' and its supremum (P2BC_T_RANGE), the ratio clause (P2BC_T_RATIO),   *)
(* intrinsic distances (P2BC_T_DIAM) and the volume of the image             *)
(* (P2BC_T_VOL).                                                             *)
(* ========================================================================= *)

let P2BC_NECK_SCALAR = prove
 (`!u:A->bool. ?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps z e.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps z e
        ==> !w. w IN IMAGE e (rfs_neck_dom eps)
                ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g w`,
  GEN_TAC THEN
  MP_TAC(SPEC `u:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `y:real^3`]
                APX_NECK_SCALAR_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`;
                                  `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SIMP_TAC[]]);;

let P2BC_CORE_FACTS_BALL = prove
 (`!top atlas (b:real^3->A) (e':real^3->A) U Y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ mfd_ball_chart top atlas b /\
     IMAGE b (ball(vec 0,&2)) SUBSET U /\ Y = IMAGE b (ball(vec 0,&1)) /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1))
     ==> top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1)) /\
         top closure_of Y SUBSET U /\ compact_in top (top closure_of Y) /\ Y SUBSET U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`]
                APX_BALL_CORE_TOP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC]);;

let P2BC_CORE_FACTS_TWISTED = prove
 (`!top atlas (p:real^3->A) (e':real^3->A) U Y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ rfs_twisted_chart top atlas p /\
     IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\ Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2))
     ==> top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1)) /\
         top closure_of Y SUBSET U /\ compact_in top (top closure_of Y) /\ Y SUBSET U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`]
                APX_TWISTED_CORE_TOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let P2BC_T_RANGE = prove
 (`!(R:A->real) (R':B->real) psi U Rn Rs a x.
     x IN U /\ (!y. y IN U ==> Rn <= R y /\ R y <= Rs) /\
     (!y. y IN U ==> abs(R'(psi y) - R y) <= a) /\ &0 <= a /\ a < Rn
     ==> (!z. z IN IMAGE psi U ==> &0 < R' z /\ R' z <= Rs + a) /\
         &0 < sup(IMAGE R' (IMAGE psi U)) /\ sup(IMAGE R' (IMAGE psi U)) <= Rs + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN IMAGE (psi:A->B) U ==> &0 < (R':B->real) z /\ R' z <= Rs + a`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:A`)) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(IMAGE (R':B->real) (IMAGE (psi:A->B) U) = {}) /\
                (!w. w IN IMAGE R' (IMAGE psi U) ==> w <= Rs + a)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(psi:A->B) y`) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(R':B->real)((psi:A->B) x)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `Rs + a` THEN ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]]);;

let P2BC_T_RATIO = prove
 (`!(R:A->real) (R':B->real) psi U d4 C a Rn.
     (!y. y IN U ==> Rn <= R y) /\ (!y1 y2. y1 IN U /\ y2 IN U ==> R y2 <= d4 * R y1) /\
     (!y. y IN U ==> abs(R'(psi y) - R y) <= a) /\ &0 < Rn /\ &1 <= d4 /\ d4 < C /\
     &0 <= a /\ a * (&4 * (C + &1)) <= (C - d4) * Rn
     ==> rfs_sup_lt {R' y2 / R' y1 | y1 IN IMAGE psi U /\ y2 IN IMAGE psi U} C`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_sup_lt] THEN
  EXISTS_TAC `(d4 + C) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
  X_GEN_TAC `w:real` THEN MAP_EVERY X_GEN_TAC [`z1:B`; `z2:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:A` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y2:A` STRIP_ASSUME_TAC)) SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &4 * (C + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < Rn` ASSUME_TAC THENL
   [SUBGOAL_THEN `(C - d4) * Rn < (&4 * (C + &1)) * Rn` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a * (&4 * (C + &1)) < Rn * (&4 * (C + &1))` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rn <= (R:A->real) y1 /\ R y2 <= d4 * R y1 /\
                abs((R':B->real)((psi:A->B) y1) - R y1) <= a /\
                abs((R':B->real)((psi:A->B) y2) - R y2) <= a`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (R':B->real)((psi:A->B) y1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `a * (&1 + (d4 + C) / &2) <= ((C - d4) / &2) * (R:A->real) y1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * (&2 * (C + &1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((C - d4) / &2) * Rn` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d4 + C) / &2 * ((R:A->real) y1 - a) <=
                (d4 + C) / &2 * (R':B->real)((psi:A->B) y1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BC_T_DIAM = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U psi psi' d3 dl.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\ &0 <= dl /\
     (!y1 y2. y1 IN U /\ y2 IN U
              ==> mfd_joinable_in (top,atlas) U y1 y2 /\
                  mfd_dist_in (top,atlas) g U y1 y2 <= d3) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                (&1 + dl) * (v dot (g y ** v)))
     ==> !z1 z2. z1 IN IMAGE psi U /\ z2 IN IMAGE psi U
                 ==> mfd_joinable_in (top',atlas') (IMAGE psi U) z1 z2 /\
                     mfd_dist_in (top',atlas') g' (IMAGE psi U) z1 z2 <= sqrt(&1 + dl) * d3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y1:A` THEN DISCH_TAC THEN X_GEN_TAC `y2:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`; `U:A->bool`;
                 `&1 + dl`; `y1:A`; `y2:A`] P2B9S_DIST_IN_PB_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + dl) * mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d3:real`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

let P2BC_T_VOL = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U psi psi' x D v0 dl.
     hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_complete (top',atlas') g' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\ x IN U /\ &0 <= dl /\
     (!z1 z2. z1 IN IMAGE psi U /\ z2 IN IMAGE psi U
              ==> mfd_joinable_in (top',atlas') (IMAGE psi U) z1 z2 /\
                  mfd_dist_in (top',atlas') g' (IMAGE psi U) z1 z2 <= D) /\
     mfd_has_volume (top,atlas) g U v0 /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                (&1 + dl) * (v dot (g y ** v)))
     ==> ?v'. mfd_has_volume (top',atlas') g' (IMAGE psi U) v' /\
              v' <= (&1 + dl) * sqrt(&1 + dl) * v0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(psi:A->B) x IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) U SUBSET
                mfd_cball (top',atlas':((B->bool)#(B->real^3))->bool) (g':B->real^3^3) (psi x) D`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(psi:A->B) x`; `q:B`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `D:real`)) (concl th))) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN EXISTS_TAC `IMAGE (psi:A->B) U` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist_in (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) U)
                    (psi x) q` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `mfd_cball (top',atlas') (g':B->real^3^3) ((psi:A->B) x) D`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_complete (top',atlas') (g':B->real^3^3)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `wc:real`)] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `IMAGE (psi:A->B) U`;
                 `mfd_cball (top',atlas') (g':B->real^3^3) ((psi:A->B) x) D`; `wc:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN]; STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) U)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`; `U:A->bool`;
                 `v0:real`;
                 `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) U)`;
                 `&1 + dl`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The common core of the cap case of P2_PROP_9_79_OPEN.  P2BC_EXISTS_SMALL  *)
(* chooses one positive alpha below finitely many positive ratios;           *)
(* P2BC_QF_LAM turns a two-sided (1 +/- d) comparison of quadratic forms     *)
(* into one-sided bounds with factor 1 + 2d; P2BC_INV_SQRT_MONO is the       *)
(* monotonicity of C / sqrt s and C / sqrt s ^ 3. P2BC_OPEN_CAP_COMMON:      *)
(* given the source cap clauses, the source neck at the core boundary and a  *)
(* transfer of the chart data (hypothesis dc), a delta with rfs_mclose ==>   *)
(* rfs_cap for the image.  Clause (7) comes from P2BC_CLAUSE7 with lam = 1 + *)
(* 2 delta, the other clauses from the margins (P2BC_MARGIN_DIAM,            *)
(* P2BC_MARGIN_VOL, P2B9S_MARGIN_GRAD_POLY, ..._LAP_POLY) and the target     *)
(* lemmas of the previous section.                                           *)
(* ========================================================================= *)

let P2BC_EXISTS_SMALL = prove
 (`!l. (!c b. MEM (c,b) l ==> &0 < c /\ &0 < b)
       ==> ?a. &0 < a /\ !c b. MEM (c,b) l ==> a * c <= b`,
  LIST_INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[MEM; REAL_LT_01];
    ALL_TAC] THEN
  SPEC_TAC(`h:real#real`,`h:real#real`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`c0:real`; `b0:real`] THEN
  REWRITE_TAC[MEM; PAIR_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c0 /\ &0 < b0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`c0:real`; `b0:real`]) THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `b:real`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `b:real`]) THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a0:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `min a0 (b0 / c0)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `b:real`] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(b0 / c0) * c0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    SUBGOAL_THEN `&0 < c /\ a0 * c <= b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `b:real`] o check (fun th ->
          can (find_term ((=) `c0:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `b:real`] o check (fun th ->
          can (find_term ((=) `a0:real`)) (concl th) && is_forall (concl th))) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a0 * c` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

let P2BC_QF_LAM = prove
 (`!d q p. &0 < d /\ d <= &1 / &2 /\ (&1 - d) * q <= p /\ p <= (&1 + d) * q
           ==> p <= (&1 + &2 * d) * q /\ q <= (&1 + &2 * d) * p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < d * --q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d * q /\ &0 <= d * (&1 - &2 * d) * q /\
                (&1 + &2 * d) * ((&1 - d) * q) <= (&1 + &2 * d) * p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let P2BC_INV_SQRT_MONO = prove
 (`!C s t. &0 <= C /\ &0 < s /\ s <= t
           ==> C * inv(sqrt t) <= C * inv(sqrt s) /\
               C * inv(sqrt t pow 3) <= C * inv(sqrt s pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt s /\ sqrt s <= sqrt t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let SPDR7_ASM_REAL_ARITH_TAC : tactic =
  let rty = `:real` in
  let aops = ["real_add"; "real_sub"; "real_mul"; "real_div"; "real_neg"; "real_inv";
              "real_abs"; "real_max"; "real_min"; "real_pow"] in
  let cname t = if is_const t then fst(dest_const t) else "" in
  let rec leaves tm acc =
    if is_comb tm && cname (rator tm) = "real_of_num" then
      (if is_numeral (rand tm) then acc else insert tm acc)
    else if (is_comb tm && cname (rator tm) = "DECIMAL") ||
            (is_comb tm && is_comb (rator tm) && cname (rator (rator tm)) = "DECIMAL") ||
            is_const tm then acc
    else let f,args = strip_comb tm in
         if is_const f && mem (fst(dest_const f)) aops && args <> [] then
           itlist leaves (filter (fun a -> type_of a = rty) args) acc
         else insert tm acc in
  let is_rrel tm =
    is_comb tm && is_comb (rator tm) &&
    (let c = rator (rator tm) in
     is_const c &&
     (let s,ty = dest_const c in
      mem s ["real_le"; "real_lt"; "real_ge"; "real_gt"] ||
      (s = "=" && (match dest_type ty with "fun",[ty1;_] -> ty1 = rty | _ -> false)))) in
  let rec atoms tm acc =
    if is_comb tm && cname (rator tm) = "~" then atoms (rand tm) acc
    else if is_comb tm && is_comb (rator tm) &&
            mem (cname (rator (rator tm))) ["/\\"; "\\/"; "==>"] then
      atoms (rand (rator tm)) (atoms (rand tm) acc)
    else if is_comb tm && is_comb (rator tm) && cname (rator (rator tm)) = "=" &&
            (match dest_type (type_of (rator (rator tm))) with
               "fun",[a;_] -> a = bool_ty | _ -> false) then
      atoms (rand (rator tm)) (atoms (rand tm) acc)
    else if is_const tm && mem (fst(dest_const tm)) ["T"; "F"] then acc
    else if is_rrel tm then leaves (lhand tm) (leaves (rand tm) acc) else insert tm acc in
  let levels n (asl,w) =
    let cands = map (fun (_,th) -> th,atoms (concl th) [])
                    (filter (fun (_,th) -> not(is_forall(concl th))) asl) in
    let rec go k s sel rest =
      if k = 0 then [] else
      let now,later = partition (fun (_,a) -> exists (fun x -> mem x s) a) rest in
      if now = [] then [] else
      let sel' = sel @ map fst now in
      sel' :: go (k - 1) (itlist (fun (_,a) acc -> union a acc) now s) sel' later in
    [] :: go n (atoms w []) [] cands in
  fun (asl,w as g) ->
    if w = `F` then ASM_REAL_ARITH_TAC g
    else if is_forall w || is_exists w then failwith "SPDR7_ASM_REAL_ARITH_TAC"
    else tryfind (fun hs -> (MAP_EVERY MP_TAC hs THEN REAL_ARITH_TAC) g) (levels 3 g);;

let P2BC_OPEN_CAP_COMMON = prove
 (`!eps1B C eps top atlas (g:A->real^3^3) x U Y zb eb.
     (!top' atlas' (g':B->real^3^3) eps z e.
         &0 < eps /\ eps <= eps1B /\ riemannian_metric atlas' g' /\
         rfs_neck (top',atlas') g' eps z e
         ==> !w. w IN IMAGE e (rfs_neck_dom eps)
                 ==> mfd_scalar atlas' g' z / &2 <= mfd_scalar atlas' g' w) /\
     P2B_REQ_LRG_DERIV_STATEMENT /\
     &1 < C /\ &0 < eps /\ eps <= &1 / &4 /\ eps <= eps1B /\ hausdorff_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top U /\ compact_in top (top closure_of U) /\ Y SUBSET U /\ x IN Y /\
     (!y1 y2. y1 IN U /\ y2 IN U ==> mfd_joinable_in (top,atlas) U y1 y2) /\
     (!y. y IN U ==> &0 < mfd_scalar atlas g y) /\
     rfs_sup_lt {mfd_dist_in (top,atlas) g U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U}
                (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)))) /\
     rfs_sup_lt {mfd_scalar atlas g y2 / mfd_scalar atlas g y1 |
                 y1 IN U /\ y2 IN U} C /\
     (?v. mfd_has_volume (top,atlas) g U v /\
          v < C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)) pow 3)) /\
     (?d. inv C < d /\
          !y r. y IN Y /\ &0 < r /\
                (?B. !z. z IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g z <= B) /\
                sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) =
                inv(r pow 2)
                ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                    top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                    ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                        d <= v / r pow 3) /\
     rfs_sup_lt {sqrt(rfs_scalar_grad2 atlas g y) /
                 (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) | y IN U} C /\
     rfs_sup_lt {abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                 mfd_scalar atlas g y pow 2 | y IN U} C /\
     rfs_neck (top,atlas) g eps zb eb /\ IMAGE eb (rfs_neck_dom eps) SUBSET U /\
     top frontier_of (top closure_of Y) SUBSET IMAGE eb (sphere(vec 0,&1)) /\
     top closure_of Y SUBSET U /\
     (!w. w IN IMAGE eb (rfs_neck_dom eps)
          ==> mfd_scalar atlas g zb / &2 <= mfd_scalar atlas g w) /\
     (?dc. &0 < dc /\
           !delta top' atlas' (g':B->real^3^3) psi psi'.
             &0 < delta /\ delta <= dc /\ hausdorff_space top' /\
             smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
             mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
             rfs_mclose (rfs_kreg delta) delta atlas U (\y. mfd_scalar atlas g x %% g y)
               (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
             ==> ((?b e e' z z' f f'.
                     mfd_ball_chart top' atlas' b /\ IMAGE b (ball(vec 0,&2)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE b (ball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) = IMAGE psi U DIFF IMAGE b (cball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) \/
                  (?p e e' z z' f f'.
                     rfs_twisted_chart top' atlas' p /\
                     IMAGE p (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE p (annulus (&1 / &2) (&2)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) =
                       IMAGE psi U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))))) /\
                 rfs_neck (top',atlas') g' eps (psi zb) (psi o eb) /\
                 top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                   IMAGE (psi o eb) (sphere(vec 0,&1)) /\
                 top' closure_of IMAGE psi Y SUBSET IMAGE psi U /\
                 IMAGE (psi o eb) (rfs_neck_dom eps) SUBSET IMAGE psi U)
     ==> ?delta. &0 < delta /\
           !top' atlas' (g':B->real^3^3) psi psi'.
              hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
              riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_mclose (rfs_kreg delta) delta atlas U
                (\y. mfd_scalar atlas g x %% g y)
                (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> rfs_cap (top',atlas') g' C eps (IMAGE psi U) (IMAGE psi Y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "NSB") (CONJUNCTS_THEN2
    (LABEL_TAC "LRGD" o MATCH_MP P2B9S_LRG_D) STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "mfd_dist_in"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d9:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_grad2"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d10:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_lap"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN Y` THEN UNDISCH_TAC `(Y:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [EXPAND_TAC "R0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN U /\ y2 IN U
                        ==> mfd_scalar atlas (g:A->real^3^3) y2 <= d4 * mfd_scalar atlas g y1`
  (LABEL_TAC "RAT") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) y2 / mfd_scalar atlas g y1` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `d4:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`y2:A`; `y1:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= d4` ASSUME_TAC THENL
   [USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:A`; `x:A`] th)
      (CONJ (ASSUME `(x:A) IN U`) (ASSUME `(x:A) IN U`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 * R0 <= d4 * R0` MP_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R0 / d4 /\ R0 / d4 <= d4 * R0 /\ (R0 / d4) * d4 = R0 /\
                (!y. y IN U ==> R0 / d4 <= mfd_scalar atlas (g:A->real^3^3) y /\
                                mfd_scalar atlas g y <= d4 * R0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < d4` ASSUME_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R0:real` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SPDR7_ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`y:A`; `x:A`] th)
        (CONJ (ASSUME `(y:A) IN U`) (ASSUME `(x:A) IN U`)))) THEN
      USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:A`; `y:A`] th)
        (CONJ (ASSUME `(x:A) IN U`) (ASSUME `(y:A) IN U`)))) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Rn = R0 / d4` THEN ABBREV_TAC `Rm = d4 * R0` THEN
  ABBREV_TAC `Rs = sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `(!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= Rs) /\
                R0 <= Rs /\ Rs <= Rm /\ &0 < Rs`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= Rs` ASSUME_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXPAND_TAC "Rs" THEN
      MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `Rm:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R0 <= Rs` ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN U`))) o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `Rs:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Rs" THEN MATCH_MP_TAC REAL_SUP_LE THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      CONJ_TAC THENL [UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[]; ASM_SIMP_TAC[]];
      SPDR7_ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d3 /\ &0 <= v /\ &0 <= d9 /\ &0 <= d10` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U x x` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_IN_POS_LE THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d3:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `x:A`] THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `U:A->bool`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(rfs_scalar_grad2 atlas (g:A->real^3^3) x) /
                  (mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P2B9S_GRAD2_POS THEN
          EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[OPEN_IN_SUBSET; SUBSET; ASSUME `open_in top (U:A->bool)`;
                    ASSUME `(x:A) IN U`];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE]];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d9:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(rfs_scalar_lap atlas (g:A->real^3^3) x + &2 * rfs_ric_norm2 atlas g x) /
                  mfd_scalar atlas g x pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d10:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET top closure_of U` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?K0. !y. y IN U
             ==> rfa_rmd2 0 atlas (\z. R0 %% (g:A->real^3^3) z) y <= K0 /\
                 rfa_rmd2 1 atlas (\z. R0 %% g z) y <= K0 /\
                 rfa_rmd2 2 atlas (\z. R0 %% g z) y <= K0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `riemannian_metric atlas (\z. R0 %% (g:A->real^3^3) z)` ASSUME_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY (fun l -> MP_TAC(ISPECL [l; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. R0 %% (g:A->real^3^3) z`; `top closure_of (U:A->bool)`]
                P2B9S_RMD2_COMPACT_BOUND)) [`2`; `1`; `0`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN
    EXISTS_TAC `max B0 (max B1 B2)` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN top closure_of U` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN U` THEN UNDISCH_TAC `(U:A->bool) SUBSET top closure_of U` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_MAX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top closure_of (U:A->bool)`] P2BC_RICCI_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Kr:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y w. y IN U
                      ==> --(&2 * Kr) * (w dot ((g:A->real^3^3) y ** w)) <=
                          mfd_ricci atlas g y w w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:A) IN U` THEN UNDISCH_TAC `(U:A->bool) SUBSET top closure_of U` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`; `Y:A->bool`; `C:real`; `eps:real`; `zb:A`; `eb:real^3->A`;
                 `Rn:real`; `Rm:real`; `Kr:real`; `d:real`]
                (INST_TYPE [`:B`,`:B`] P2BC_CLAUSE7)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `eta7:real` (X_CHOOSE_THEN `d7:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C7")))))] THEN
  MP_TAC(SPECL [`d3:real`; `Rs:real`; `C:real`] P2BC_MARGIN_DIAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t3:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MD")))) THEN
  MP_TAC(SPECL [`v:real`; `Rs:real`; `C:real`] P2BC_MARGIN_VOL) THEN
  ASM_REWRITE_TAC[REAL_POW_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t5:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MV")))) THEN
  ABBREV_TAC `m = Rn / R0` THEN
  SUBGOAL_THEN `&0 < m /\ m * R0 = Rn` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `E9 = (d9 + C) / &2` THEN ABBREV_TAC `E10 = (d10 + C) / &2` THEN
  SUBGOAL_THEN `d9 < E9 /\ E9 < C /\ d10 < E10 /\ E10 < C /\ &0 < E9 pow 2 - d9 pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E9"; "E10"] THEN REPEAT CONJ_TAC THEN TRY SPDR7_ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_ARITH `x pow 2 - y pow 2 = (x - y) * (x + y)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `[R0, Rn / &4; R0 * (&4 * (C + &1)), (C - d4) * Rn; R0, eta7 * Rn / &8;
                 R0, t3; R0, t5 * Rs;
                 &1 + &3 * E9 pow 2 * m pow 2, (E9 pow 2 - d9 pow 2) * m pow 3;
                 &3 + &2 * E10 * m, (E10 - d10) * m pow 2; &3, m]` P2BC_EXISTS_SMALL) THEN
  SUBGOAL_THEN `&0 < R0 * (&4 * (C + &1)) /\ &0 < (C - d4) * Rn /\ &0 < eta7 * Rn / &8 /\
                &0 < t5 * Rs /\ &0 < &1 + &3 * E9 pow 2 * m pow 2 /\
                &0 < (E9 pow 2 - d9 pow 2) * m pow 3 /\ &0 < &3 + &2 * E10 * m /\
                &0 < (E10 - d10) * m pow 2 /\ &0 < Rn / &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + &3 * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &3 + &2 * x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN SPDR7_ASM_REAL_ARITH_TAC;
      SPDR7_ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `alpha:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AL")))] THEN
  SUBGOAL_THEN `alpha * R0 <= Rn / &4 /\ alpha * (R0 * (&4 * (C + &1))) <= (C - d4) * Rn /\
                alpha * R0 <= eta7 * Rn / &8 /\ alpha * R0 <= t3 /\ alpha * R0 <= t5 * Rs /\
                alpha * (&1 + &3 * E9 pow 2 * m pow 2) <= (E9 pow 2 - d9 pow 2) * m pow 3 /\
                alpha * (&3 + &2 * E10 * m) <= (E10 - d10) * m pow 2 /\ alpha * &3 <= m`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "AL" MATCH_MP_TAC THEN REWRITE_TAC[MEM; PAIR_EQ];
    ALL_TAC] THEN
  USE_THEN "LRGD" (fun th -> MP_TAC(MATCH_MP (SPECL [`K0:real`; `alpha:real`] th)
                                            (ASSUME `&0 < alpha`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dform"))) THEN
  EXISTS_TAC `min (&1 / &10) (min eta (min dc (min (eta7 / &2) (min t3 t5))))` THEN
  ABBREV_TAC `delta = min (&1 / &10) (min eta (min dc (min (eta7 / &2) (min t3 t5))))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ delta <= eta /\ delta <= dc /\
                delta <= eta7 / &2 /\ delta <= t3 /\ delta <= t5`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_mclose" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0 /\
            (!u v. ~collinear {vec 0,u,v}
                   ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                           mfd_sectional atlas g y u v) <= alpha * R0) /\
            abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y) <=
            alpha * R0 pow 3 /\
            abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R0 pow 2 /\
            abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R0 pow 2 /\
            (!v. v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                 (&1 + delta) * (v dot (g y ** v))) /\
            (!v. (&1 - delta) * (v dot (g y ** v)) <=
                 v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_TARGET_POINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`; `K0:real`; `eta:real`;
                          `d2:real`] THEN
    ASM_SIMP_TAC[] THEN TRY(CONJ_TAC THENL [USE_THEN "Dform" ACCEPT_TAC; ALL_TAC]) THEN
    SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`delta:real`; `top':B topology`;
                                `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                                `psi:A->B`; `psi':B->A`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `dc:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CH") STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_diffeo"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN
   `(!y. y IN U ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                        mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0) /\
    (!y v. y IN U ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                      (&1 + delta) * (v dot (g y ** v))) /\
    (!y v. y IN U ==> (&1 - delta) * (v dot (g y ** v)) <=
                      v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (CONJUNCTS_THEN2 (LABEL_TAC "ABS") (CONJUNCTS_THEN2 (LABEL_TAC "PBU") (LABEL_TAC "PBL")))
  THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y1 y2. y1 IN U /\ y2 IN U
             ==> mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2 <= d3) /\
    (!y. y IN U ==> sqrt(rfs_scalar_grad2 atlas g y) /
                    (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) <= d9) /\
    (!y. y IN U ==> abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                    mfd_scalar atlas g y pow 2 <= d10)`
  (CONJUNCTS_THEN2 (LABEL_TAC "D3") (CONJUNCTS_THEN2 (LABEL_TAC "G9") (LABEL_TAC "L10")))
  THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d3:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`y1:A`; `y2:A`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d9:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d10:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN U ==> Rn <= mfd_scalar atlas (g:A->real^3^3) y /\ mfd_scalar atlas g y <= Rs) /\
    (!y. y IN U ==> Rn <= mfd_scalar atlas (g:A->real^3^3) y) /\
    &0 <= alpha * R0 /\ alpha * R0 < Rn /\ &0 <= delta /\
    (alpha * R0) * (&4 * (C + &1)) <= (C - d4) * Rn /\
    (!y1 y2. y1 IN U /\ y2 IN U
             ==> mfd_joinable_in (top,atlas) U y1 y2 /\
                 mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2 <= d3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      SPDR7_ASM_REAL_ARITH_TAC;
      SPDR7_ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `mfd_scalar atlas' (g':B->real^3^3)`;
                 `psi:A->B`; `U:A->bool`; `Rn:real`; `Rs:real`; `alpha * R0`; `x:A`]
                P2BC_T_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `mfd_scalar atlas' (g':B->real^3^3)`;
                 `psi:A->B`; `U:A->bool`; `d4:real`; `C:real`; `alpha * R0`; `Rn:real`]
                P2BC_T_RATIO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `psi:A->B`; `psi':B->A`; `d3:real`; `delta:real`]
                P2BC_T_DIAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "TD") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `psi:A->B`; `psi':B->A`; `x:A`; `sqrt(&1 + delta) * d3`;
                 `v:real`; `delta:real`] P2BC_T_VOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "MD" (MP_TAC o SPECL [`delta:real`; `alpha * R0`]) THEN
  ANTS_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "MV" (MP_TAC o SPECL [`delta:real`; `alpha * R0`]) THEN
  ANTS_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`C:real`;
                `sup(IMAGE (mfd_scalar atlas' (g':B->real^3^3)) (IMAGE (psi:A->B) U))`;
                `Rs + alpha * R0`] P2BC_INV_SQRT_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(zb:A) IN U` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps zb eb` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (eb:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
    UNDISCH_TAC `(zb:A) IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rn <= mfd_scalar atlas (g:A->real^3^3) zb` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))
                    ==> mfd_scalar atlas (g:A->real^3^3) zb / &4 <=
                        mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:A) IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `IMAGE (eb:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPEC `w:A` (ASSUME `!w. w IN IMAGE (eb:real^3->A) (rfs_neck_dom eps)
                                   ==> mfd_scalar atlas (g:A->real^3^3) zb / &2 <=
                                       mfd_scalar atlas g w`))
                    (ASSUME `(w:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps)`)) THEN
    USE_THEN "ABS" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(w:A) IN U`))) THEN
    UNDISCH_TAC `alpha * R0 <= Rn / &4` THEN
    UNDISCH_TAC `Rn <= mfd_scalar atlas (g:A->real^3^3) zb` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "NSB" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                  `g':B->real^3^3`; `eps:real`; `(psi:A->B) zb`;
                                  `(psi:A->B) o (eb:real^3->A)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!w. w IN IMAGE ((psi:A->B) o (eb:real^3->A)) (sphere(vec 0,&1))
                    ==> mfd_scalar atlas' (g':B->real^3^3) (psi zb) / &2 <=
                        mfd_scalar atlas' g' w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:B) IN IMAGE ((psi:A->B) o (eb:real^3->A)) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y v. y IN U
           ==> v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** v) <=
               (&1 + &2 * delta) * (v dot ((g:A->real^3^3) y ** v))) /\
    (!y v. y IN U
           ==> v dot (g y ** v) <=
               (&1 + &2 * delta) * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:A` THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`delta:real`; `w dot ((g:A->real^3^3) y ** w)`;
                  `w dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** w)`]
                 P2BC_QF_LAM) THEN
    (ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [ASM_REWRITE_TAC[];
         SPDR7_ASM_REAL_ARITH_TAC;
         USE_THEN "PBL" (fun th -> ACCEPT_TAC(MATCH_MP (SPECL [`y:A`; `w:real^3`] th)
                                                       (ASSUME `(y:A) IN U`)));
         USE_THEN "PBU" (fun th -> ACCEPT_TAC(MATCH_MP (SPECL [`y:A`; `w:real^3`] th)
                                                       (ASSUME `(y:A) IN U`)))];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  USE_THEN "C7" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                 `g':B->real^3^3`; `psi:A->B`; `psi':B->A`;
                                 `&1 + &2 * delta`; `alpha * R0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "C7T")] THEN
  REWRITE_TAC[rfs_cap] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "CH" ACCEPT_TAC;
    ASM_SIMP_TAC[];
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `sqrt(&1 + delta) * d3` THEN CONJ_TAC THENL
     [SPDR7_ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:real`; `z1:B`; `z2:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
      USE_THEN "TD" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(z1:B) IN IMAGE (psi:A->B) U`)
              (ASSUME `(z2:B) IN IMAGE (psi:A->B) U`)))) THEN
      SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    EXISTS_TAC `v1:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; SPDR7_ASM_REAL_ARITH_TAC];
    EXISTS_TAC `d7:real` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; USE_THEN "C7T" ACCEPT_TAC];
    REWRITE_TAC[rfs_sup_lt] THEN
    EXISTS_TAC `E9:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`));
        MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`))] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`; `d9:real`]
                 P2B9S_GRAD_RATIO_IMP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `d9:real`; `E9:real`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas' (g':B->real^3^3) ((psi:A->B) y)`; `alpha:real`]
                 P2B9S_MARGIN_GRAD_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_GRAD_RATIO_BACK THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      SPDR7_ASM_REAL_ARITH_TAC];
    REWRITE_TAC[rfs_sup_lt] THEN
    EXISTS_TAC `E10:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\ m * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `d10:real`] P2B9S_LAP_RATIO_IMP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`m:real`; `R0:real`; `d10:real`; `E10:real`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `rfs_scalar_lap atlas' (g':B->real^3^3) ((psi:A->B) y) +
                   &2 * rfs_ric_norm2 atlas' g' (psi y)`; `alpha:real`]
                 P2B9S_MARGIN_LAP_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_LAP_RATIO_BACK THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The cap case and the open form of MT Prop 9.79.  P2BC_CAP_DC_BALL and     *)
(* P2BC_CAP_DC_TWISTED transfer the chart data of a cap (both necks through  *)
(* P2BC_NECK_TRANSFER, the charts through P2BC_CHART_BALL or                 *)
(* P2BC_CHART_TWISTED, the core facts of the target). P2BC_OPEN_CAP: for eps *)
(* <= eps0 every cap with compact closure stays a cap with core IMAGE psi Y  *)
(* under close complete targets (from P2BC_OPEN_CAP_COMMON).                 *)
(* P2_PROP_9_79_OPEN: the four alternatives of a canonical neighbourhood     *)
(* (neck P2B9S_OPEN_NECK, cap, C-component P2B9S_OPEN_CCOMP_U, round         *)
(* component P2B9S_OPEN_ROUND with R(x) > 0 from APX_ROUND_SECTIONAL for eps *)
(* <= 1/40).                                                                 *)
(* ========================================================================= *)

let P2BC_CAP_DC_BALL = prove
 (`!top atlas (g:A->real^3^3) U Y eps R0 b e e' z z' f f'.
     &0 < eps /\ eps < &1 / &4 /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ &0 < R0 /\
     mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
     Y = IMAGE b (ball(vec 0,&1)) /\
     rfs_neck (top,atlas) g eps z e /\
     IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
     rfs_neck (top,atlas) g eps z' e' /\
     IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))
     ==> ?dc. &0 < dc /\
           !delta top' atlas' (g':B->real^3^3) psi psi'.
             &0 < delta /\ delta <= dc /\ hausdorff_space top' /\
             smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
             mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
             rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% g y)
               (\y. R0 %% mfd_pullback_metric atlas atlas' psi g' y)
             ==> ((?b e e' z z' f f'.
                     mfd_ball_chart top' atlas' b /\ IMAGE b (ball(vec 0,&2)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE b (ball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) = IMAGE psi U DIFF IMAGE b (cball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) \/
                  (?p e e' z z' f f'.
                     rfs_twisted_chart top' atlas' p /\
                     IMAGE p (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE p (annulus (&1 / &2) (&2)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) =
                       IMAGE psi U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))))) /\
                 rfs_neck (top',atlas') g' eps (psi z') (psi o e') /\
                 top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                   IMAGE (psi o e') (sphere(vec 0,&1)) /\
                 top' closure_of IMAGE psi Y SUBSET IMAGE psi U /\
                 IMAGE (psi o e') (rfs_neck_dom eps) SUBSET IMAGE psi U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z:A`; `e:real^3->A`; `U:A->bool`; `R0:real`]
                P2BC_NECK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))] THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z':A`; `e':real^3->A`; `U:A->bool`; `R0:real`]
                P2BC_NECK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N2")))] THEN
  EXISTS_TAC `min d1 d2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; REWRITE_TAC[REAL_LE_MIN]] THEN
  MAP_EVERY X_GEN_TAC [`delta:real`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck (top',atlas') (g':B->real^3^3) eps ((psi:A->B) z) (psi o (e:real^3->A)) /\
                rfs_neck (top',atlas') g' eps (psi z') (psi o (e':real^3->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`delta:real`; `psi':B->A`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "N2" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`delta:real`; `psi':B->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `U:A->bool`;
                 `psi:A->B`; `psi':B->A`; `Y:A->bool`; `eps:real`; `b:real^3->A`;
                 `e:real^3->A`; `e':real^3->A`; `z:A`; `z':A`; `f:real^3->real^3`;
                 `f':real^3->real^3`] P2BC_CHART_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(psi:A->B) o (b:real^3->A)`; `(psi:A->B) o (e':real^3->A)`;
                 `IMAGE (psi:A->B) U`; `IMAGE (psi:A->B) Y`] P2BC_CORE_FACTS_BALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`(psi:A->B) o (b:real^3->A)`; `(psi:A->B) o (e:real^3->A)`;
                          `(psi:A->B) o (e':real^3->A)`; `(psi:A->B) z`; `(psi:A->B) z'`;
                          `f:real^3->real^3`; `f':real^3->real^3`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let P2BC_CAP_DC_TWISTED = prove
 (`!top atlas (g:A->real^3^3) U Y eps R0 p e e' z z' f f'.
     &0 < eps /\ eps < &1 / &4 /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ &0 < R0 /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
     Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     rfs_neck (top,atlas) g eps z e /\
     IMAGE e (rfs_neck_dom eps) =
       U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
     rfs_neck (top,atlas) g eps z' e' /\
     IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y)))
     ==> ?dc. &0 < dc /\
           !delta top' atlas' (g':B->real^3^3) psi psi'.
             &0 < delta /\ delta <= dc /\ hausdorff_space top' /\
             smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
             mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
             rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% g y)
               (\y. R0 %% mfd_pullback_metric atlas atlas' psi g' y)
             ==> ((?b e e' z z' f f'.
                     mfd_ball_chart top' atlas' b /\ IMAGE b (ball(vec 0,&2)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE b (ball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) = IMAGE psi U DIFF IMAGE b (cball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) \/
                  (?p e e' z z' f f'.
                     rfs_twisted_chart top' atlas' p /\
                     IMAGE p (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U /\
                     IMAGE psi Y = IMAGE p (annulus (&1 / &2) (&2)) /\
                     rfs_neck (top',atlas') g' eps z e /\
                     IMAGE e (rfs_neck_dom eps) =
                       IMAGE psi U DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
                     rfs_neck (top',atlas') g' eps z' e' /\
                     IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE psi U /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))))) /\
                 rfs_neck (top',atlas') g' eps (psi z') (psi o e') /\
                 top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                   IMAGE (psi o e') (sphere(vec 0,&1)) /\
                 top' closure_of IMAGE psi Y SUBSET IMAGE psi U /\
                 IMAGE (psi o e') (rfs_neck_dom eps) SUBSET IMAGE psi U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z:A`; `e:real^3->A`; `U:A->bool`; `R0:real`]
                P2BC_NECK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))] THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `z':A`; `e':real^3->A`; `U:A->bool`; `R0:real`]
                P2BC_NECK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N2")))] THEN
  EXISTS_TAC `min d1 d2` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; REWRITE_TAC[REAL_LE_MIN]] THEN
  MAP_EVERY X_GEN_TAC [`delta:real`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `psi:A->B`; `psi':B->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck (top',atlas') (g':B->real^3^3) eps ((psi:A->B) z) (psi o (e:real^3->A)) /\
                rfs_neck (top',atlas') g' eps (psi z') (psi o (e':real^3->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "N1" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`delta:real`; `psi':B->A`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "N2" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`delta:real`; `psi':B->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `U:A->bool`;
                 `psi:A->B`; `psi':B->A`; `Y:A->bool`; `eps:real`; `p:real^3->A`;
                 `e:real^3->A`; `e':real^3->A`; `z:A`; `z':A`; `f:real^3->real^3`;
                 `f':real^3->real^3`] P2BC_CHART_TWISTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(psi:A->B) o (p:real^3->A)`; `(psi:A->B) o (e':real^3->A)`;
                 `IMAGE (psi:A->B) U`; `IMAGE (psi:A->B) Y`] P2BC_CORE_FACTS_TWISTED) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`(psi:A->B) o (p:real^3->A)`; `(psi:A->B) o (e:real^3->A)`;
                          `(psi:A->B) o (e':real^3->A)`; `(psi:A->B) z`; `(psi:A->B) z'`;
                          `f:real^3->real^3`; `f':real^3->real^3`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let P2BC_OPEN_CAP = prove
 (`P2B_REQ_LRG_DERIV_STATEMENT
   ==> ?eps0. &0 < eps0 /\ eps0 <= &1 / &8 /\
         !C eps top atlas (g:A->real^3^3) x U Y.
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
           smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
           rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
           compact_in top (top closure_of U)
           ==> ?delta. &0 < delta /\
                 !top' atlas' (g':B->real^3^3) psi psi'.
                    hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
                    riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
                    mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                    rfs_mclose (rfs_kreg delta) delta atlas U
                      (\y. mfd_scalar atlas g x %% g y)
                      (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                    ==> rfs_cap (top',atlas') g' C eps (IMAGE psi U) (IMAGE psi Y)`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `UNIV:A->bool` P2BC_NECK_SCALAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1A:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NSA"))) THEN
  MP_TAC(ISPEC `UNIV:B->bool` P2BC_NECK_SCALAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NSB"))) THEN
  EXISTS_TAC `min (&1 / &8) (min eps1A eps1B)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_cap"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CHS") (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  SUBGOAL_THEN `eps < &1 / &4 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "CHS" (DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:real^3->A` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC))))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `b:real^3->A`; `e':real^3->A`; `U:A->bool`; `Y:A->bool`]
                  P2BC_CORE_FACTS_BALL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(x:A) IN Y` THEN
      UNDISCH_TAC `(Y:A->bool) SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `U:A->bool`; `Y:A->bool`; `eps:real`; `mfd_scalar atlas (g:A->real^3^3) x`;
                   `b:real^3->A`; `e:real^3->A`; `e':real^3->A`; `z:A`; `z':A`;
                   `f:real^3->real^3`; `f':real^3->real^3`] P2BC_CAP_DC_BALL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    USE_THEN "NSA" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `g:A->real^3^3`; `eps:real`; `z':A`; `e':real^3->A`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`eps1B:real`; `C:real`; `eps:real`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
                   `U:A->bool`; `Y:A->bool`; `z':A`; `e':real^3->A`] P2BC_OPEN_CAP_COMMON) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->A` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC))))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `p:real^3->A`; `e':real^3->A`; `U:A->bool`; `Y:A->bool`]
                  P2BC_CORE_FACTS_TWISTED) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(x:A) IN Y` THEN
      UNDISCH_TAC `(Y:A->bool) SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `U:A->bool`; `Y:A->bool`; `eps:real`; `mfd_scalar atlas (g:A->real^3^3) x`;
                   `p:real^3->A`; `e:real^3->A`; `e':real^3->A`; `z:A`; `z':A`;
                   `f:real^3->real^3`; `f':real^3->real^3`] P2BC_CAP_DC_TWISTED) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    USE_THEN "NSA" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `g:A->real^3^3`; `eps:real`; `z':A`; `e':real^3->A`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`eps1B:real`; `C:real`; `eps:real`; `top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
                   `U:A->bool`; `Y:A->bool`; `z':A`; `e':real^3->A`] P2BC_OPEN_CAP_COMMON) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

let P2_PROP_9_79_OPEN = prove
 (`!(u:A->bool) (w:B->bool). P2_PROP_9_79_OPEN_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2_PROP_9_79_OPEN_STATEMENT] THEN
  MP_TAC(MATCH_MP P2BC_OPEN_CAP P2B_REQ_LRG_DERIV) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsc:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAP")))) THEN
  EXISTS_TAC `min (&1 / &40) epsc` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
                       `U:A->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) o
    GEN_REWRITE_RULE I [rfs_canonical_nbhd] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_canonical_nbhd"
                     with Failure _ -> false)) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `e:real^3->A`] P2B9S_OPEN_NECK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NK"))) THEN
    EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
    STRIP_TAC THEN REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ1_TAC THEN
    EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN CONJ_TAC THENL
     [USE_THEN "NK" MATCH_MP_TAC THEN EXISTS_TAC `psi':B->A` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_o]];
    USE_THEN "CAP" (MP_TAC o SPECL [`C:real`; `eps:real`; `top:A topology`;
                                    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                                    `x:A`; `U:A->bool`; `Y:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CP"))) THEN
    EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
    STRIP_TAC THEN REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `IMAGE (psi:A->B) Y` THEN CONJ_TAC THENL
     [USE_THEN "CP" MATCH_MP_TAC THEN EXISTS_TAC `psi':B->A` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    MP_TAC(ISPECL [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `U:A->bool`] P2B9S_OPEN_CCOMP_U) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CC"))) THEN
    EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
      SIMP_TAC[rfs_c_component];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "CC" MATCH_MP_TAC THEN EXISTS_TAC `psi':B->A` THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
      SIMP_TAC[rfs_round_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`] APX_ROUND_SECTIONAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < mfd_sectional atlas (g:A->real^3^3) x u1 v1 / q` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `U:A->bool`] P2B9S_OPEN_ROUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RD"))) THEN
    EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `g':B->real^3^3`; `psi:A->B`; `psi':B->A`] THEN
    STRIP_TAC THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "RD" MATCH_MP_TAC THEN EXISTS_TAC `psi':B->A` THEN ASM_SIMP_TAC[]]);;

