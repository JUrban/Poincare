(* ========================================================================= *)
(* Unit pc_p2b_g3e: slices of the global functional (Fubini and the chart    *)
(* pieces of the manifold integral), linearity of the global functional, and *)
(* the time integration by parts for the cutoffs of G3.                      *)
(* ========================================================================= *)

needs "src/pc_p2b_g3d.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Manifold integrals of functions supported in one chart piece; finite      *)
(* sums; continuous functions with compact support.                          *)
(* ========================================================================= *)

let P2BX_MFD_ZERO_SUBSET = prove
 (`!top atlas (g:A->real^N^N) S S'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g (\x. &0) S' (&0) /\
     mfd_lebesgue_measurable (top,atlas) S /\ S SUBSET S'
     ==> mfd_has_integral (top,atlas) g (\x. &0) S (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\x:A. &0`; `S:A->bool`; `S':A->bool`] MFD_INTEGRABLE_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfd_integrable_on] THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\x:A. &0`; `S:A->bool`; `v:real`; `&0`] MFD_HAS_INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

let P2BX_CHART_COMPACT_IMAGE = prove
 (`!(top:A topology) atlas (c:(A->bool)#(A->real^N)) Kc.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
     compact Kc /\ Kc SUBSET IMAGE (SND c) (FST c)
     ==> compact_in top (IMAGE (chart_inv c) Kc) /\
         closed_in top (IMAGE (chart_inv c) Kc) /\
         IMAGE (chart_inv c) Kc SUBSET FST c /\
         IMAGE (SND c) (IMAGE (chart_inv c) Kc) = Kc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                MFDC_CHART_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_in (subtopology top (FST(c:(A->bool)#(A->real^N))))
                  (IMAGE (chart_inv c) Kc)` MP_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\y:real^N. y) Kc` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
       [UNDISCH_TAC `(Kc:real^N->bool) SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[IMAGE_ID]]]);;

(* A function supported in one compact chart piece: its integral over the   *)
(* manifold is the chart integral.                                           *)

let P2BX_MFD_CHART_PIECE = prove
 (`!(top:A topology) atlas (g:A->real^N^N) c Kc f.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ compact Kc /\ Kc SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(x IN IMAGE (chart_inv c) Kc) ==> f x = &0) /\
     mfd_chart_integrand atlas g f c absolutely_integrable_on Kc /\
     mfd_has_integral (top,atlas) g (\x. &0) (topspace top) (&0)
     ==> mfd_has_integral (top,atlas) g f (topspace top)
           (drop(integral Kc (mfd_chart_integrand atlas g f c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `Kc:real^N->bool`] P2BX_CHART_COMPACT_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (chart_inv (c:(A->bool)#(A->real^N))) Kc SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top = IMAGE (chart_inv (c:(A->bool)#(A->real^N))) Kc UNION
                               (topspace top DIFF IMAGE (chart_inv c) Kc)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `c:(A->bool)#(A->real^N)`;
                   `IMAGE (chart_inv (c:(A->bool)#(A->real^N))) Kc`;
                   `drop(integral Kc (mfd_chart_integrand atlas (g:A->real^N^N) f c))`]
                  MFD_HAS_INTEGRAL_CHART) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `\x:A. &0`; `f:A->real`;
                   `topspace top DIFF IMAGE (chart_inv (c:(A->bool)#(A->real^N))) Kc`; `&0`]
                  MFD_HAS_INTEGRAL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN GEN_TAC THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC P2BX_MFD_ZERO_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF] THEN
    MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    SET_TAC[]]);;

(* Finite sums of manifold integrals. *)

let P2BX_MFD_HAS_INTEGRAL_SUM = prove
 (`!top atlas (g:A->real^N^N) (f:num->A->real) v S n.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g (\x. &0) S (&0) /\
     (!j. 1 <= j /\ j <= n ==> mfd_has_integral (top,atlas) g (f j) S (v j))
     ==> mfd_has_integral (top,atlas) g (\x. sum(1..n) (\j. f j x)) S (sum(1..n) v)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN SIMP_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* Continuous functions on an open set with compact support inside it. *)

let P2BX_CONT_SUPPORT_UNIV = prove
 (`!(om:real^M->bool) f k.
     open om /\ (\z. lift(f z)) continuous_on om /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> f z = &0)
     ==> (\z. lift(f z)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN om` THENL
   [MP_TAC(ISPECL [`\z. lift((f:real^M->real) z)`; `om:real^M->bool`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^M. lift(&0)` THEN
  SUBGOAL_THEN `open((:real^M) DIFF k)` MP_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[CONTINUOUS_CONST] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let P2BX_CONT_SUPPORT_ABSINT = prove
 (`!(om:real^M->bool) f k.
     open om /\ (\z. lift(f z)) continuous_on om /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> f z = &0)
     ==> (\z. lift(f z)) absolutely_integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `f:real^M->real`; `k:real^M->bool`] P2BX_CONT_SUPPORT_UNIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^M->bool` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `aa:real^M` (X_CHOOSE_TAC `bb:real^M`)) THEN
  SUBGOAL_THEN `(\x. lift((f:real^M->real) x)) =
                (\x. if x IN interval[aa,bb] then lift(f x) else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:real^M->real) x = &0` (fun th -> REWRITE_TAC[th; LIFT_NUM]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

(* ========================================================================= *)
(* Slices.  A partition-weighted chart term of a continuous function with    *)
(* compact support is the time integral of the manifold integrals of its     *)
(* slices (Fubini); summed over the partition the slices recombine.          *)
(* ========================================================================= *)

let P2BX_SLICE_PIECE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi K a b k c om Ks rho ff j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k /\ &0 < a /\
     (!t x. ~(ff t x = &0) ==> a <= t /\ t <= b) /\
     (\z. lift(p2bw_cfun (c j) ff z)) continuous_on om j /\
     (!t. a <= t /\ t <= b
          ==> mfd_has_integral (top',atlas') (g'(&1 - t)) (\x. &0) (topspace top') (&0))
     ==> ?v. (!t. a <= t /\ t <= b
                  ==> mfd_has_integral (top',atlas') (g'(&1 - t)) (\x. rho j x * ff t x)
                        (topspace top') (v t)) /\
             ((\y. if y IN interval[lift a,lift b] then lift(v(drop y)) else vec 0) has_integral
              integral (om j) (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z * p2bw_cfun (c j) ff z *
                                        sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)))))
             (:real^1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_BOX_A_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `G = \z:real^(3,1)finite_sum.
                    if z IN (om:num->real^(3,1)finite_sum->bool) j
                    then p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                         p2bw_cfun (c j) (ff:real->B->real) z *
                         sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))
                    else &0` THEN
  (* continuity on the box and support *)
  SUBGOAL_THEN `(\z. lift((G:real^(3,1)finite_sum->real) z)) continuous_on (om:num->real^(3,1)finite_sum->bool) j`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                         p2bw_cfun (c j) (ff:real->B->real) z *
                         sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])
                    ==> (G:real^(3,1)finite_sum->real) z = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[p2bw_cfun; REAL_ENTIRE] THEN
    ASM_CASES_TAC `(rho:num->B->real) j (chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                     (fstcart(z:real^(3,1)finite_sum))) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(ff:real->B->real) (drop(sndcart(z:real^(3,1)finite_sum)))
                     (chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart z)) = &0` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                                (fstcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) j`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                               `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `ff:real->B->real`)) (concl th) &&
        can (find_term ((=) `b:real`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
    REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN `SND((c:num->(B->bool)#(B->real^3)) j)
                    (chart_inv (c j) (fstcart(z:real^(3,1)finite_sum))) = fstcart z`
    (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((G:real^(3,1)finite_sum->real) z)) continuous_on (:real^(3,1)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_CONT_SUPPORT_UNIV THEN
    MAP_EVERY EXISTS_TAC [`(om:num->real^(3,1)finite_sum->bool) j`;
                          `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((G:real^(3,1)finite_sum->real) z)) absolutely_integrable_on (:real^(3,1)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_CONT_SUPPORT_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`(om:num->real^(3,1)finite_sum->bool) j`;
                          `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral ((om:num->real^(3,1)finite_sum->bool) j)
      (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                p2bw_cfun (c j) (ff:real->B->real) z *
                sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z)))) =
    integral (:real^(3,1)finite_sum) (\z. lift((G:real^(3,1)finite_sum->real) z))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN
    EXPAND_TAC "G" THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  (* the slices *)
  EXISTS_TAC `\t. drop(integral ((Ks:num->real^3->bool) j)
                   (mfd_chart_integrand atlas' ((g':real->B->real^3^3)(&1 - t))
                      (\x. (rho:num->B->real) j x * (ff:real->B->real) t x)
                      ((c:num->(B->bool)#(B->real^3)) j)))` THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t <= b /\ y IN (Ks:num->real^3->bool) j
          ==> mfd_chart_integrand atlas' ((g':real->B->real^3^3)(&1 - t))
                (\x. (rho:num->B->real) j x * (ff:real->B->real) t x)
                ((c:num->(B->bool)#(B->real^3)) j) y =
              lift((G:real^(3,1)finite_sum->real) (pastecart y (lift t)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
    SUBGOAL_THEN `pastecart (y:real^3) (lift t) IN (om:num->real^(3,1)finite_sum->bool) j`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b] SUBSET
                   (om:num->real^(3,1)finite_sum->bool) j` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_chart_integrand; mfd_density; p2bw_cfun; p2bw_cmet;
                FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (\x. lift((G:real^(3,1)finite_sum->real) (pastecart x (lift t))))
        absolutely_integrable_on (:real^3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BX_CONT_SUPPORT_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(Ks:num->real^3->bool) j`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. lift((G:real^(3,1)finite_sum->real) (pastecart x (lift t)))) =
                    (\z. lift(G z)) o (\x:real^3. pastecart x (lift t))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t <= b
        ==> mfd_chart_integrand atlas' ((g':real->B->real^3^3)(&1 - t))
              (\x. (rho:num->B->real) j x * (ff:real->B->real) t x)
              ((c:num->(B->bool)#(B->real^3)) j) absolutely_integrable_on (Ks:num->real^3->bool) j /\
            integral (Ks j) (mfd_chart_integrand atlas' (g'(&1 - t))
              (\x. rho j x * ff t x) (c j)) =
            integral (:real^3) (\x. lift((G:real^(3,1)finite_sum->real) (pastecart x (lift t))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. lift((G:real^(3,1)finite_sum->real) (pastecart x (lift t)))) =
      (\y. if y IN (Ks:num->real^3->bool) j
           then mfd_chart_integrand atlas' ((g':real->B->real^3^3)(&1 - t))
                  (\x. (rho:num->B->real) j x * (ff:real->B->real) t x)
                  ((c:num->(B->bool)#(B->real^3)) j) y
           else vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^3` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; ETA_AX] THEN
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "absolutely_integrable_on")) (concl th) &&
      can (find_term ((=) `(:real^3)`)) (concl th))) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^3` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_MFD_CHART_PIECE THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(rho:num->B->real) j x = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\z. lift((G:real^(3,1)finite_sum->real) z)` FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^1` THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `a <= drop y /\ drop y <= b` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^1) IN interval[lift a,lift b]` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "integral")) (concl th) &&
      can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP];
    REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `integral (:real^3) (\x:real^3. vec 0:real^1)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      REWRITE_TAC[INTEGRAL_0]]]);;

(* The slice formula. *)

let P2BX_SLICE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi K a b k c om Ks rho ff.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ &0 < a /\
     (!t x. ~(ff t x = &0) ==> a <= t /\ t <= b) /\
     (!t x. x IN topspace top' /\ ~(ff t x = &0) ==> x IN K) /\
     (!j. j IN 1..k ==> (\z. lift(p2bw_cfun (c j) ff z)) continuous_on om j) /\
     (!t. a <= t /\ t <= b
          ==> mfd_has_integral (top',atlas') (g'(&1 - t)) (\x. &0) (topspace top') (&0))
     ==> (!t. a <= t /\ t <= b
              ==> mfd_integrable_on (top',atlas') (g'(&1 - t)) (ff t) (topspace top')) /\
         ((\y. lift(mfd_integral (top',atlas') (g'(&1 - drop y)) (topspace top') (ff (drop y))))
          has_integral
          lift(sum(1..k) (\j. drop(integral (om j)
                 (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z * p2bw_cfun (c j) ff z *
                           sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))))))))
         (interval[lift a,lift b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?v. (!t. a <= t /\ t <= b
                     ==> mfd_has_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                           (\x. (rho:num->B->real) j x * (ff:real->B->real) t x)
                           (topspace top') (v t)) /\
                ((\y. if y IN interval[lift a,lift b] then lift(v(drop y)) else vec 0) has_integral
                 integral ((om:num->real^(3,1)finite_sum->bool) j)
                   (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. rho j) z *
                             p2bw_cfun (c j) ff z *
                             sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))))) (:real^1)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX_SLICE_PIECE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `K:B->bool`; `k:num`; `Ks:num->real^3->bool`] THEN
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real->real` ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t <= b
        ==> mfd_has_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) ((ff:real->B->real) t)
              (topspace top') (sum(1..k) (\j. (v:num->real->real) j t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3)(&1 - t)`;
                   `\j x. (rho:num->B->real) j x * (ff:real->B->real) t x`;
                   `\j. (v:num->real->real) j t`; `topspace top':B->bool`; `k:num`]
                  P2BX_MFD_HAS_INTEGRAL_SUM) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `v:num->real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN REWRITE_TAC[SUM_RMUL] THEN
    ASM_CASES_TAC `(ff:real->B->real) t x = &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    SUBGOAL_THEN `sum(1..k) (\j. (rho:num->B->real) j x) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks (rho:num->B->real)` THEN
    REWRITE_TAC[p2bx_pdata] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `x:B`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K:B->bool`)) (concl th) &&
      can (find_term ((=) `ff:real->B->real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_integrable_on] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    EXISTS_TAC `sum(1..k) (\j. (v:num->real->real) j t)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  MP_TAC(INST
   [`\j. integral ((om:num->real^(3,1)finite_sum->bool) j)
           (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                     p2bw_cfun (c j) (ff:real->B->real) z *
                     sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))))`,
    `i:num->real^1`]
   (ISPECL
   [`\j y. if y IN interval[lift a,lift b] then lift((v:num->real->real) j (drop y)) else vec 0`;
    `(:real^1)`; `1..k`]
   (INST_TYPE [`:num`,`:A`] HAS_INTEGRAL_VSUM))) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN MK_COMB_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^1` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VSUM_0; P2BX_VSUM_LIFT; LIFT_EQ] THEN
    SUBGOAL_THEN `a <= drop y /\ drop y <= b` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^1) IN interval[lift a,lift b]` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - drop y))` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(g':real->B->real^3^3)(&1 - drop y)`; `(ff:real->B->real) (drop y)`;
                          `topspace top':B->bool`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL; mfd_integrable_on] THEN
    EXISTS_TAC `sum(1..k) (\j. (v:num->real->real) j (drop y))` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[GSYM P2BX_VSUM_LIFT; LIFT_DROP] THEN
    REWRITE_TAC[P2BX_SUM_DROP; LIFT_DROP]]);;

(* ========================================================================= *)
(* Linearity of the weak integrand and of the global functional in the       *)
(* admissible function; integrability of a chart term.                       *)
(* ========================================================================= *)

let P2BX_DER_LINCOMB = prove
 (`!(f:real^M->real) h (M:real) x v.
     (\y. lift(f y)) differentiable at x /\ (\y. lift(h y)) differentiable at x
     ==> (\y. lift(M * f y - h y)) differentiable at x /\
         drop(frechet_derivative (\y. lift(M * f y - h y)) (at x) v) =
         M * drop(frechet_derivative (\y. lift(f y)) (at x) v) -
         drop(frechet_derivative (\y. lift(h y)) (at x) v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS])) THEN
  SUBGOAL_THEN `((\y. lift(M * (f:real^M->real) y - h y)) has_derivative
                 (\u. M % frechet_derivative (\y. lift(f y)) (at x) u -
                      frechet_derivative (\y. lift(h y)) (at x) u)) (at x)` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_SUB; DROP_CMUL]);;

let P2BX_BIL_LINEAR = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u f h (M:real) z.
     (\w. lift(f w)) differentiable at z /\ (\w. lift(h w)) differentiable at z
     ==> p2bw_bil A u (\w. M * f w - h w) z =
         M * p2bw_bil A u f z - p2bw_bil A u h z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_xder j (\w. M * (f:real^(N,1)finite_sum->real) w - h w) z =
                    M * wan_xder j f z - wan_xder j h z` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_xder] THEN
    MP_TAC(ISPECL [`f:real^(N,1)finite_sum->real`; `h:real^(N,1)finite_sum->real`; `M:real`;
                   `z:real^(N,1)finite_sum`; `pastecart (basis j:real^N) (vec 0:real^1)`]
                  P2BX_DER_LINCOMB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_bil] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2BX_WINT_LINEAR = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) uu f h (M:real) z.
     (\w. lift(f w)) differentiable at z /\ (\w. lift(h w)) differentiable at z
     ==> p2bx_wint atlas' g' c uu (\w. M * f w - h w) z =
         M * p2bx_wint atlas' g' c uu f z - p2bx_wint atlas' g' c uu h z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_wint] THEN
  ASM_SIMP_TAC[P2BX_BIL_LINEAR] THEN REAL_ARITH_TAC);;

let P2BX_CFUN_LINCOMB = prove
 (`!(c:(B->bool)#(B->real^3)) (f:real->B->real) (h:real->B->real) (M:real).
     p2bw_cfun c (\t x. M * f t x - h t x) = (\z. M * p2bw_cfun c f z - p2bw_cfun c h z)`,
  REWRITE_TAC[FUN_EQ_THM; p2bw_cfun]);;

(* A partition-weighted chart term is absolutely integrable. *)

let P2BX_TERM_ABSINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho tf j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> a <= t /\ t <= b) /\
     wan_loclip (om j) (p2bw_cfun (c j) tf) /\ j IN 1..k
     ==> (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                   p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) tf) z))
         absolutely_integrable_on (om j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real)`] P2BX_WINT_LEBM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BX_ABSINT_SUPPORT THEN
  EXISTS_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `fstcart(z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j` THENL
   [ALL_TAC;
    SUBGOAL_THEN `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    REWRITE_TAC[p2bw_cfun] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                                (fstcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) j`)) (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(REAL_RING `y = &0 ==> x * y = &0`) THEN
  MATCH_MP_TAC P2BX_WINT_ZERO THEN
  EXISTS_TAC `{w:real^(3,1)finite_sum | sndcart w IN (:real^1) DIFF interval[lift a,lift b]}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_SNDCART];
      REWRITE_TAC[GSYM closed; CLOSED_INTERVAL]];
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
    ASM_REWRITE_TAC[P2BX_IN_PCROSS];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN DISCH_TAC THEN
    REWRITE_TAC[p2bw_cfun] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop(sndcart(w:real^(3,1)finite_sum))`;
                                  `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(w:real^(3,1)finite_sum))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `tf:real->B->real`)) (concl th) &&
        can (find_term ((=) `b:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* Linearity of the global functional. *)

let P2BX_GFUN_LINEAR = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho tf1 tf2 M.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf1 t x = &0) ==> a <= t /\ t <= b) /\
     (!t x. ~(tf2 t x = &0) ==> a <= t /\ t <= b) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf1) /\
                        wan_loclip (om j) (p2bw_cfun (c j) tf2))
     ==> sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                               (p2bw_cfun (c j) (\t x. M * tf1 t x - tf2 t x)) z)))) =
         M * sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) tf1) z)))) -
         sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) tf2) z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(j:num) IN 1..k` ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip ((om:num->real^(3,1)finite_sum->bool) j)
                  (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf1:real->B->real)) /\
                wan_loclip (om j) (p2bw_cfun (c j) (tf2:real->B->real))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `tf1:real->B->real`; `j:num`]
                P2BX_TERM_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `tf2:real->B->real`; `j:num`]
                P2BX_TERM_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM DROP_CMUL; GSYM DROP_SUB] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; GSYM INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
               INTEGRABLE_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{z | z IN (om:num->real^(3,1)finite_sum->bool) j /\
                   ~((\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                                 (tf1:real->B->real) y)) differentiable at z)} UNION
              {z | z IN om j /\
                   ~((\y. lift(p2bw_cfun (c j) (tf2:real->B->real) y)) differentiable at z)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[P2BX_CFUN_LINCOMB] THEN
  SUBGOAL_THEN `(\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf1:real->B->real) y))
                differentiable at z /\
                (\y. lift(p2bw_cfun (c j) (tf2:real->B->real) y)) differentiable at z`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BX_WINT_LINEAR] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ; ETA_AX] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The spatial cutoffs h_R = chi(linf / R - 1) of G3 (p2bx_hcut), the        *)
(* lower integrand of the time integration by parts (p2bx_lowf), and the     *)
(* calculus of the cutoffs in charts.                                        *)
(* ========================================================================= *)

let p2bx_hcut = new_definition
 `p2bx_hcut (R:real) (linf:real->B->real) (t:real) (x:B) = p2bx_chi (linf t x / R - &1)`;;

let p2bx_lowf = new_definition
 `p2bx_lowf (eta:real->real) (deta:real->real) (a:real) (R:real) (linf:real->B->real)
            (t:real) (x:B) =
    --(deta t * p2bx_uf linf t x * p2bx_hcut R linf t x) -
    &4 / a * eta t * p2bx_uf linf t x * --(p2bx_dchi(linf t x / R - &1))`;;

let P2BX_CHI_LIP = prove
 (`!s s'. abs(p2bx_chi s - p2bx_chi s') <= &3 / &2 * abs(s - s')`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_SUB] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p2bx_chi`; `p2bx_dchi`; `s:real`; `s':real`] REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REWRITE_TAC[P2BX_CHI_DERIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  MP_TAC(SPEC `x:real` P2BX_CHI_BOUNDS) THEN REAL_ARITH_TAC);;

let P2BX_DCHI_CLAMP = prove
 (`!s. p2bx_dchi s = &6 * (max (&0) (min s (&1))) pow 2 - &6 * max (&0) (min s (&1))`,
  GEN_TAC THEN REWRITE_TAC[p2bx_dchi] THEN
  ASM_CASES_TAC `s <= &0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `max (&0) (min s (&1)) = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= s` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `max (&0) (min s (&1)) = &1` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN `max (&0) (min s (&1)) = s` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let P2BX_DCHI_CONT = prove
 (`!s. p2bx_dchi real_continuous atreal s`,
  GEN_TAC THEN
  SUBGOAL_THEN `p2bx_dchi = \s. &6 * (max (&0) (min s (&1))) pow 2 - &6 * max (&0) (min s (&1))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P2BX_DCHI_CLAMP]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_POW; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MIN THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID]);;

(* Composition of a continuous real function with a continuous function. *)

let P2BX_REAL_COMPOSE_CONT = prove
 (`!(g:real->real) (f:real^M->real) S.
     (!s. g real_continuous atreal s) /\ (\z. lift(f z)) continuous_on S
     ==> (\z. lift(g(f z))) continuous_on S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((g:real->real)((f:real^M->real) z))) = (lift o g o drop) o (\z. lift(f z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN
  REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN ASM_REWRITE_TAC[]);;

(* The cutoffs in a chart: Lipschitz, and their derivatives. *)

let P2BX_HCUT_LOCLIP = prove
 (`!(om:real^(3,1)finite_sum->bool) (c:(B->bool)#(B->real^3)) linf R.
     wan_loclip om (p2bw_cfun c linf) /\ &0 < R
     ==> wan_loclip om (p2bw_cfun c (p2bx_hcut R linf))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_loclip] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^(3,1)finite_sum->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^(3,1)finite_sum->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN EXISTS_TAC `&3 / &2 * abs(inv R) * L` THEN
  MAP_EVERY X_GEN_TAC [`x:real^(3,1)finite_sum`; `y:real^(3,1)finite_sum`] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bw_cfun; p2bx_hcut] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 / &2 * abs(((linf:real->B->real) (drop(sndcart(x:real^(3,1)finite_sum)))
                                (chart_inv (c:(B->bool)#(B->real^3)) (fstcart x)) / R - &1) -
                            (linf (drop(sndcart(y:real^(3,1)finite_sum))) (chart_inv c (fstcart y)) / R - &1))` THEN
  REWRITE_TAC[P2BX_CHI_LIP] THEN
  SUBGOAL_THEN `!u v. abs(u / R - &1 - (v / R - &1)) = abs(inv R) * abs(u - v)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_ABS_MUL; real_div] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^(3,1)finite_sum`; `y:real^(3,1)finite_sum`]) THEN
  ASM_REWRITE_TAC[p2bw_cfun]);;

let P2BX_HCUT_DERIV = prove
 (`!(c:(B->bool)#(B->real^3)) linf R z.
     (\w. lift(p2bw_cfun c linf w)) differentiable at z
     ==> (\w. lift(p2bw_cfun c (p2bx_hcut R linf) w)) differentiable at z /\
         !v. drop(frechet_derivative (\w. lift(p2bw_cfun c (p2bx_hcut R linf) w)) (at z) v) =
             p2bx_dchi(p2bw_cfun c linf z / R - &1) / R *
             drop(frechet_derivative (\w. lift(p2bw_cfun c linf w)) (at z) v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  ABBREV_TAC `l' = frechet_derivative (\w. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) w)) (at z)` THEN
  SUBGOAL_THEN
   `((\w. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) w / R - &1)) has_derivative
     (\v. inv R % (l':real^(3,1)finite_sum->real^1) v)) (at z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) w / R - &1)) =
                  (\w. inv R % lift(p2bw_cfun c linf w) - lift(&1))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\v. inv R % (l':real^(3,1)finite_sum->real^1) v) = (\v. inv R % l' v - vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN EXPAND_TAC "l'" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_hcut R linf) w)) has_derivative
     (\v. (p2bx_dchi(p2bw_cfun c (linf:real->B->real) z / R - &1) / R) %
          (l':real^(3,1)finite_sum->real^1) v)) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_hcut R linf) w)) =
      (lift o p2bx_chi o drop) o (\w. lift(p2bw_cfun c (linf:real->B->real) w / R - &1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; p2bw_cfun; p2bx_hcut]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. (p2bx_dchi(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z / R - &1) / R) %
           (l':real^(3,1)finite_sum->real^1) v) =
      (\x. p2bx_dchi(p2bw_cfun c linf z / R - &1) % x) o (\v. inv R % l' v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_MUL_ASSOC; real_div]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; P2BX_CHI_DERIV];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_CMUL]);;

(* ========================================================================= *)
(* Time cutoffs eta(t) read on space-time, time independence of the chart    *)
(* readings of a function on the limit, and the smooth test rho_j eta        *)
(* sqrt(det G) of the time integration by parts.                             *)
(* ========================================================================= *)

let P2BX_TDER_TIMEINDEP = prove
 (`!(c:(B->bool)#(B->real^3)) (r:B->real) z.
     (\w. lift(p2bw_cfun c (\t:real. r) w)) differentiable at z
     ==> wan_tder (p2bw_cfun c (\t:real. r)) z = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p2bw_cfun (c:(B->bool)#(B->real^3)) (\t:real. r)`; `z:real^(3,1)finite_sum`;
                 `pastecart (vec 0:real^3) (lift(&1))`] P2BX_DIRDERIV) THEN
  ASM_REWRITE_TAC[GSYM wan_tder] THEN
  SUBGOAL_THEN `(\h. p2bw_cfun (c:(B->bool)#(B->real^3)) (\t:real. r)
                       (z + h % pastecart (vec 0:real^3) (lift(&1)))) =
                (\h. p2bw_cfun c (\t:real. r) z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun; FSTCART_ADD; FSTCART_CMUL; FSTCART_PASTECART;
                VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\h:real. p2bw_cfun (c:(B->bool)#(B->real^3)) (\t:real. r) z`; `&0`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]);;

let P2BX_ETA_FACTS = prove
 (`!(eta:real->real) deta z.
     (!t. (eta has_real_derivative deta t) (atreal t))
     ==> (\w. lift(eta(drop(sndcart w)))) differentiable at (z:real^(3,1)finite_sum) /\
         wan_tder (\w. eta(drop(sndcart w))) z = deta(drop(sndcart z)) /\
         (!i. wan_xder i (\w. eta(drop(sndcart w))) z = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\w:real^(3,1)finite_sum. lift((eta:real->real)(drop(sndcart w)))) has_derivative
                 (\v. (deta:real->real)(drop(sndcart(z:real^(3,1)finite_sum))) % sndcart v)) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w:real^(3,1)finite_sum. lift((eta:real->real)(drop(sndcart w)))) =
                  (lift o eta o drop) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\v:real^(3,1)finite_sum. (deta:real->real)(drop(sndcart(z:real^(3,1)finite_sum))) % sndcart v) =
                  (\x. deta(drop(sndcart z)) % x) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
      SUBGOAL_THEN `sndcart(z:real^(3,1)finite_sum) = lift(drop(sndcart z))`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
       [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
      REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^(3,1)finite_sum. lift((eta:real->real)(drop(sndcart w)))) differentiable
                at (z:real^(3,1)finite_sum)`
  ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\v:real^(3,1)finite_sum. (deta:real->real)(drop(sndcart(z:real^(3,1)finite_sum))) %
                                          sndcart v` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_tder; wan_xder] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[SNDCART_PASTECART; DROP_CMUL; LIFT_DROP; REAL_MUL_RID; DROP_VEC; REAL_MUL_RZERO]);;

let P2BX_SMOOTH_LIFT_MUL = prove
 (`!(s:real^M->bool) f g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2BX_ETA_SMOOTH = prove
 (`!(eta:real->real).
     smooth_map_on (:real^1) (\s. lift(eta(drop s)))
     ==> smooth_map_on (:real^(3,1)finite_sum) (\w. lift(eta(drop(sndcart w))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w:real^(3,1)finite_sum. lift((eta:real->real)(drop(sndcart w)))) =
                (\s. lift(eta(drop s))) o (sndcart o (\w:real^(3,1)finite_sum. w))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

(* The smooth test of the time integration by parts and its time derivative. *)

let P2BX_CUT_TEST = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi K a b k c om Ks rho eta deta j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b)
     ==> wan_test (om j)
           (\z. if z IN om j
                then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
                     sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
                else &0) /\
         (!z. z IN om j
              ==> wan_tder (\z. if z IN om j
                                then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
                                     sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
                                else &0) z =
                  p2bw_cfun (c j) (\t:real. rho j) z *
                  (deta(drop(sndcart z)) * sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) +
                   eta(drop(sndcart z)) * (p2bw_cscal atlas' (c j) (&1) g' z *
                                            sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded((om:num->real^(3,1)finite_sum->bool) j) /\
                om j SUBSET {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j)) /\
                                 &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox ((c:num->(B->bool)#(B->real^3)) j) ((om:num->real^(3,1)finite_sum->bool) j)` THEN
    REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `(om:num->real^(3,1)finite_sum->bool) j` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(om:num->real^(3,1)finite_sum->bool) j`;
                 `p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1) (g':real->B->real^3^3)`]
                P2BW_SQRTDET_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`] P2BX_MSMOOTH_CFUN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `eta:real->real` P2BX_ETA_SMOOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `P = \z. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                      (eta:real->real)(drop(sndcart z)) *
                      sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))` THEN
  SUBGOAL_THEN `!z. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                    (eta:real->real)(drop(sndcart z)) *
                    sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z)) =
                    (P:real^(3,1)finite_sum->real) z`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((om:num->real^(3,1)finite_sum->bool) j)
                  (\z. lift((P:real^(3,1)finite_sum->real) z))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC P2BX_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN
                    IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])
                    ==> (if z IN (om:num->real^(3,1)finite_sum->bool) j
                         then (P:real^(3,1)finite_sum->real) z else &0) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[REAL_ENTIRE; p2bw_cfun] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                  P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(rho:num->B->real) j (chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                     (fstcart(z:real^(3,1)finite_sum))) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(eta:real->real)(drop(sndcart(z:real^(3,1)finite_sum))) = &0` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                                (fstcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) j`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `drop(sndcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `eta:real->real`)) (concl th) &&
        can (find_term ((=) `b:real`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
    REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `SND((c:num->(B->bool)#(B->real^3)) j)
                   (chart_inv (c j) (fstcart(z:real^(3,1)finite_sum))) IN (Ks:num->real^3->bool) j` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^(3,1)finite_sum)
                  (\z. lift(if z IN (om:num->real^(3,1)finite_sum->bool) j
                            then (P:real^(3,1)finite_sum->real) z else &0))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN
    ASM_CASES_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THENL
     [EXISTS_TAC `(om:num->real^(3,1)finite_sum->bool) j` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\z. lift((P:real^(3,1)finite_sum->real) z)` THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `(:real^(3,1)finite_sum) DIFF (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\z:real^(3,1)finite_sum. lift(&0)` THEN
        REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
        X_GEN_TAC `w:real^(3,1)finite_sum` THEN DISCH_TAC THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[wan_test] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j)) /\ &0 < drop(sndcart z)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j)) /\
                      &0 < drop(sndcart z)}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `(c:num->(B->bool)#(B->real^3)) j`; `z:real^(3,1)finite_sum`]
                P2BX_BOX_RHO_TDER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eta:real->real`; `deta:real->real`; `z:real^(3,1)finite_sum`] P2BX_ETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\w. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) w))
                differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC P2BX_OPEN_CHART_CYL THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(c:num->(B->bool)#(B->real^3)) j`; `(rho:num->B->real) j`; `z:real^(3,1)finite_sum`]
                P2BX_TDER_TIMEINDEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z. if z IN (om:num->real^(3,1)finite_sum->bool) j
                      then (P:real^(3,1)finite_sum->real) z else &0`;
                 `P:real^(3,1)finite_sum->real`; `(om:num->real^(3,1)finite_sum->bool) j`;
                 `z:real^(3,1)finite_sum`] P2BX_DERIV_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(om:num->real^(3,1)finite_sum->bool) j` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[wan_tder; CONJUNCT2 th]) THEN
  EXPAND_TAC "P" THEN
  MP_TAC(ISPECL [`p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j)`;
                 `\w. (eta:real->real)(drop(sndcart w)) *
                      sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                                 (g':real->B->real^3^3) w))`;
                 `z:real^(3,1)finite_sum`; `pastecart (vec 0:real^3) (lift(&1))`] P2BW_DER_MUL) THEN
  MP_TAC(ISPECL [`\w:real^(3,1)finite_sum. (eta:real->real)(drop(sndcart w))`;
                 `\w. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                                 (g':real->B->real^3^3) w))`;
                 `z:real^(3,1)finite_sum`; `pastecart (vec 0:real^3) (lift(&1))`] P2BW_DER_MUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wan_tder]) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The pointwise lower bound behind the time integration by parts for the    *)
(* cutoff eta(t) h_R (MT Section 2.6: the gradient term has a sign, l_tau >= *)
(* -2 l / tau where the cutoff varies).                                      *)
(* ========================================================================= *)

let P2BX_CUT_ALG = prove
 (`!rho eta deta U D hh dc lt BLL R0 Ut R a l t BUF.
     &0 <= rho /\ &0 <= eta /\ &0 <= U /\ &0 <= D /\ &0 <= BLL /\ dc <= &0 /\
     &0 < R /\ &0 < a /\ &0 < t /\
     (~(eta = &0) ==> a <= t) /\
     (~(dc = &0) ==> R <= l /\ l <= &2 * R) /\
     --(&2 * l / t) <= lt /\
     BUF = eta * (dc / R) * --U * BLL
     ==> rho * (--(deta * U * hh) - &4 / a * eta * U * --dc) * D <=
         rho * ((eta * hh) * (Ut + R0 * U) * D + BUF) -
         (Ut * hh + U * (dc / R * lt)) * (rho * eta * D) -
         (U * hh) * (rho * (deta * D + eta * (R0 * D)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN
   `rho * ((eta * hh) * (Ut + R0 * U) * D + BUF) -
    (Ut * hh + U * (dc / R * lt)) * (rho * eta * D) -
    (U * hh) * (rho * (deta * D + eta * (R0 * D))) -
    rho * (--(deta * U * hh) - &4 / a * eta * U * --dc) * D =
    (rho * eta * U * --dc) / R * (BLL + D * (lt + &4 * R / a))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < R` THEN UNDISCH_TAC `&0 < a` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `eta = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_LE_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `dc = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= t /\ R <= l /\ l <= &2 * R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * l / t <= &4 * R / a` ASSUME_TAC THENL
   [SUBGOAL_THEN `l / t <= &2 * R / a` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * R) / t` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
        REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC]);;

(* Sign facts for the metric weights. *)

let P2BX_POSDEF_FACTS = prove
 (`!(G:real^N^N).
     transp G = G /\ (!v. ~(v = vec 0) ==> &0 < v dot (G ** v))
     ==> &0 < det G /\ &0 <= sqrt(det G) /\ (!v. &0 <= v dot (matrix_inv G ** v))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `positive_definite(G:real^N^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[positive_definite; symmetric_matrix]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(G:real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `positive_semidefinite(matrix_inv(G:real^N^N))` MP_TAC THENL
   [REWRITE_TAC[POSITIVE_SEMIDEFINITE_INV] THEN
    UNDISCH_TAC `positive_definite(G:real^N^N)` THEN
    SIMP_TAC[POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE];
    SIMP_TAC[positive_semidefinite]]);;

let P2BX_BIL_SELF_NONNEG = prove
 (`!(G:real^(N,1)finite_sum->real^N^N) f z.
     transp(G z) = G z /\ (!v. ~(v = vec 0) ==> &0 < v dot (G z ** v))
     ==> &0 <= p2bw_bil (\z. sqrt(det(G z)) %% matrix_inv(G z)) f f z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(G:real^(N,1)finite_sum->real^N^N) z` P2BX_POSDEF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX_BIL_DOT; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]);;

let P2BX_BIL_SCALE = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u l ff U K z.
     (!i. wan_xder i u z = --U * wan_xder i l z) /\
     (!j. wan_xder j ff z = K * wan_xder j l z)
     ==> p2bw_bil A u ff z = K * --U * p2bw_bil A l l z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_bil] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* Derivatives of U and of the cutoff eta(t) h_R in a chart. *)

let P2BX_UF_DERIVS = prove
 (`!(c:(B->bool)#(B->real^3)) linf z.
     &0 < drop(sndcart z) /\ (\w. lift(p2bw_cfun c linf w)) differentiable at z
     ==> (\w. lift(p2bw_cfun c (p2bx_uf linf) w)) differentiable at z /\
         (!i. wan_xder i (p2bw_cfun c (p2bx_uf linf)) z =
              --(p2bw_cfun c (p2bx_uf linf) z) * wan_xder i (p2bw_cfun c linf) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`; `z:real^(3,1)finite_sum`]
                P2BW_UOF_DERIV) THEN
  ASM_REWRITE_TAC[P2BX_UOF_UF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[wan_xder] THEN
  REWRITE_TAC[SNDCART_PASTECART; DROP_VEC; REAL_MUL_RZERO; REAL_ADD_RID]);;

let P2BX_CUTF_DERIVS = prove
 (`!(c:(B->bool)#(B->real^3)) linf R (eta:real->real) deta z.
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ &0 < drop(sndcart z) /\
     (\w. lift(p2bw_cfun c linf w)) differentiable at z
     ==> (\w. lift(p2bw_cfun c (\t x. eta t * p2bx_hcut R linf t x) w)) differentiable at z /\
         (!j. wan_xder j (p2bw_cfun c (\t x. eta t * p2bx_hcut R linf t x)) z =
              (eta(drop(sndcart z)) * (p2bx_dchi(p2bw_cfun c linf z / R - &1) / R)) *
              wan_xder j (p2bw_cfun c linf) z) /\
         wan_tder (\w. p2bw_cfun c (p2bx_uf linf) w * p2bw_cfun c (p2bx_hcut R linf) w) z =
         wan_tder (p2bw_cfun c (p2bx_uf linf)) z * p2bw_cfun c (p2bx_hcut R linf) z +
         p2bw_cfun c (p2bx_uf linf) z *
         (p2bx_dchi(p2bw_cfun c linf z / R - &1) / R * wan_tder (p2bw_cfun c linf) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `linf:real->B->real`; `R:real`; `z:real^(3,1)finite_sum`]
                P2BX_HCUT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eta:real->real`; `deta:real->real`; `z:real^(3,1)finite_sum`] P2BX_ETA_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_cfun (c:(B->bool)#(B->real^3)) (\t x. (eta:real->real) t * p2bx_hcut R linf t x) =
                (\w. eta(drop(sndcart w)) * p2bw_cfun c (p2bx_hcut R linf) w)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun]; ALL_TAC] THEN
  REWRITE_TAC[wan_xder; wan_tder] THEN
  MP_TAC(ISPECL [`\w:real^(3,1)finite_sum. (eta:real->real)(drop(sndcart w))`;
                 `p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_hcut R linf)`;
                 `z:real^(3,1)finite_sum`] P2BW_DER_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wan_xder; wan_tder]) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `linf:real->B->real`; `z:real^(3,1)finite_sum`]
                P2BX_UF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_uf linf)`;
                 `p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_hcut R linf)`;
                 `z:real^(3,1)finite_sum`; `pastecart (vec 0:real^3) (lift(&1))`] P2BW_DER_MUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The pointwise lower bound at a differentiability point of linf. *)

let P2BX_CUT_POINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho eta deta R j z.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\ P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k /\ &0 < a /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. &0 <= eta t) /\
     z IN om j /\ (\w. lift(p2bw_cfun (c j) linf w)) differentiable at z
     ==> p2bw_cfun (c j) (\t:real. rho j) z * p2bw_cfun (c j) (p2bx_lowf eta deta a R linf) z *
         sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) <=
         p2bw_cfun (c j) (\t:real. rho j) z *
         p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                   (p2bw_cfun (c j) (\t x. eta t * p2bx_hcut R linf t x)) z -
         wan_tder (\w. p2bw_cfun (c j) (p2bx_uf linf) w * p2bw_cfun (c j) (p2bx_hcut R linf) w) z *
         (if z IN om j
          then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
               sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
          else &0) -
         (p2bw_cfun (c j) (p2bx_uf linf) z * p2bw_cfun (c j) (p2bx_hcut R linf) z) *
         wan_tder (\z. if z IN om j
                       then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
                            sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
                       else &0) z`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j)) /\ &0 < drop(sndcart z)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
    UNDISCH_TAC `p2bg_cbox ((c:num->(B->bool)#(B->real^3)) j) ((om:num->real^(3,1)finite_sum->bool) j)` THEN
    REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `(om:num->real^(3,1)finite_sum->bool) j` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`]
                P2BX_BOX_LIMIT_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    C MP (ASSUME `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j`) o
    SPEC `z:real^(3,1)finite_sum` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "transp")) (concl th))) THEN
  MP_TAC(ISPEC `p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1) (g':real->B->real^3^3) z`
                P2BX_POSDEF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `eta:real->real`; `deta:real->real`;
                 `j:num`] P2BX_CUT_TEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^(3,1)finite_sum` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(c:num->(B->bool)#(B->real^3)) j`; `linf:real->B->real`; `z:real^(3,1)finite_sum`]
                P2BX_UF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(c:num->(B->bool)#(B->real^3)) j`; `linf:real->B->real`; `R:real`;
                 `eta:real->real`; `deta:real->real`; `z:real^(3,1)finite_sum`] P2BX_CUTF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                                  (g':real->B->real^3^3) z)) %%
                      matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf linf)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                    (\t x. (eta:real->real) t * p2bx_hcut R (linf:real->B->real) t x)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf linf) z`;
                 `(eta:real->real)(drop(sndcart(z:real^(3,1)finite_sum))) *
                  (p2bx_dchi(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R - &1) / R)`;
                 `z:real^(3,1)finite_sum`] P2BX_BIL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1) (g':real->B->real^3^3)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real)`;
                 `z:real^(3,1)finite_sum`] P2BX_BIL_SELF_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `z:real^(3,1)finite_sum`] P2BX_CFUN_TDER_LB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R - &1`
              P2BX_CHI_BOUNDS) THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z`;
    `(eta:real->real)(drop(sndcart(z:real^(3,1)finite_sum)))`;
    `(deta:real->real)(drop(sndcart(z:real^(3,1)finite_sum)))`;
    `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf (linf:real->B->real)) z`;
    `sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1) (g':real->B->real^3^3) z))`;
    `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_hcut R (linf:real->B->real)) z`;
    `p2bx_dchi(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R - &1)`;
    `wan_tder (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real)) z`;
    `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                                (g':real->B->real^3^3) z)) %%
                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
              (p2bw_cfun (c j) (linf:real->B->real)) (p2bw_cfun (c j) linf) z`;
    `p2bw_cscal atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1) (g':real->B->real^3^3) z`;
    `wan_tder (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf (linf:real->B->real))) z`;
    `R:real`; `a:real`;
    `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z`;
    `drop(sndcart(z:real^(3,1)finite_sum))`;
    `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                                (g':real->B->real^3^3) z)) %%
                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
              (p2bw_cfun (c j) (p2bx_uf (linf:real->B->real)))
              (p2bw_cfun (c j) (\t x. (eta:real->real) t * p2bx_hcut R linf t x)) z`]
   P2BX_CUT_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[p2bw_cfun; p2bx_uf; REAL_EXP_POS_LE];
      DISCH_TAC THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `&1 < p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R /\
                    p2bw_cfun (c j) linf z / R < &2` MP_TAC THENL
       [SUBGOAL_THEN `~(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R - &1 <= &0 \/
                       &1 <= p2bw_cfun (c j) linf z / R - &1)` MP_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `~(p2bx_dchi(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (linf:real->B->real) z / R - &1) = &0)` THEN
          ASM_SIMP_TAC[];
          REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' ==> a <= b ==> a' <= b'`) THEN CONJ_TAC THENL
   [REWRITE_TAC[p2bw_cfun; p2bx_lowf]; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2bx_wint] THEN REWRITE_TAC[p2bw_cfun] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The time integration by parts for the cutoff eta(t) h_R in one partition  *)
(* term: the term is bounded below by the integral of the lower integrand    *)
(* p2bx_lowf.                                                                *)
(* ========================================================================= *)

let P2BX_GUARD_ABSINT = prove
 (`!(om:real^M->bool) f k.
     open om /\ (\z. lift(f z)) continuous_on om /\ compact k /\ k SUBSET om /\
     (!z. z IN om /\ ~(z IN k) ==> f z = &0)
     ==> (\z. lift(f z)) absolutely_integrable_on om`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^M->bool`; `\z:real^M. if z IN om then (f:real^M->real) z else &0`;
                 `k:real^M->bool`] P2BX_CONT_SUPPORT_ABSINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\z. lift((f:real^M->real) z)` THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
  EXISTS_TAC `\z:real^M. lift(if z IN om then (f:real^M->real) z else &0)` THEN
  CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^M)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN]);;

(* Continuity of the chart readings entering the lower integrand. *)

let P2BX_CFUN_ETA_CONT = prove
 (`!(c:(B->bool)#(B->real^3)) (e:real->real) S.
     (!s. e real_continuous atreal s)
     ==> (\z. lift(p2bw_cfun c (\t x:B. e t) z)) continuous_on S`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_cfun] THEN
  MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_SNDCART]);;

(* Continuity of the chart reading of the lower integrand. *)

let P2BX_LOWF_CONT = prove
 (`!(om:real^(3,1)finite_sum->bool) (c:(B->bool)#(B->real^3)) linf (eta:real->real) deta a R.
     open om /\ &0 < R /\ wan_loclip om (p2bw_cfun c linf) /\
     wan_loclip om (p2bw_cfun c (p2bx_uf linf)) /\
     (!s. eta real_continuous atreal s) /\ (!s. deta real_continuous atreal s)
     ==> (\z. lift(p2bw_cfun c (p2bx_lowf eta deta a R linf) z)) continuous_on om`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z)) continuous_on om /\
                (\z. lift(p2bw_cfun c (p2bx_uf linf) z)) continuous_on om /\
                (\z. lift(p2bw_cfun c (p2bx_hcut R linf) z)) continuous_on om`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2BX_HCUT_LOCLIP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real->real. (!s. e real_continuous atreal s)
                  ==> (\z. lift(e(drop(sndcart z)))) continuous_on (om:real^(3,1)finite_sum->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(p2bx_dchi(p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z / R - &1)))
                continuous_on om` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN REWRITE_TAC[P2BX_DCHI_CONT] THEN
    REWRITE_TAC[real_div; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_lowf eta deta a R (linf:real->B->real)) =
    (\z. --((deta:real->real)(drop(sndcart z)) * (p2bw_cfun c (p2bx_uf linf) z *
                                                  p2bw_cfun c (p2bx_hcut R linf) z)) -
         &4 / a * ((eta:real->real)(drop(sndcart z)) *
                   (p2bw_cfun c (p2bx_uf linf) z * --(p2bx_dchi(p2bw_cfun c linf z / R - &1)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun; p2bx_lowf; REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB; LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_NEG THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[LIFT_NEG] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[]]);;

let P2BX_CUT_TERM_LB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho eta deta R j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\ P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k /\ &0 < a /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\
     (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t)
     ==> drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bw_cfun (c j) (p2bx_lowf eta deta a R linf) z *
                     sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))))) <=
         drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                               (p2bw_cfun (c j) (\t x. eta t * p2bx_hcut R linf t x)) z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`]
                P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_BOX_A_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(om:num->real^(3,1)finite_sum->bool) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `linf:real->B->real`; `R:real`] P2BX_HCUT_LOCLIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `eta:real->real` P2BX_ETA_SMOOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_loclip ((om:num->real^(3,1)finite_sum->bool) j)
                  (\w. (eta:real->real)(drop(sndcart w)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  (* the cutoff F and the Lipschitz function V *)
  SUBGOAL_THEN `wan_loclip ((om:num->real^(3,1)finite_sum->bool) j)
                  (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                     (\t x. (eta:real->real) t * p2bx_hcut R (linf:real->B->real) t x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                    (\t x. (eta:real->real) t * p2bx_hcut R (linf:real->B->real) t x) =
                  (\w. eta(drop(sndcart w)) * p2bw_cfun (c j) (p2bx_hcut R linf) w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun]; ALL_TAC] THEN
    MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip ((om:num->real^(3,1)finite_sum->bool) j)
                  (\w. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf (linf:real->B->real)) w *
                       p2bw_cfun (c j) (p2bx_hcut R linf) w)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  (* the test and the integration by parts *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `eta:real->real`; `deta:real->real`;
                 `j:num`] P2BX_CUT_TEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(om:num->real^(3,1)finite_sum->bool) j`;
                 `\w. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf (linf:real->B->real)) w *
                      p2bw_cfun (c j) (p2bx_hcut R linf) w`;
                 `\z. if z IN (om:num->real^(3,1)finite_sum->bool) j
                      then p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                           (eta:real->real)(drop(sndcart z)) *
                           sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))
                      else &0`] WAN_LIP_TDER_IBP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  (* integrability of the pieces *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `\t x. (eta:real->real) t * p2bx_hcut R (linf:real->B->real) t x`; `j:num`]
                P2BX_TERM_ABSINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_uf (linf:real->B->real)) x *
               p2bw_cfun (c j) (p2bx_hcut R linf) x) *
              wan_tder (\z. if z IN (om:num->real^(3,1)finite_sum->bool) j
                            then p2bw_cfun (c j) (\t:real. (rho:num->B->real) j) z *
                                 (eta:real->real)(drop(sndcart z)) *
                                 sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))
                            else &0) x))
    absolutely_integrable_on om j` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o BETA_RULE o GEN_REWRITE_RULE I [wan_test] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_test")) (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kt:real^(3,1)finite_sum->bool`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC P2BX_GUARD_ABSINT THEN EXISTS_TAC `kt:real^(3,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; wan_tder] THEN
        MP_TAC(ISPECL [`\z. if z IN (om:num->real^(3,1)finite_sum->bool) j
                            then p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                                   (\t:real. (rho:num->B->real) j) z *
                                 (eta:real->real)(drop(sndcart z)) *
                                 sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))
                            else &0`;
                       `pastecart (vec 0:real^3) (lift(&1))`] WAN_TEST_DERIV_TEST) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[wan_test; SUBSET_UNIV] THEN ASM_REWRITE_TAC[] THEN
          EXISTS_TAC `kt:real^(3,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[wan_test] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
          REWRITE_TAC[LIFT_DROP; ETA_AX] THEN SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]]];
      X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_RING `y = &0 ==> x * y = &0`) THEN
      MP_TAC(ISPECL [`\z. if z IN (om:num->real^(3,1)finite_sum->bool) j
                          then p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                                 (\t:real. (rho:num->B->real) j) z *
                               (eta:real->real)(drop(sndcart z)) *
                               sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))
                          else &0`;
                     `(:real^(3,1)finite_sum) DIFF kt`; `y:real^(3,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
              p2bw_cfun (c j) (p2bx_lowf eta deta a R (linf:real->B->real)) z *
              sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z))))
    absolutely_integrable_on (om:num->real^(3,1)finite_sum->bool) j` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_GUARD_ABSINT THEN
    EXISTS_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BX_LOWF_CONT THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(deta:real->real) s` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart(y:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(y:real^(3,1)finite_sum)`]
                  P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `fstcart(y:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j` THENL
     [ALL_TAC;
      SUBGOAL_THEN `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) y = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      REWRITE_TAC[p2bw_cfun] THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                                  (fstcart(y:real^(3,1)finite_sum))` o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th) &&
          can (find_term ((=) `(rho:num->B->real) j`)) (concl th))) THEN
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `~(a <= drop(sndcart(y:real^(3,1)finite_sum)) /\ drop(sndcart y) <= b)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((y:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
      ASM_REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN `(eta:real->real)(drop(sndcart(y:real^(3,1)finite_sum))) = &0 /\
                  (deta:real->real)(drop(sndcart y)) = &0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[p2bw_cfun; p2bx_lowf; REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO;
                    REAL_SUB_REFL; REAL_SUB_RZERO];
    ALL_TAC] THEN
  (* the comparison *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral ((om:num->real^(3,1)finite_sum->bool) j)
      (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                p2bx_wint atlas' (g':real->B->real^3^3) (c j) (p2bx_uf (linf:real->B->real))
                          (p2bw_cfun (c j) (\t x. (eta:real->real) t * p2bx_hcut R linf t x)) z) -
           lift(wan_tder (\w. p2bw_cfun (c j) (p2bx_uf linf) w * p2bw_cfun (c j) (p2bx_hcut R linf) w) z *
                (if z IN om j
                 then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
                      sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
                 else &0)) -
           lift((p2bw_cfun (c j) (p2bx_uf linf) z * p2bw_cfun (c j) (p2bx_hcut R linf) z) *
                wan_tder (\z. if z IN om j
                              then p2bw_cfun (c j) (\t:real. rho j) z * eta(drop(sndcart z)) *
                                   sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z))
                              else &0) z)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
    EXISTS_TAC `{z | z IN (om:num->real^(3,1)finite_sum->bool) j /\
                     ~((\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                                   (linf:real->B->real) y)) differentiable at z)}` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
      MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
      MATCH_MP_TAC P2BX_CUT_POINT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                            `sub:num->num`; `K:B->bool`; `b:real`; `k:num`;
                            `Ks:num->real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The cutoffs F_R = eta(t) h_R guarded to the limit (p2bx_fcut); the global *)
(* functional at F_R is at least the time integral of the manifold integrals *)
(* of the lower integrand.                                                   *)
(* ========================================================================= *)

let p2bx_fcut = new_definition
 `p2bx_fcut (top':B topology) (eta:real->real) (R:real) (linf:real->B->real) (t:real) (x:B) =
    if x IN topspace top' then eta t * p2bx_hcut R linf t x else &0`;;

(* Weak integrands only depend on the test near the point. *)

let P2BX_WINT_LOCAL_GEN = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) uu ff hh O z.
     open O /\ z IN O /\ (!w. w IN O ==> ff w = hh w)
     ==> p2bx_wint atlas' g' c uu ff z = p2bx_wint atlas' g' c uu hh z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `open(O:real^(3,1)finite_sum->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `frechet_derivative (\w. lift((ff:real^(3,1)finite_sum->real) w)) (at z) =
                frechet_derivative (\w. lift(hh w)) (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `O:real^(3,1)finite_sum->bool`)) (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bx_wint; p2bw_bil; wan_xder] THEN ASM_SIMP_TAC[]);;

let P2BX_FCUT_CFUN = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) eta R linf z.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ fstcart z IN IMAGE (SND c) (FST c)
     ==> p2bw_cfun c (p2bx_fcut top' eta R linf) z =
         p2bw_cfun c (\t x. eta t * p2bx_hcut R linf t x) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`; `fstcart(z:real^(3,1)finite_sum)`] P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2bw_cfun; p2bx_fcut]);;

(* The global lower bound for the cutoffs. *)

let P2BX_GFUN_CUT_LB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho eta deta R.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\ P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ &0 < a /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\
     (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t) /\
     (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN K) /\
     (!t. a <= t /\ t <= b
          ==> mfd_has_integral (top',atlas') (g'(&1 - t)) (\x. &0) (topspace top') (&0))
     ==> (!t. a <= t /\ t <= b
              ==> mfd_integrable_on (top',atlas') (g'(&1 - t)) (p2bx_lowf eta deta a R linf t)
                    (topspace top')) /\
         (\y. lift(mfd_integral (top',atlas') (g'(&1 - drop y)) (topspace top')
                       (p2bx_lowf eta deta a R linf (drop y))))
           integrable_on interval[lift a,lift b] /\
         drop(integral (interval[lift a,lift b])
           (\y. lift(mfd_integral (top',atlas') (g'(&1 - drop y)) (topspace top')
                       (p2bx_lowf eta deta a R linf (drop y))))) <=
         sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                               (p2bw_cfun (c j) (p2bx_fcut top' eta R linf)) z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `p2bx_lowf eta deta a R (linf:real->B->real)`] P2BX_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN
      ASM_CASES_TAC `(eta:real->real) t = &0` THEN ASM_CASES_TAC `(deta:real->real) t = &0` THEN
      ASM_SIMP_TAC[p2bx_lowf; REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO; REAL_SUB_REFL];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a <= t /\ t <= b` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `~(p2bx_lowf eta deta a R (linf:real->B->real) t x = &0)` THEN
        ASM_CASES_TAC `(eta:real->real) t = &0` THEN ASM_CASES_TAC `(deta:real->real) t = &0` THEN
        ASM_SIMP_TAC[p2bx_lowf; REAL_MUL_LZERO; REAL_NEG_0; REAL_MUL_RZERO; REAL_SUB_REFL];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(p2bx_lowf eta deta a R (linf:real->B->real) t x = &0)` THEN
      REWRITE_TAC[p2bx_lowf; p2bx_hcut] THEN
      ASM_CASES_TAC `&2 * R <= (linf:real->B->real) t x` THENL
       [ALL_TAC; DISCH_TAC THEN ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&1 <= (linf:real->B->real) t x / R - &1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `(linf:real->B->real) t x / R - &1` P2BX_CHI_BOUNDS) THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_SUB_REFL];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                     `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                     `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                     `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                     `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                     `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`]
                    P2BX_BOX_UF) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BX_LOWF_CONT THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(deta:real->real) s` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(j:num) IN 1..k` ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integral ((om:num->real^(3,1)finite_sum->bool) j)
      (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                p2bx_wint atlas' (g':real->B->real^3^3) (c j) (p2bx_uf (linf:real->B->real))
                          (p2bw_cfun (c j) (p2bx_fcut top' eta R linf)) z)) =
    integral (om j)
      (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                          (p2bw_cfun (c j) (\t x. eta t * p2bx_hcut R linf t x)) z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_EQ] THEN AP_TERM_TAC THEN MATCH_MP_TAC P2BX_WINT_LOCAL_GEN THEN
    EXISTS_TAC `{w:real^(3,1)finite_sum | fstcart w IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_OPEN_CHART_CYL THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_FCUT_CFUN THEN
      EXISTS_TAC `atlas':((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX_CUT_TERM_LB THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                        `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                        `sub:num->num`; `K:B->bool`; `b:real`; `k:num`;
                        `Ks:num->real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

