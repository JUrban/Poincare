(* ========================================================================= *)
(* Unit pc_p3_s14ftr (Part 3 proofs; MT Lemma 14.11 support):               *)
(* Ricci flows across the retained region of a surgery event.  Naturality   *)
(* of the Ricci form under isometries, Ricci flows under a change of        *)
(* compatible atlas (P3S_RFO_ATLAS_CHANGE), restriction commutes with       *)
(* transport by the identity, and the retained region of an event: a set    *)
(* open in the new stage and inside the old one is open in the old stage,   *)
(* lies in Omega, and carries one smooth structure (P3S_EVENT_RETAINED);    *)
(* the transported restricted flow (P3S_RFO_TRANSPORT_W).                   *)
(* ========================================================================= *)

needs "src/pc_p2c_fview.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_pde_gauge.ml";;
needs "src/pc_p2a_lgeo2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Algebra for the change of atlas.  The Ricci form as a                     *)
(* matrix quadratic form, entries of congruent matrices, derivatives of     *)
(* quadratic forms of a matrix family, and naturality of the Ricci form     *)
(* under isometries (the Ricci version of MFD_ISOMETRY_SCALAR).             *)
(* ------------------------------------------------------------------------- *)

let P3S_MFD_RICCI_DOT = prove
 (`!top atlas (g:A->real^N^N) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top
     ==> mfd_ricci atlas g x u v = u dot (mfd_ricci_matrix atlas g x ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at atlas (x:A))) (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN
  MATCH_MP_TAC LRG_LRICCI_DOT_FORM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let P3S_CONGR_ENTRY = prove
 (`!(J:real^N^N) M i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (transp J ** M ** J)$i$j = (J ** basis i) dot (M ** (J ** basis j))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let P3S_DOT_MATRIX_DERIV = prove
 (`!(M:real->real^N^N) D u v t.
     (!k l. 1 <= k /\ k <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
            ==> ((\s. M s$k$l) has_real_derivative D$k$l) (atreal t))
     ==> ((\s. u dot (M s ** v)) has_real_derivative (u dot (D ** v))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!A:real^N^N. u dot (A ** v) =
                 sum(1..dimindex(:N))
                    (\k. sum(1..dimindex(:N)) (\l. (u$k * v$l) * A$k$l))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[]);;

let P3S_ISOMETRY_RICCI = prove
 (`!top atlas top' atlas' (g:A->real^N^N) (g':B->real^N^N) f f' x u v.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
        ==> mfd_ricci atlas g x u v =
            mfd_ricci atlas' g' (f x)
              (frechet_derivative (SND(chart_at atlas' (f x)) o f o
                                   chart_inv (chart_at atlas x))
                                  (at (SND(chart_at atlas x) x)) u)
              (frechet_derivative (SND(chart_at atlas' (f x)) o f o
                                   chart_inv (chart_at atlas x))
                                  (at (SND(chart_at atlas x) x)) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
               MFDR_ISOMETRY_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_ricci] THEN
  TRANS_TAC EQ_TRANS
   `lricci (mpullback (SND(chart_at atlas' ((f:A->B) x)) o f o
                       chart_inv (chart_at atlas x))
                      (metric_local atlas' (chart_at atlas' (f x))
                                    (g':B->real^N^N)))
           (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [SYM th]) THEN
    MATCH_MP_TAC LRICCI_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Ricci flows under a change of compatible atlas.  If the                   *)
(* identity is a diffeomorphism between two smooth structures on the same    *)
(* space, a Ricci flow for the first atlas, transported by the identity, is  *)
(* a Ricci flow for the second (chart smoothness from the isometry clause    *)
(* and PDG_MPULLBACK_SMOOTH_TD; the evolution from P3S_ISOMETRY_RICCI).       *)
(* ------------------------------------------------------------------------- *)

let P3S_RFO_ATLAS_CHANGE = prove
 (`!top atlas1 atlas2 a b (g:real->A->real^N^N).
     smooth_manifold_atlas top atlas2 /\
     mfd_diffeo top atlas2 (topspace top) top atlas1 (topspace top)
                (\x. x) (\x. x) /\
     ricci_flow_on (top,atlas1) a b g
     ==> ricci_flow_on (top,atlas2) a b
           (\t. mfd_pullback_metric atlas2 atlas1 (\x. x) (g t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ricci_flow_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RM")
      (CONJUNCTS_THEN2 (LABEL_TAC "SM") (LABEL_TAC "EV"))))) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!t. mfd_isometry (top,atlas2)
          (mfd_pullback_metric atlas2 atlas1 (\x:A. x) ((g:real->A->real^N^N) t))
          (top,atlas1) (g t) (\x. x) (\x. x)`
  (LABEL_TAC "ISO") THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlas2:((A->bool)#(A->real^N))->bool)
                   (atlas1:((A->bool)#(A->real^N))->bool) (topspace top) (\x:A. x)`
  (LABEL_TAC "SMAP") THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`; `\x:A. x`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC;
    ALL_TAC] THENL
   [(* chart smoothness *)
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `chart_inv (c:(A->bool)#(A->real^N)) y0 IN FST c /\
      SND c (chart_inv c y0) = (y0:real^N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x0 = chart_inv (c:(A->bool)#(A->real^N)) y0` THEN
    SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `x0:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c1 = chart_at (atlas1:((A->bool)#(A->real^N))->bool) (x0:A)` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                   `c1:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    ABBREV_TAC
     `N0 = IMAGE (SND (c:(A->bool)#(A->real^N)))
                 (FST c INTER FST (c1:(A->bool)#(A->real^N)))` THEN
    SUBGOAL_THEN `open (N0:real^N->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "N0" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c1:(A->bool)#(A->real^N))`] MFDR_RESTRICT_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN N0
          ==> chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
              chart_inv c y IN FST (c1:(A->bool)#(A->real^N)) /\
              SND c (chart_inv c y) = (y:real^N)`
    (LABEL_TAC "N0P") THENL
     [EXPAND_TAC "N0" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (N0:real^N->bool)
        (SND (c1:(A->bool)#(A->real^N)) o (\x:A. x) o
         chart_inv (c:(A->bool)#(A->real^N)))`
    ASSUME_TAC THENL
     [USE_THEN "SMAP" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                                        `c1:(A->bool)#(A->real^N)`] o
                       REWRITE_RULE[mfd_smooth_map]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "N0" THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (N0:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`interval(lift a,lift b) PCROSS (N0:real^N->bool)`;
      `interval(lift a,lift b) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1)`;
      `\w:real^(1,N)finite_sum.
          (SND (c1:(A->bool)#(A->real^N)) o (\x:A. x) o
           chart_inv (c:(A->bool)#(A->real^N))) (sndcart w)`;
      `\z:real^(1,N)finite_sum.
          (vectorize:real^N^N->real^(N,N)finite_prod)
          (metric_local atlas1 (c1:(A->bool)#(A->real^N))
                        ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))`]
     PDG_MPULLBACK_SMOOTH_TD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
        SUBGOAL_THEN
         `(\w:real^(1,N)finite_sum.
             (SND (c1:(A->bool)#(A->real^N)) o (\x:A. x) o
              chart_inv (c:(A->bool)#(A->real^N))) (sndcart w)) =
          (SND c1 o (\x:A. x) o chart_inv c) o sndcart`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
        EXISTS_TAC `N0:real^N->bool` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                      PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
          MESON_TAC[];
          MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (N0:real^N->bool)`;
                         `\x:real^(1,N)finite_sum. x`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
          ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_ID] THEN
          MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
          REWRITE_TAC[FUN_EQ_THM; o_THM]];
        USE_THEN "SM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART; o_THM] THEN
        MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th ->
      MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] SMOOTH_MAP_ON_EQ) th)) THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; MATRIFY_VECTORIZE; ETA_AX] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "ISO" (MP_TAC o SPEC `drop t`) THEN REWRITE_TAC[mfd_isometry] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                               `c1:(A->bool)#(A->real^N)`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN
    ASM_MESON_TAC[];
    (* evolution equation *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`; `x:A`]
                  CHART_AT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`; `x:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)`]
                  MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                  `top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                  `mfd_pullback_metric atlas2 atlas1 (\x:A. x)
                     ((g:real->A->real^N^N) t)`;
                  `(g:real->A->real^N^N) t`; `\x:A. x`; `\x:A. x`; `x:A`]
                 MFDR_ISOMETRY_REP) THEN
    ASM_SIMP_TAC[] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` (X_CHOOSE_THEN `s0':real^N->bool`
      (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
    ABBREV_TAC
     `h = SND(chart_at (atlas1:((A->bool)#(A->real^N))->bool) (x:A)) o (\x:A. x) o
          chart_inv (chart_at (atlas2:((A->bool)#(A->real^N))->bool) x)` THEN
    ABBREV_TAC
     `J = matrix(frechet_derivative (h:real^N->real^N)
                   (at (SND(chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)) x)))` THEN
    SUBGOAL_THEN
     `(h:real^N->real^N) differentiable
      at (SND(chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)) x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2A_DIFFEO_ON_DIFFERENTIABLE THEN
      MAP_EVERY EXISTS_TAC [`s0:real^N->bool`; `s0':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!w. frechet_derivative (h:real^N->real^N)
            (at (SND(chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)) x)) w =
          (J:real^N^N) ** w`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "J" THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`h:real^N->real^N`;
        `at (SND(chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)) x)`]
        LINEAR_FRECHET_DERIVATIVE) THEN
      ASM_SIMP_TAC[MATRIX_WORKS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!s. mfd_pullback_metric atlas2 atlas1 (\x:A. x) ((g:real->A->real^N^N) s) x =
          transp (J:real^N^N) ** g s x ** J`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[mfd_pullback_metric; mpullback] THEN
      BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(h:real^N->real^N)
          (SND(chart_at (atlas2:((A->bool)#(A->real^N))->bool) (x:A)) x) =
        SND(chart_at (atlas1:((A->bool)#(A->real^N))->bool) x) x`
      SUBST1_TAC THENL
       [EXPAND_TAC "h" THEN REWRITE_TAC[o_THM] THEN BETA_TAC THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) s`; `x:A`] METRIC_LOCAL_AT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3S_CONGR_ENTRY] THEN
    SUBGOAL_THEN
     `--(&2) * mfd_ricci_matrix atlas2
                 (mfd_pullback_metric atlas2 atlas1 (\x:A. x)
                    ((g:real->A->real^N^N) t)) x$i$j =
      ((J:real^N^N) ** basis i) dot
      ((--(&2) %% mfd_ricci_matrix atlas1 (g t) x) ** (J ** basis j))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT] THEN
      REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `x:A`;
                     `(J:real^N^N) ** basis i`; `(J:real^N^N) ** basis j`]
                    P3S_MFD_RICCI_DOT) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas2:((A->bool)#(A->real^N))->bool`;
                    `top:A topology`; `atlas1:((A->bool)#(A->real^N))->bool`;
                    `mfd_pullback_metric atlas2 atlas1 (\x:A. x)
                       ((g:real->A->real^N^N) t)`;
                    `(g:real->A->real^N^N) t`; `\x:A. x`; `\x:A. x`; `x:A`;
                    `basis i:real^N`; `basis j:real^N`] P3S_ISOMETRY_RICCI) THEN
      ASM_SIMP_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P3S_DOT_MATRIX_DERIV THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    USE_THEN "EV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction commutes with transport by the identity, and                 *)
(* the retained region of a surgery event.  If the identity is a            *)
(* diffeomorphism on W between two atlases, restricting the transported     *)
(* metric to W equals transporting the restricted metric between the       *)
(* restricted atlases.  At an event (rfs_event_ok, identity cut-and-cap), a *)
(* set W open in the new stage and contained in the old one is open in the  *)
(* old stage, lies in Omega, the identity is a diffeomorphism on W, and the *)
(* two subspace topologies on W agree.                                      *)
(* ------------------------------------------------------------------------- *)

let P3S_RESTRICT_PULLBACK_EQ = prove
 (`!topY atlasY topX atlasX W (g:A->real^N^N) x.
     smooth_manifold_atlas topY atlasY /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\ x IN W
     ==> restrict_metric atlasY W (mfd_pullback_metric atlasY atlasX (\x. x) g) x =
         mfd_pullback_metric (restrict_atlas atlasY W) (restrict_atlas atlasX W)
                             (\x. x) (restrict_metric atlasX W g) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in topY (W:A->bool) /\ open_in topX W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RY")))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RX")))))) THEN
  USE_THEN "RY" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\x:A. x`; `\x:A. x`; `g:A->real^N^N`; `U2:A->bool`; `phi2:A->real^N`;
                 `U1:A->bool`; `phi1:A->real^N`; `x:A`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                 `U2:A->bool`; `phi2:A->real^N`; `W:A->bool`; `x:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `mpullback ((phi1:A->real^N) o (\x:A. x) o chart_inv (U2 INTER W,phi2))
              (metric_local atlasX (U1,phi1) (g:A->real^N^N)) (phi2 x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
    EXISTS_TAC `topX:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `IMAGE (phi2:A->real^N) (U2 INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                   `U2:A->bool`; `phi2:A->real^N`; `W:A->bool`; `z:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]);;

let P3S_EVENT_RETAINED = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev W.
     smooth_manifold_atlas topX atlasX /\
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     open_in topY W /\ W SUBSET topspace topX
     ==> open_in topX W /\ W SUBSET ev_omega ev /\
         smooth_manifold_atlas topY atlasY /\
         mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\
         subtopology topY W = subtopology topX W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  ABBREV_TAC `Z = topspace(ev_ztop (ev:(A)rfs_event)) DIFF ev_disc ev` THEN
  SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_MESON_TAC[closed_in]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology (ev_ztop ev) Z)
                  (restrict_atlas (ev_zatlas (ev:(A)rfs_event)) Z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) W /\ W SUBSET Z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology (ev_ztop ev) Z) (W:A->bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [mfd_cut_cap]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(W:A->bool) SUBSET
    topspace(ev_ztop ev) DIFF
    mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (topspace topX)
                   (mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm (ev:(A)rfs_event)))` THEN
    UNDISCH_TAC `(W:A->bool) SUBSET topspace topX` THEN
    UNDISCH_TAC `(W:A->bool) SUBSET Z` THEN EXPAND_TAC "Z" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (ev_ztop ev) (ev_zatlas ev) W topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
    DISCH_THEN(MP_TAC o SPEC `W:A->bool` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] MFD_DIFFEO_RESTRICT)) THEN
    ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (subtopology (ev_ztop ev) Z) (restrict_atlas (ev_zatlas ev) Z) W
               topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                   `Z:A->bool`; `W:A->bool`; `\x:A. x`; `\x:A. x`]
                  APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `topspace (subtopology (ev_ztop ev) Z) INTER topspace topX:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    UNDISCH_TAC
     `mfd_diffeo (subtopology (ev_ztop ev) Z) (restrict_atlas (ev_zatlas ev) Z) W
                 topX (atlasX:((A->bool)#(A->real^3))->bool) W (\x:A. x) (\x. x)` THEN
    REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN MESON_TAC[]]);;

(* A Ricci flow on the old stage, restricted to a region W on which the     *)
(* identity is a diffeomorphism to the new stage, transported to the new    *)
(* atlas: the family used by p3_region_flow before the event time.          *)

let P3S_RFO_TRANSPORT_W = prove
 (`!topY atlasY topX atlasX W a b (g:real->A->real^N^N).
     smooth_manifold_atlas topY atlasY /\
     mfd_diffeo topY atlasY W topX atlasX W (\x. x) (\x. x) /\
     subtopology topY W = subtopology topX W /\
     ricci_flow_on (topX,atlasX) a b g
     ==> ricci_flow_on (subtopology topY W,restrict_atlas atlasY W) a b
           (\t. restrict_metric atlasY W
                  (mfd_pullback_metric atlasY atlasX (\x. x) (g t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in topY (W:A->bool) /\ open_in topX W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology topY (W:A->bool)) = W` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`topY:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN
  EXISTS_TAC
   `\t. mfd_pullback_metric (restrict_atlas atlasY W)
          (restrict_atlas (atlasX:((A->bool)#(A->real^N))->bool) W) (\x:A. x)
          (restrict_metric atlasX W ((g:real->A->real^N^N) t))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology topY (W:A->bool)`;
      `restrict_atlas (atlasX:((A->bool)#(A->real^N))->bool) W`;
      `restrict_atlas (atlasY:((A->bool)#(A->real^N))->bool) W`;
      `a:real`; `b:real`;
      `\t. restrict_metric (atlasX:((A->bool)#(A->real^N))->bool) W
             ((g:real->A->real^N^N) t)`] P3S_RFO_ATLAS_CHANGE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^N))->bool`;
                     `W:A->bool`; `topX:A topology`;
                     `atlasX:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                     `W:A->bool`; `W:A->bool`; `\x:A. x`; `\x:A. x`]
                    APX_MFD_DIFFEO_RESTRICT) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `subtopology topY (W:A->bool) = subtopology topX W` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CF_RFO_RESTRICT THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P3S_RESTRICT_PULLBACK_EQ THEN
    MAP_EVERY EXISTS_TAC [`topY:A topology`; `topX:A topology`] THEN
    ASM_REWRITE_TAC[]]);;

