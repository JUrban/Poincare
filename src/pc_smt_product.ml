(* ========================================================================= *)
(* pc_smt_product: product structures from functions without critical      *)
(* points (Milnor, Morse Theory, Theorem 3.1; Lee, Introduction to Smooth  *)
(* Manifolds, 2nd ed., Theorem 9.16 for flows of compactly supported       *)
(* fields).  M6b SMT_PRODUCT2_STATEMENT: between two neck spheres the slab *)
(* a <= f <= b is a product, E x = Phi (log |x|) (e0(x / |x|)) for the flow *)
(* Phi of a gradient-like field V (df(V) = 1 near the slab, radial in the  *)
(* two neck charts).  V is glued from pushforward fields of chart pieces   *)
(* by binary gluing b V1 + (1 - b) V2 with smooth bumps (pc_mfd_cutoff);   *)
(* the flow is MFLOW_GEN of pc_mfd_flow.                                   *)
(*                                                                           *)
(* Definitions; chart representatives of glued fields; the                 *)
(* bookkeeping of df(V) = 1.                                               *)
(* ========================================================================= *)

needs "src/pc_mfd_flow.ml";;
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* df(V) = 1 on U, read in every chart (f real-valued, V in preferred       *)
(* coordinates as for mfd_vrep).                                            *)

let mfp_level = new_definition
 `mfp_level (atlas:((A->bool)#(A->real^N))->bool) (f:A->real) (V:A->real^N) (U:A->bool) <=>
    !c x. c IN atlas /\ x IN FST c /\ x IN U
          ==> frechet_derivative (\y. lift(f(chart_inv c y))) (at (SND c x))
                (mfd_vrep atlas V c (SND c x)) = lift(&1)`;;

(* The inverse of a parametrization p of s on its image.                    *)

let mfp_pinv = new_definition
 `mfp_pinv (p:real^N->A) (s:real^N->bool) (x:A) = @q. q IN s /\ p q = x`;;

(* The pushforward by p of the field Fl on s (zero off the image).         *)

let mfp_push = new_definition
 `mfp_push (atlas:((A->bool)#(A->real^N))->bool) (p:real^N->A) (s:real^N->bool)
           (Fl:real^N->real^N) =
    \x. if x IN IMAGE p s
        then frechet_derivative (\q. SND (chart_at atlas x) (p q))
               (at (mfp_pinv p s x)) (Fl (mfp_pinv p s x))
        else vec 0`;;

(* Binary gluing with a weight b.                                            *)

let mfp_glue = new_definition
 `mfp_glue (b:A->real) (V1:A->real^N) (V2:A->real^N) =
    \x. b x % V1 x + (&1 - b x) % V2 x`;;

(* Chart representatives are linear in the field.                          *)

let MFP_VREP_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b V1 V2 c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (mfp_glue b V1 V2) c y =
            b(chart_inv c y) % mfd_vrep atlas V1 c y +
            (&1 - b(chart_inv c y)) % mfd_vrep atlas V2 c y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(x:A) IN FST (c:(A->bool)#(A->real^N)) /\ x IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] MFL_CHART_TRANS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_vrep; mfp_glue] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

(* Smoothness of the chart representatives of a glued field: V1 smooth in   *)
(* charts on an open O1, V2 everywhere, b smooth and zero off a compact     *)
(* L inside O1.                                                              *)

let MFP_GLUE_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b V1 V2 O1 L.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        open_in top O1 /\ compact_in top L /\ L SUBSET O1 /\
        mfd_smooth atlas (\x. lift(b x)) /\ (!x. x IN topspace top DIFF L ==> b x = &0) /\
        (!c. c IN atlas
             ==> smooth_map_on (IMAGE (SND c) (FST c INTER O1)) (mfd_vrep atlas V1 c)) /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V2 c))
        ==> !c. c IN atlas
                ==> smooth_map_on (IMAGE (SND c) (FST c))
                      (mfd_vrep atlas (mfp_glue b V1 V2) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))
                  (\y. lift(b(chart_inv c y:A)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(b x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF (L:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  ABBREV_TAC `S1 = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (O1:A->bool))` THEN
  ABBREV_TAC `S2 = IMAGE (SND (c:(A->bool)#(A->real^N)))
                         (FST c INTER (topspace top DIFF (L:A->bool)))` THEN
  SUBGOAL_THEN
   `open (S1:real^N->bool) /\ S1 SUBSET IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))) /\
    open (S2:real^N->bool) /\ S2 SUBSET IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]) THEN
    MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S1 (\y. lift(b(chart_inv (c:(A->bool)#(A->real^N)) y:A))) /\
                smooth_map_on S1 (\y. lift(&1) - lift(b(chart_inv c y:A))) /\
                smooth_map_on S1 (mfd_vrep atlas (V1:A->real^N) c) /\
                smooth_map_on S1 (mfd_vrep atlas (V2:A->real^N) c) /\
                smooth_map_on S2 (mfd_vrep atlas (V2:A->real^N) c)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on S1 (\y. lift(b(chart_inv (c:(A->bool)#(A->real^N)) y:A)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      EXPAND_TAC "S1" THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0 IN (O1:A->bool)` THENL
   [EXISTS_TAC `S1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "S1" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. drop(lift(b(chart_inv (c:(A->bool)#(A->real^N)) y:A))) %
                    mfd_vrep atlas (V1:A->real^N) c y +
                    drop(lift(&1) - lift(b(chart_inv c y))) % mfd_vrep atlas (V2:A->real^N) c y` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; DROP_SUB; DROP_VEC] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MFP_VREP_GLUE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `S2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "S2" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `mfd_vrep atlas (V2:A->real^N) (c:(A->bool)#(A->real^N))` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "S2" THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_DIFF] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:A->real`; `V1:A->real^N`; `V2:A->real^N`;
                 `c:(A->bool)#(A->real^N)`; `SND (c:(A->bool)#(A->real^N)) (p:A)`]
    MFP_VREP_GLUE) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID]);;

(* The bookkeeping of df = 1: if df(V1) = 1 on U1, df(V2) = 1 on U2 and b   *)
(* vanishes off U1, then df(glue) = 1 where b = 1 and on U2.                *)

let MFP_LEVEL_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W f b V1 V2 U1 U2.
        smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\ U1 SUBSET W /\ U2 SUBSET W /\
        mfp_level atlas f V1 U1 /\ mfp_level atlas f V2 U2 /\
        (!x. x IN topspace top /\ ~(x IN U1) ==> b x = &0)
        ==> mfp_level atlas f (mfp_glue b V1 V2) ({x | b x = &1} UNION U2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfp_level] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "l1") (CONJUNCTS_THEN2 (LABEL_TAC "l2")
                                                     (LABEL_TAC "b0")))))))) THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:A) IN U2` THENL
     [UNDISCH_TAC `(U2:A->bool) SUBSET W` THEN UNDISCH_TAC `(x:A) IN U2` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:A) IN U1` THENL
     [UNDISCH_TAC `(U1:A->bool) SUBSET W` THEN UNDISCH_TAC `(x:A) IN U1` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "b0" (fun th -> ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`) (ASSUME `~((x:A) IN U1)`)))) THEN
    UNDISCH_TAC `(b:A->real) x = &1 \/ x IN U2` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
                              (at (SND c (x:A))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (W:A->bool))`;
                   `(\x. lift((f:A->real) x)) o chart_inv (c:(A->bool)#(A->real^N))`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                       (\x. lift((f:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) (x:A)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:A->real`; `V1:A->real^N`; `V2:A->real^N`;
                 `c:(A->bool)#(A->real^N)`; `SND (c:(A->bool)#(A->real^N)) (x:A)`]
    MFP_VREP_GLUE) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  SUBGOAL_THEN
   `((x:A) IN U1
     ==> frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
           (at (SND c x)) (mfd_vrep atlas (V1:A->real^N) c (SND c x)) = lift(&1)) /\
    ((x:A) IN U2
     ==> frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
           (at (SND c x)) (mfd_vrep atlas (V2:A->real^N) c (SND c x)) = lift(&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "l1" MATCH_MP_TAC; USE_THEN "l2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN U1` THEN ASM_CASES_TAC `(x:A) IN U2` THEN ASM_SIMP_TAC[] THENL
   [REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; REAL_ARITH `b + (&1 - b) = &1`; VECTOR_MUL_LID];
    SUBGOAL_THEN `(b:A->real) x = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `(b:A->real) x = &1 \/ x IN U2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID];
    SUBGOAL_THEN `(b:A->real) x = &0` SUBST1_TAC THENL
     [USE_THEN "b0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID];
    USE_THEN "b0" (fun th -> ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`) (ASSUME `~((x:A) IN U1)`)))) THEN
    UNDISCH_TAC `(b:A->real) x = &1 \/ x IN U2` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ]]);;

(* Fields with smooth chart representatives give the flow hypothesis.      *)

let MFP_HYP_OF_VREP = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) (J:real^1->bool).
        open J /\
        (!c. c IN atlas ==> open (IMAGE (SND c) (FST c)) /\
                            smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V c))
        ==> !c. c IN atlas
                ==> smooth_map_on (J PCROSS IMAGE (SND c) (FST c))
                                  (mfl_field atlas (\t. V) c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfl_field] THEN
  MATCH_MP_TAC MFL_SMOOTH_SNDCART THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART;
               ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Pushforward fields of parametrizations.  The inverse on the              *)
(* image, smoothness of p and of its inverse in charts, the chart           *)
(* representative of the pushforward (chain rule), its smoothness, and      *)
(* df = 1 on the image when df of the pushforward of Fl is 1 upstairs.       *)
(* ------------------------------------------------------------------------- *)

(* The chain rule for a derivative read off a local factorization.          *)

let MFP_FD_CHAIN_LOCAL = prove
 (`!(g:real^M->real^P) (g1:real^M->real^N) (h:real^N->real^P) D1 Dh O q0.
        open O /\ q0 IN O /\ (g1 has_derivative D1) (at q0) /\
        (h has_derivative Dh) (at (g1 q0)) /\ (!q. q IN O ==> g q = h(g1 q))
        ==> frechet_derivative g (at q0) = Dh o D1`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`(h:real^N->real^P) o (g1:real^M->real^N)`; `O:real^M->bool`] THEN
  ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]);;

let MFP_PINV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A).
        mfd_param top atlas s p
        ==> (!q. q IN s ==> mfp_pinv p s (p q) = q) /\
            (!x. x IN IMAGE p s ==> mfp_pinv p s x IN s /\ p(mfp_pinv p s x) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!q. q IN s ==> mfp_pinv (p:real^N->A) s (p q) = q` ASSUME_TAC THENL
   [X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN REWRITE_TAC[mfp_pinv] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `r:real^N` THEN REWRITE_TAC[] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `s:real^N->bool`; `p:real^N->A`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

let MFP_PARAM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) c.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\ c IN atlas
        ==> open {q | q IN s /\ p q IN FST c} /\
            smooth_map_on {q | q IN s /\ p q IN FST c} (\q. SND c (p q)) /\
            open (IMAGE (SND c) (FST c INTER IMAGE p s)) /\
            smooth_map_on (IMAGE (SND c) (FST c INTER IMAGE p s))
                          (\y. mfp_pinv p s (chart_inv c y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^N)) s top
                 (atlas:((A->bool)#(A->real^N))->bool) (IMAGE (p:real^N->A) s) p p'` THEN
  REWRITE_TAC[mfd_diffeo; MFD_SMOOTH_MAP_INTO_EUCLIDEAN; mfd_smooth_on] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN];
    UNDISCH_TAC `mfd_smooth_map (open_set_atlas (:real^N))
                   (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_ID; INTER_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND (c:(A->bool)#(A->real^N)) o (p:real^N->A) o
                chart_inv ((:real^N),(\x:real^N. x))` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID; IN_UNIV];
    MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(p':A->real^N) o chart_inv (c:(A->bool)#(A->real^N))` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN IMAGE (p:real^N->A) s` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[]]);;

(* Transition of pushforward vectors between charts.                       *)

let MFP_PUSH_TRANS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) c0 c x v.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\
        c0 IN atlas /\ c IN atlas /\ x IN FST c0 /\ x IN FST c /\ x IN IMAGE p s
        ==> chart_jac c0 c x
              (frechet_derivative (\q. SND c0 (p q)) (at (mfp_pinv p s x)) v) =
            frechet_derivative (\q. SND c (p q)) (at (mfp_pinv p s x)) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`; `c0:(A->bool)#(A->real^N)`]
    MFP_PARAM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`; `c:(A->bool)#(A->real^N)`]
    MFP_PARAM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ABBREV_TAC `q0 = mfp_pinv (p:real^N->A) s x` THEN
  SUBGOAL_THEN `(q0:real^N) IN s /\ (p:real^N->A) q0 = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
    MFL_CHART_TRANS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\q. SND (c:(A->bool)#(A->real^N)) ((p:real^N->A) q)) (at q0) =
    chart_jac (c0:(A->bool)#(A->real^N)) c x o
    frechet_derivative (\q. SND c0 (p q)) (at q0)`
  (fun th -> REWRITE_TAC[th; o_THM]) THEN
  MATCH_MP_TAC MFP_FD_CHAIN_LOCAL THEN
  EXISTS_TAC `\q. SND (c0:(A->bool)#(A->real^N)) ((p:real^N->A) q)` THEN
  EXISTS_TAC `chart_trans (c0:(A->bool)#(A->real^N)) (c:(A->bool)#(A->real^N))` THEN
  EXISTS_TAC `{q | q IN s /\ (p:real^N->A) q IN FST (c0:(A->bool)#(A->real^N))} INTER
              {q | q IN s /\ p q IN FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{q | q IN s /\ (p:real^N->A) q IN FST (c0:(A->bool)#(A->real^N))}`;
                   `\q. SND (c0:(A->bool)#(A->real^N)) ((p:real^N->A) q)`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q0:real^N`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN REWRITE_TAC[chart_trans] THEN
    ASM_SIMP_TAC[]]);;

let MFP_PUSH_VREP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) Fl c x.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\ c IN atlas /\
        x IN FST c /\ x IN IMAGE p s
        ==> mfd_vrep atlas (mfp_push atlas p s Fl) c (SND c x) =
            frechet_derivative (\q. SND c (p q)) (at (mfp_pinv p s x))
              (Fl (mfp_pinv p s x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_vrep] THEN REWRITE_TAC[mfp_push] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFP_PUSH_TRANS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* Smoothness of the pushforward in every chart, on the chart image of the  *)
(* parametrized open set.                                                    *)

let MFP_LINEAR_BASIS_EXPAND = prove
 (`!(L:real^N->real^M) v.
        linear L ==> L v = vsum(1..dimindex(:N)) (\k. v$k % L(basis k))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let MFP_PUSH_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) Fl.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\ smooth_map_on s Fl
        ==> !c. c IN atlas
                ==> smooth_map_on (IMAGE (SND c) (FST c INTER IMAGE p s))
                                  (mfd_vrep atlas (mfp_push atlas p s Fl) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`; `c:(A->bool)#(A->real^N)`]
    MFP_PARAM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER IMAGE (p:real^N->A) s)` THEN
  ABBREV_TAC `O = {q | q IN s /\ (p:real^N->A) q IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `Q = \y. mfp_pinv (p:real^N->A) s (chart_inv (c:(A->bool)#(A->real^N)) y)` THEN
  ABBREV_TAC `g = \q. SND (c:(A->bool)#(A->real^N)) ((p:real^N->A) q)` THEN
  SUBGOAL_THEN `!y. y IN S ==> (Q:real^N->real^N) y IN O` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "Q" THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (s:real^N->bool)` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (S:real^N->bool) (Q:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "Q" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (S:real^N->bool) /\ open (O:real^N->bool) /\
                smooth_map_on O (g:real^N->real^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "O"; "g"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. vsum(1..dimindex(:N))
                    (\k. drop(lift(((Fl:real^N->real^N) ((Q:real^N->real^N) y))$k)) %
                         frechet_derivative (g:real^N->real^N) (at (Q y)) (basis k))` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real^N->bool`; `p:real^N->A`; `Fl:real^N->real^N`;
                   `c:(A->bool)#(A->real^N)`; `x:A`] MFP_PUSH_VREP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "Q" THEN EXPAND_TAC "g" THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFP_LINEAR_BASIS_EXPAND THEN
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`{q | q IN s /\ (p:real^N->A) q IN FST (c:(A->bool)#(A->real^N))}`;
                   `\q. SND (c:(A->bool)#(A->real^N)) ((p:real^N->A) q)`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `mfp_pinv (p:real^N->A) s x`) THEN
    ANTS_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
                    ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`S:real^N->bool`;
    `\k y. drop(lift(((Fl:real^N->real^N) ((Q:real^N->real^N) y))$k)) %
           frechet_derivative (g:real^N->real^N) (at (Q y)) (basis k)`;
    `1..dimindex(:N)`] SMOOTH_MAP_ON_VSUM_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `(Fl:real^N->real^N) o (Q:real^N->real^N)`; `k:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `(O:real^N->bool) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(\y. frechet_derivative (g:real^N->real^N) (at ((Q:real^N->real^N) y)) (basis k)) =
      (\q. frechet_derivative g (at q) (basis k)) o Q` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

(* df = 1 on the image when it holds upstairs.                              *)

let MFP_PUSH_LEVEL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) s (p:real^N->A) Fl.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\ open_in top W /\
        IMAGE p s SUBSET W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        (!q. q IN s ==> frechet_derivative (\q. lift(f(p q))) (at q) (Fl q) = lift(&1))
        ==> mfp_level atlas f (mfp_push atlas p s Fl) (IMAGE p s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfp_level] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`; `Fl:real^N->real^N`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] MFP_PUSH_VREP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`; `c:(A->bool)#(A->real^N)`]
    MFP_PARAM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `q0 = mfp_pinv (p:real^N->A) s x` THEN
  SUBGOAL_THEN `(q0:real^N) IN s /\ (p:real^N->A) q0 = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (W:A->bool)))
                  (\y. lift((f:A->real)(chart_inv c y))) /\
    open (IMAGE (SND c) (FST c INTER W))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                     (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\q. lift((f:A->real)((p:real^N->A) q))) (at q0) =
    frechet_derivative (\y. lift(f(chart_inv (c:(A->bool)#(A->real^N)) y))) (at (SND c x)) o
    frechet_derivative (\q. SND c (p q)) (at q0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFP_FD_CHAIN_LOCAL THEN
    EXISTS_TAC `\q. SND (c:(A->bool)#(A->real^N)) ((p:real^N->A) q)` THEN
    EXISTS_TAC `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))` THEN
    EXISTS_TAC `{q | q IN s /\ (p:real^N->A) q IN FST (c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`{q | q IN s /\ (p:real^N->A) q IN FST (c:(A->bool)#(A->real^N))}`;
                     `\q. SND (c:(A->bool)#(A->real^N)) ((p:real^N->A) q)`]
        SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q0:real^N`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (W:A->bool))`;
                     `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`]
        SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) (x:A)`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q0:real^N` o check (fun th ->
    can (find_term ((=) `lift(&1)`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[o_THM]);;

(* ------------------------------------------------------------------------- *)
(* The pieces.  In a neck chart (f(e y) = a + log|y|) the                   *)
(* radial field y has df = 1; in a chart ball the normalized gradient of    *)
(* f o chart_inv has df = 1 and is smooth, by regularity.                   *)
(* ------------------------------------------------------------------------- *)

let MFP_LOG_NORM_DERIV = prove
 (`!a (q:real^N).
        ~(q = vec 0)
        ==> ((\x. lift(a + log(norm x))) has_derivative
             (\h. inv(norm q pow 2) % lift(q dot h))) (at q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(q:real^N) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\x:real^N. lift a + (&1 / &2) % lift(log(drop(lift(norm x pow 2))))` THEN
  EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^N) DIFF {a}`] THEN
    REWRITE_TAC[GSYM closed; CLOSED_SING];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POW; GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^N. inv(norm(q:real^N) pow 2) % lift(q dot h)) =
    (\h. vec 0 + (&1 / &2) % ((\y. inv(drop(lift(norm q pow 2))) % y) o
                              (\x. &2 % lift(q dot x))) h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; VECTOR_MUL_ASSOC; VECTOR_ADD_LID] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  SUBGOAL_THEN
   `(\x:real^N. lift(log(drop(lift(norm x pow 2))))) =
    (lift o log o drop) o (\x. lift(norm x pow 2))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [ETA_AX] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT] THEN
  REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[]);;

(* The radial field in a neck chart.                                         *)

let MFP_NECK_DF = prove
 (`!(f:A->real) (e:real^N->A) a.
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e x) = a + log(norm x))
        ==> !q. q IN annulus (&1 / &2) (&2)
                ==> frechet_derivative (\q. lift(f(e q))) (at q) q = lift(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(q:real^N) IN annulus (&1 / &2) (&2)` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\q. lift((f:A->real)((e:real^N->A) q))) (at q) =
    (\h. inv(norm(q:real^N) pow 2) % lift(q dot h))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. lift(a + log(norm x))`;
                          `annulus (&1 / &2) (&2):real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_ANNULUS; MFP_LOG_NORM_DERIV];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ; GSYM NORM_POW_2] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_SIMP_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC);;

(* The normalized gradient of a function with nonvanishing derivative.      *)

let mfp_grad = new_definition
 `mfp_grad (h:real^N->real^1) (y:real^N) =
    (lambda k. drop(frechet_derivative h (at y) (basis k))):real^N`;;

let MFP_GRAD_APPLY = prove
 (`!(h:real^N->real^1) y v.
        linear(frechet_derivative h (at y))
        ==> frechet_derivative h (at y) v = lift(mfp_grad h y dot v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP MFP_LINEAR_BASIS_EXPAND th]) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VSUM; FINITE_NUMSEG; LIFT_DROP; dot; mfp_grad] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; o_THM; DROP_CMUL] THEN REAL_ARITH_TAC);;

let MFP_GRAD_FIELD = prove
 (`!(h:real^N->real^1) U.
        open U /\ smooth_map_on U h /\
        (!y. y IN U ==> ~(frechet_derivative h (at y) = (\k. vec 0)))
        ==> smooth_map_on U (\y. inv(mfp_grad h y dot mfp_grad h y) % mfp_grad h y) /\
            (!y. y IN U
                 ==> frechet_derivative h (at y)
                       (inv(mfp_grad h y dot mfp_grad h y) % mfp_grad h y) = lift(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN U ==> linear(frechet_derivative (h:real^N->real^1) (at y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `h:real^N->real^1`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> ~(mfp_grad (h:real^N->real^1) y dot mfp_grad h y = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[DOT_EQ_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term ((=) `(\k:real^N. vec 0:real^1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
    ASM_SIMP_TAC[MFP_GRAD_APPLY; DOT_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (mfp_grad (h:real^N->real^1))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[mfp_grad] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\k y. lift(drop(frechet_derivative (h:real^N->real^1) (at y) (basis k)))`]
      (INST_TYPE [`:N`,`:N`] SMOOTH_MAP_ON_LAMBDA)) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`;
                   `\y. lift(inv(drop(lift(mfp_grad (h:real^N->real^1) y dot mfp_grad h y))))`;
                   `mfp_grad (h:real^N->real^1)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\y. lift(mfp_grad (h:real^N->real^1) y dot mfp_grad h y)`]
      SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[MFP_GRAD_APPLY] THEN
    REWRITE_TAC[DOT_RMUL] THEN ASM_SIMP_TAC[REAL_MUL_LINV]]);;

(* ------------------------------------------------------------------------- *)
(* Assembling the gradient-like field.  One gluing step adds a              *)
(* piece over a compact core; chart-ball pieces at every point of W; finite *)
(* induction covers a compact set; the two neck pieces are glued last, so   *)
(* the field is exactly radial in the neck cores.                           *)
(* ------------------------------------------------------------------------- *)

let MFP_LEVEL_SUBSET = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) f V U U'.
        mfp_level atlas f V U /\ U' SUBSET U ==> mfp_level atlas f V U'`,
  REWRITE_TAC[mfp_level; SUBSET] THEN MESON_TAC[]);;

let MFP_ZERO_FIELD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c.
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (\x:A. vec 0) c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y:real^N. vec 0:real^N` THEN REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MFL_VREP_ZERO THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* One gluing step.                                                          *)

let MFP_PIECE_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) s (p:real^N->A) Fl Kc
    V2 K2 U2.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        open_in top W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        mfd_param top atlas s p /\ IMAGE p s SUBSET W /\ smooth_map_on s Fl /\
        (!q. q IN s ==> frechet_derivative (\q. lift(f(p q))) (at q) (Fl q) = lift(&1)) /\
        compact_in top Kc /\ Kc SUBSET IMAGE p s /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V2 c)) /\
        compact_in top K2 /\ (!x. x IN topspace top DIFF K2 ==> V2 x = vec 0) /\
        U2 SUBSET W /\ mfp_level atlas f V2 U2
        ==> ?V C L.
              (!c. c IN atlas
                   ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V c)) /\
              compact_in top (L UNION K2) /\
              (!x. x IN topspace top DIFF (L UNION K2) ==> V x = vec 0) /\
              open_in top C /\ Kc SUBSET C /\ C SUBSET L /\ compact_in top L /\
              L SUBSET IMAGE p s /\
              mfp_level atlas f V (C UNION U2) /\
              (!x. x IN C ==> V x = mfp_push atlas p s Fl x) /\
              (!x. x IN topspace top DIFF L ==> V x = V2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Kc:A->bool`; `IMAGE (p:real^N->A) s`] MFD_SMOOTH_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A->real` (X_CHOOSE_THEN `C:A->bool`
    (X_CHOOSE_THEN `L:A->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `mfp_glue (b:A->real) (mfp_push atlas (p:real^N->A) s Fl) (V2:A->real^N)` THEN
  MAP_EVERY EXISTS_TAC [`C:A->bool`; `L:A->bool`] THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET L` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(b:A->real) x = &1 /\ b x = &0` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFP_GLUE_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `IMAGE (p:real^N->A) s`; `L:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFP_PUSH_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[COMPACT_IN_UNION];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[mfp_glue] THEN
    SUBGOAL_THEN `(b:A->real) x = &0 /\ (V2:A->real^N) x = vec 0`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
      VECTOR_ARITH_TAC];
    MATCH_MP_TAC MFP_LEVEL_SUBSET THEN
    EXISTS_TAC `{x | (b:A->real) x = &1} UNION (U2:A->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFP_LEVEL_GLUE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`; `IMAGE (p:real^N->A) s`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFP_PUSH_LEVEL THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[mfp_glue] THEN
    SUBGOAL_THEN `(b:A->real) x = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL] THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[mfp_glue] THEN
    SUBGOAL_THEN `(b:A->real) x = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    VECTOR_ARITH_TAC]);;

(* A chart-ball piece at every point of W.                                    *)

let MFP_CHART_PIECE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) x0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\ mfd_regular_on atlas W f /\ x0 IN W
        ==> ?s (p:real^N->A) Fl O Kc.
              mfd_param top atlas s p /\ IMAGE p s SUBSET W /\ smooth_map_on s Fl /\
              (!q. q IN s
                   ==> frechet_derivative (\q. lift(f(p q))) (at q) (Fl q) = lift(&1)) /\
              open_in top O /\ x0 IN O /\ O SUBSET Kc /\ compact_in top Kc /\
              Kc SUBSET IMAGE p s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?c:(A->bool)#(A->real^N). c IN atlas /\ (x0:A) IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)` THEN
    MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `G = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (W:A->bool))` THEN
  SUBGOAL_THEN `open (G:real^N->bool) /\ SND (c:(A->bool)#(A->real^N)) (x0:A) IN G /\
                G SUBSET IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) (x0:A)` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^N)) (x0:A)` THEN
  SUBGOAL_THEN `ball(y0:real^N,r) SUBSET G /\ cball(y0,r / &2) SUBSET ball(y0,r) /\
                ball(y0,r / &2) SUBSET cball(y0,r / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = \y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))` THEN
  SUBGOAL_THEN `smooth_map_on (ball(y0:real^N,r)) (h:real^N->real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `G:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN EXPAND_TAC "h" THEN
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(y0:real^N,r)
        ==> ~(frechet_derivative (h:real^N->real^1) (at y) = (\k. vec 0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN G` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `mfd_regular_on (atlas:((A->bool)#(A->real^N))->bool) W f` THEN
    REWRITE_TAC[mfd_regular_on] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `x:A`]) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "h" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^1`; `ball(y0:real^N,r)`] MFP_GRAD_FIELD) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ball(y0:real^N,r)`; `chart_inv (c:(A->bool)#(A->real^N))`;
    `\y. inv(mfp_grad (h:real^N->real^1) y dot mfp_grad h y) % mfp_grad h y`;
    `IMAGE (chart_inv (c:(A->bool)#(A->real^N))) (ball(y0:real^N,r / &2))`;
    `IMAGE (chart_inv (c:(A->bool)#(A->real^N))) (cball(y0:real^N,r / &2))`] THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) (ball(y0:real^N,r))
                          (chart_inv (c:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
        MFD_PARAM_CHART_INV) THEN
      ASM_REWRITE_TAC[PAIR];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN G` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(y0:real^N,r)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^N` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_HALF] THEN
    EXPAND_TAC "y0" THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(y0:real^N,r)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* A field with df = 1 near a compact subset of W, by finitely many chart   *)
(* pieces.                                                                    *)

let MFP_MIDDLE_FIELD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) M.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\ mfd_regular_on atlas W f /\
        compact_in top M /\ M SUBSET W
        ==> ?V K U.
              (!c. c IN atlas
                   ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V c)) /\
              compact_in top K /\ (!x. x IN topspace top DIFF K ==> V x = vec 0) /\
              open_in top U /\ M SUBSET U /\ U SUBSET W /\ mfp_level atlas f V U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x0:A. x0 IN M
           ==> ?s (p:real^N->A) Fl O Kc.
                 mfd_param top atlas s p /\ IMAGE p s SUBSET W /\ smooth_map_on s Fl /\
                 (!q. q IN s
                      ==> frechet_derivative (\q. lift(f(p q))) (at q) (Fl q) = lift(&1)) /\
                 open_in top O /\ x0 IN O /\ O SUBSET Kc /\ compact_in top Kc /\
                 Kc SUBSET IMAGE p s`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFP_CHART_PIECE THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->real^N->bool` (X_CHOOSE_THEN `P:A->real^N->A`
    (X_CHOOSE_THEN `FL:A->real^N->real^N` (X_CHOOSE_THEN `O:A->A->bool`
      (X_CHOOSE_THEN `KC:A->A->bool` (LABEL_TAC "pc")))))) THEN
  SUBGOAL_THEN
   `?Fs. FINITE Fs /\ Fs SUBSET M /\ M SUBSET UNIONS (IMAGE (O:A->A->bool) Fs)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `IMAGE (O:A->A->bool) M` o CONJUNCT2 o
      GEN_REWRITE_RULE I [compact_in] o check (fun th ->
        concl th = `compact_in top (M:A->bool)`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      CONJ_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "pc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:A) IN M`))) THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Vs:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`O:A->A->bool`; `M:A->bool`; `Vs:(A->bool)->bool`]
      FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `Fs:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c))
              (mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (\x:A. vec 0) c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFP_ZERO_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Gs. FINITE Gs
         ==> Gs SUBSET M
             ==> ?V K U.
                   (!c. c IN atlas
                        ==> smooth_map_on (IMAGE (SND c) (FST c))
                                          (mfd_vrep atlas (V:A->real^N) c)) /\
                   compact_in top K /\ (!x. x IN topspace top DIFF K ==> V x = vec 0) /\
                   open_in top U /\ UNIONS (IMAGE (O:A->A->bool) Gs) SUBSET U /\
                   U SUBSET W /\ mfp_level atlas f V U`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`\x:A. vec 0:real^N`; `{}:A->bool`; `{}:A->bool`] THEN
      ASM_REWRITE_TAC[COMPACT_IN_EMPTY; OPEN_IN_EMPTY; IMAGE_CLAUSES;
                      UNIONS_0; EMPTY_SUBSET] THEN
      REWRITE_TAC[mfp_level; NOT_IN_EMPTY];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `Gs:A->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V2:A->real^N` (X_CHOOSE_THEN `K2:A->bool`
      (X_CHOOSE_THEN `U2:A->bool` STRIP_ASSUME_TAC))) THEN
    USE_THEN "pc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:A) IN M`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `W:A->bool`; `f:A->real`; `(S:A->real^N->bool) x`;
                   `(P:A->real^N->A) x`; `(FL:A->real^N->real^N) x`;
                   `(KC:A->A->bool) x`; `V2:A->real^N`; `K2:A->bool`; `U2:A->bool`]
      MFP_PIECE_GLUE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:A->real^N` (X_CHOOSE_THEN `C:A->bool`
      (X_CHOOSE_THEN `L:A->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`V:A->real^N`; `(L:A->bool) UNION K2`;
                          `(C:A->bool) UNION U2`] THEN
    ASM_SIMP_TAC[OPEN_IN_UNION; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
    TRY(ASM SET_TAC[]) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(L:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `Fs:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:A->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U:A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The neck pieces.                                                           *)

let MFP_NECK_SHELL = prove
 (`compact {y:real^N | &3 / &5 <= norm y /\ norm y <= &5 / &3} /\
   {y:real^N | &3 / &5 <= norm y /\ norm y <= &5 / &3} SUBSET annulus (&1 / &2) (&2) /\
   annulus (&3 / &5) (&5 / &3) SUBSET {y:real^N | &3 / &5 <= norm y /\ norm y <= &5 / &3}`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^N | &3 / &5 <= norm y /\ norm y <= &5 / &3} =
                  cball(vec 0,&5 / &3) DIFF ball(vec 0,&3 / &5)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REAL_ARITH_TAC]);;

(* The gradient-like field for two necks (M6b): df(V) = 1 on an open R      *)
(* containing the slab and both neck cores, V radial in the neck cores.     *)

let MFP_FIELD_NECKS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\ mfd_regular_on atlas W f /\
        compact_in top {x | x IN W /\ a <= f x /\ f x <= b} /\
        mfd_neck_chart top atlas e0 /\ mfd_neck_chart top atlas e1 /\
        IMAGE e0 (annulus (&1 / &2) (&2)) SUBSET W /\
        IMAGE e1 (annulus (&1 / &2) (&2)) SUBSET W /\
        DISJOINT (IMAGE e0 (annulus (&1 / &2) (&2))) (IMAGE e1 (annulus (&1 / &2) (&2))) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e0 x) = a + log(norm x)) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e1 x) = b + log(norm x))
        ==> ?V K R.
              (!c. c IN atlas
                   ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V c)) /\
              compact_in top K /\ (!x. x IN topspace top DIFF K ==> V x = vec 0) /\
              open_in top R /\ R SUBSET W /\
              {x | x IN W /\ a <= f x /\ f x <= b} SUBSET R /\
              IMAGE e0 (annulus (&3 / &5) (&5 / &3)) SUBSET R /\
              IMAGE e1 (annulus (&3 / &5) (&5 / &3)) SUBSET R /\
              mfp_level atlas f V R /\
              (!x. x IN IMAGE e0 (annulus (&3 / &5) (&5 / &3))
                   ==> V x = mfp_push atlas e0 (annulus (&1 / &2) (&2)) (\y. y) x) /\
              (!x. x IN IMAGE e1 (annulus (&3 / &5) (&5 / &3))
                   ==> V x = mfp_push atlas e1 (annulus (&1 / &2) (&2)) (\y. y) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN STRIP_TAC THEN
  ABBREV_TAC `S = {x:A | x IN W /\ a <= f x /\ f x <= b}` THEN
  ABBREV_TAC `Sh = {y:real^N | &3 / &5 <= norm y /\ norm y <= &5 / &3}` THEN
  ABBREV_TAC `A0 = annulus (&1 / &2) (&2):real^N->bool` THEN
  ABBREV_TAC `A1 = annulus (&3 / &5) (&5 / &3):real^N->bool` THEN
  SUBGOAL_THEN `compact (Sh:real^N->bool) /\ Sh SUBSET A0 /\ A1 SUBSET Sh /\
                open (A0:real^N->bool) /\ open (A1:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Sh"; "A0"; "A1"] THEN REWRITE_TAC[MFP_NECK_SHELL; OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (e0:real^N->A) A1) /\ open_in top (IMAGE (e1:real^N->A) A1) /\
    compact_in top (IMAGE (e0:real^N->A) Sh) /\ compact_in top (IMAGE (e1:real^N->A) Sh)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN; MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN;
      MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE; MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE] THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `A0:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top ((S:A->bool) DIFF (IMAGE e0 A1 UNION IMAGE e1 A1)) /\
                S DIFF (IMAGE (e0:real^N->A) A1 UNION IMAGE (e1:real^N->A) A1) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "S" THEN SET_TAC[]] THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `S:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; OPEN_IN_UNION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `f:A->real`;
                 `(S:A->bool) DIFF (IMAGE (e0:real^N->A) A1 UNION IMAGE (e1:real^N->A) A1)`]
    MFP_MIDDLE_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Vm:A->real^N` (X_CHOOSE_THEN `Km:A->bool`
    (X_CHOOSE_THEN `Um:A->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `f:A->real`; `A0:real^N->bool`; `e1:real^N->A`;
                 `\y:real^N. y`; `IMAGE (e1:real^N->A) Sh`;
                 `Vm:A->real^N`; `Km:A->bool`; `Um:A->bool`] MFP_PIECE_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN CONJ_TAC THENL
     [EXPAND_TAC "A0" THEN MATCH_MP_TAC MFP_NECK_DF THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V1:A->real^N` (X_CHOOSE_THEN `C1:A->bool`
    (X_CHOOSE_THEN `L1:A->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `f:A->real`; `A0:real^N->bool`; `e0:real^N->A`;
                 `\y:real^N. y`; `IMAGE (e0:real^N->A) Sh`;
                 `V1:A->real^N`; `(L1:A->bool) UNION Km`; `(C1:A->bool) UNION Um`]
    MFP_PIECE_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "A0" THEN MATCH_MP_TAC MFP_NECK_DF THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->real^N` (X_CHOOSE_THEN `C0:A->bool`
    (X_CHOOSE_THEN `L0:A->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`V:A->real^N`; `(L0:A->bool) UNION (L1 UNION Km)`;
                        `(C0:A->bool) UNION (C1 UNION Um)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_UNION];
    REWRITE_TAC[UNION_SUBSET] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `C0:A->bool`)) (concl th) && is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfp_push")) (concl th))) THEN
    ASM SET_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(V:A->real^N) x = V1 x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `L0:A->bool`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `V1:A->real^N`)) (concl th))) THEN
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM SET_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `C1:A->bool`)) (concl th) && is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfp_push")) (concl th))) THEN
      ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The flow of an autonomous compactly supported field.  The               *)
(* flow hypotheses, time translation (Phi from s to t is Phi for t - s),   *)
(* the group law, and the radial integral curves in a neck core.           *)
(* ------------------------------------------------------------------------- *)

let MFP_AUTO_HYP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas V c)) /\
        compact_in top K /\ (!x. x IN topspace top DIFF K ==> V x = vec 0)
        ==> mfl_hyp top atlas (\t:real. V) (:real^1) K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> smooth_map_on ((:real^1) PCROSS IMAGE (SND c) (FST c))
                          (mfl_field atlas (\t:real. (V:A->real^N)) c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFP_HYP_OF_VREP THEN REWRITE_TAC[OPEN_UNIV] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfl_hyp; OPEN_UNIV; IS_INTERVAL_UNIV; IN_UNIV] THEN ASM_SIMP_TAC[]);;

let MFP_VDERIV_SHIFT_WITHIN = prove
 (`!(u:real^1->real^N) u' t c S.
        (u has_vector_derivative u') (at (t - c) within S)
        ==> ((\r. u(r - c)) has_vector_derivative u') (at t within {r | r - c IN S})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:real^1. r - c`; `u:real^1->real^N`; `vec 1 - vec 0:real^1`;
                 `u':real^N`; `{r:real^1 | r - c IN S}`; `t:real^1`]
    VECTOR_DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[o_DEF; DROP_SUB; DROP_VEC; REAL_SUB_RZERO; VECTOR_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST];
    SUBGOAL_THEN `IMAGE (\r:real^1. r - c) {r | r - c IN S} = S` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^1` THEN
      EQ_TAC THENL [MESON_TAC[]; DISCH_TAC THEN EXISTS_TAC `y + c:real^1`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(y + c) - c:real^1 = y`];
      ASM_REWRITE_TAC[]]]);;

let MFP_CURVE_SHIFT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) L gamma c.
        mfl_curve top atlas (\t:real. V) L gamma
        ==> mfl_curve top atlas (\t:real. V) {r | r - c IN L} (\r. gamma(r - c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfl_curve] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`L:real^1->bool`; `c:real^1`] ODE_IS_INTERVAL_SHIFT) THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `(\r. (gamma:real^1->A)(r - c)) = gamma o (\r. r - c)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (L:real^1->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`c':(A->bool)#(A->real^N)`; `t:real^1`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`\r. SND (c':(A->bool)#(A->real^N)) ((gamma:real^1->A) r)`]
      MFP_VDERIV_SHIFT_WITHIN)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c':(A->bool)#(A->real^N)`; `t - c:real^1`]) THEN
    ASM_REWRITE_TAC[]]);;

(* Time translation for the flow of an autonomous field.                     *)

let MFP_FLOW_SHIFT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) K s t x.
        mfl_hyp top atlas (\t:real. V) (:real^1) K /\ x IN topspace top
        ==> mfl_flow top atlas (\t. V) s t x = mfl_flow top atlas (\t. V) (vec 0) (t - s) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`;
                 `vec 0:real^1`; `t - s:real^1`; `x:A`] MFL_FLOW_EXISTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->real^N`; `segment[vec 0:real^1,t - s]`; `g:real^1->A`;
                 `s:real^1`] MFP_CURVE_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`;
                 `{r | r - s IN segment[vec 0:real^1,t - s]}`;
                 `\r. (g:real^1->A)(r - s)`; `s:real^1`; `t:real^1`] MFL_FLOW_CURVE) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM; VECTOR_SUB_REFL; ENDS_IN_SEGMENT]);;

let MFP_FLOW_ADD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) K s t x.
        mfl_hyp top atlas (\t:real. V) (:real^1) K /\ x IN topspace top
        ==> mfl_flow top atlas (\t. V) (vec 0) (s + t) x =
            mfl_flow top atlas (\t. V) (vec 0) t (mfl_flow top atlas (\t. V) (vec 0) s x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`;
                 `vec 0:real^1`; `s:real^1`; `s + t:real^1`; `x:A`] MFL_FLOW_COCYCLE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->real^N`; `K:A->bool`; `s:real^1`; `s + t:real^1`;
                 `mfl_flow top (atlas:((A->bool)#(A->real^N))->bool) (\t:real. (V:A->real^N))
                    (vec 0) s (x:A)`] MFP_FLOW_SHIFT) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(s + t) - s:real^1 = t`] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC MFL_FLOW_IN THEN
  MAP_EVERY EXISTS_TAC [`(:real^1)`; `K:A->bool`] THEN ASM_REWRITE_TAC[IN_UNIV]);;

(* Radial integral curves in a neck core where V is the pushforward of the  *)
(* radial field.                                                              *)

let MFP_EXP_VDERIV = prove
 (`!(x:real^N) s. ((\t. exp(drop t) % x) has_vector_derivative (exp(drop s) % x)) (at s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
  MP_TAC(REAL_DIFF_CONV
   `((\t. exp t * (x:real^N)$i) has_real_derivative f) (atreal (drop s))`) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID]);;

let MFP_VREP_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) V' c x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c /\ V x = V' x
        ==> mfd_vrep atlas V c (SND c x) = mfd_vrep atlas V' c (SND c x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[mfd_vrep]);;

let MFP_RADIAL_CURVE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) (e:real^N->A) y.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas (annulus (&1 / &2) (&2)) e /\
        (!x. x IN IMAGE e (annulus (&3 / &5) (&5 / &3))
             ==> V x = mfp_push atlas e (annulus (&1 / &2) (&2)) (\y. y) x)
        ==> mfl_curve top atlas (\t:real. V)
              {r | exp(drop r) % y IN annulus (&3 / &5) (&5 / &3)}
              (\r. e(exp(drop r) % y))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A0 = annulus (&1 / &2) (&2):real^N->bool` THEN
  ABBREV_TAC `A1 = annulus (&3 / &5) (&5 / &3):real^N->bool` THEN
  SUBGOAL_THEN `(A1:real^N->bool) SUBSET A0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A0"; "A1"] THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `A0:real^N->bool`; `e:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = {r:real^1 | exp(drop r) % (y:real^N) IN A1}` THEN
  REWRITE_TAC[mfl_curve] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "L" THEN EXPAND_TAC "A1" THEN
    REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM; annulus; NORM_MUL; REAL_ABS_EXP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`; `w:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(drop u) <= exp(drop w) /\ exp(drop w) <= exp(drop v)` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_EXP_MONO_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= norm(y:real^N)` MP_TAC THENL [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(fun th -> MP_TAC th) THEN
    MP_TAC(SPECL [`exp(drop(u:real^1))`; `exp(drop(w:real^1))`; `norm(y:real^N)`]
      REAL_LE_RMUL) THEN
    MP_TAC(SPECL [`exp(drop(w:real^1))`; `exp(drop(v:real^1))`; `norm(y:real^N)`]
      REAL_LE_RMUL) THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `(\r. (e:real^N->A)(exp(drop r) % (y:real^N))) = e o (\r. exp(drop r) % y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (A0:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `r:real^1` THEN
      DISCH_TAC THEN MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_IMP_CONTINUOUS_AT THEN
      EXISTS_TAC `exp(drop r) % (y:real^N)` THEN REWRITE_TAC[MFP_EXP_VDERIV];
      EXPAND_TAC "L" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `r:real^1`] THEN
  EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `z = exp(drop r) % (y:real^N)` THEN
  SUBGOAL_THEN `(z:real^N) IN A0 /\ mfp_pinv (e:real^N->A) A0 (e z) = z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->real^N`; `mfp_push atlas (e:real^N->A) A0 (\y:real^N. y)`;
                 `c:(A->bool)#(A->real^N)`; `(e:real^N->A) z`] MFP_VREP_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `A0:real^N->bool`; `e:real^N->A`; `\y:real^N. y`;
                 `c:(A->bool)#(A->real^N)`; `(e:real^N->A) z`] MFP_PUSH_VREP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `A0:real^N->bool`; `e:real^N->A`; `c:(A->bool)#(A->real^N)`]
    MFP_PARAM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\q. SND (c:(A->bool)#(A->real^N)) ((e:real^N->A) q)) has_derivative
     frechet_derivative (\q. SND c (e q)) (at z)) (at z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{q | q IN A0 /\ (e:real^N->A) q IN FST (c:(A->bool)#(A->real^N))}`;
                   `\q. SND (c:(A->bool)#(A->real^N)) ((e:real^N->A) q)`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`\r. exp(drop r) % (y:real^N)`;
                                 `\q. SND (c:(A->bool)#(A->real^N)) ((e:real^N->A) q)`]
    ODE_HAS_VECTOR_DERIVATIVE_CHAIN)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(ASSUME `exp(drop r) % (y:real^N) = z`)) THEN
  REWRITE_TAC[MFP_EXP_VDERIV]);;

let MFP_RADIAL_FLOW = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (V:A->real^N) K (e:real^N->A) y t.
        mfl_hyp top atlas (\t:real. V) (:real^1) K /\
        mfd_param top atlas (annulus (&1 / &2) (&2)) e /\
        (!x. x IN IMAGE e (annulus (&3 / &5) (&5 / &3))
             ==> V x = mfp_push atlas e (annulus (&1 / &2) (&2)) (\y. y) x) /\
        y IN annulus (&3 / &5) (&5 / &3) /\
        exp(drop t) % y IN annulus (&3 / &5) (&5 / &3)
        ==> mfl_flow top atlas (\t. V) (vec 0) t (e y) = e(exp(drop t) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`;
                 `{r | exp(drop r) % (y:real^N) IN annulus (&3 / &5) (&5 / &3)}`;
                 `\r. (e:real^N->A)(exp(drop r) % y)`; `vec 0:real^1`; `t:real^1`]
    MFL_FLOW_CURVE) THEN
  REWRITE_TAC[DROP_VEC; REAL_EXP_0; VECTOR_MUL_LID; SUBSET_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFP_RADIAL_CURVE THEN ASM_MESON_TAC[mfl_hyp]);;

(* ------------------------------------------------------------------------- *)
(* The function f grows with unit speed along integral curves in the region *)
(* where df(V) = 1, and flow lines from the slab stay in the slab with      *)
(* f(Phi_t p) = f(p) + t as long as the level stays in [a,b] (a clopen      *)
(* argument on segment[0,t]).                                                *)
(* ------------------------------------------------------------------------- *)

let MFP_CURVE_LOCAL_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X L gamma O r.
        mfl_curve top atlas X L gamma /\ open_in top O /\ r IN L /\ gamma r IN O
        ==> ?d. &0 < d /\ !r'. r' IN L /\ r' IN ball(r,d) ==> gamma r' IN O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real^1->A`; `L:real^1->bool`; `O:A->bool`]
    MFL_OPEN_IN_CURVE_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^1` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r':real^1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r':real^1` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* Unit speed of f along curves in the region R.                            *)

let MFP_LEVEL_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) (V:A->real^N) R L gamma t.
      smooth_manifold_atlas top atlas /\ open_in top W /\
      mfd_smooth_on atlas W (\x. lift(f x)) /\
      R SUBSET W /\ mfp_level atlas f V R /\
      mfl_curve top atlas (\t:real. V) L gamma /\ t IN L /\ gamma t IN R
      ==> ((\r. lift(f(gamma r))) has_vector_derivative lift(&1)) (at t within L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real^1->A) t IN topspace top /\ gamma t IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MFL_CURVE_IN]; ASM SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `?c:(A->bool)#(A->real^N). c IN atlas /\ (gamma:real^1->A) t IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real^1->A) t)` THEN
    MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `L:real^1->bool`; `gamma:real^1->A`;
                 `FST(c:(A->bool)#(A->real^N))`; `t:real^1`] MFP_CURVE_LOCAL_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`\r. (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
           (SND c ((gamma:real^1->A) r))`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `chart_inv (c:(A->bool)#(A->real^N))`)) (concl th) &&
      is_forall (concl th) && not (can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  UNDISCH_TAC `mfp_level (atlas:((A->bool)#(A->real^N))->bool) f (V:A->real^N) R` THEN
  REWRITE_TAC[mfp_level] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `(gamma:real^1->A) t`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real^1->A) r)`;
    `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`]
   MFL_VDERIV_CHAIN_WITHIN)) THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfl_curve top (atlas:((A->bool)#(A->real^N))->bool)
                   (\t:real. (V:A->real^N)) L gamma` THEN
    REWRITE_TAC[mfl_curve] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `t:real^1`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (W:A->bool))`;
                 `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`]
    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                     (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]);;

let MFP_LEVEL_CURVE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) (V:A->real^N) R L gamma t0.
        smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\
        R SUBSET W /\ mfp_level atlas f V R /\
        mfl_curve top atlas (\t:real. V) L gamma /\ (!t. t IN L ==> gamma t IN R) /\
        t0 IN L
        ==> !t. t IN L ==> f(gamma t) = f(gamma t0) + (drop t - drop t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN L
        ==> ((\r. lift((f:A->real)((gamma:real^1->A) r))) has_vector_derivative lift(&1))
            (at t within L)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFP_LEVEL_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `W:A->bool`; `V:A->real^N`; `R:A->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k. !t. t IN L ==> lift((f:A->real)((gamma:real^1->A) t)) - t = k`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ZERO_CONSTANT THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1] THEN ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[has_vector_derivative] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\r. lift((f:A->real)((gamma:real^1->A) r))`;
                   `\x:real^1. drop x % lift(&1)`; `\r:real^1. r`; `\x:real^1. x`;
                   `at (t:real^1) within L`] HAS_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_CMUL; LIFT_DROP; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^1` th) THEN MP_TAC(SPEC `t0:real^1` th)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* Levels along segments.                                                    *)

let MFP_SEG_LEVEL = prove
 (`!a b x t r:real^1.
        a <= x /\ x <= b /\ a <= x + drop t /\ x + drop t <= b /\ r IN segment[vec 0,t]
        ==> a <= x + drop r /\ x + drop r <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; DROP_CMUL] THEN
  ASM_CASES_TAC `&0 <= drop(t:real^1)` THENL
   [SUBGOAL_THEN `&0 <= u * drop(t:real^1) /\ &0 <= (&1 - u) * drop t` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= u * --drop(t:real^1) /\ &0 <= (&1 - u) * --drop t` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID; REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC]);;

(* Flow lines from the slab stay in the slab with f(Phi_t p) = f p + t.     *)

let MFP_SLAB_FLOW = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) (V:A->real^N) K R a b p t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\
        mfl_hyp top atlas (\t:real. V) (:real^1) K /\
        open_in top R /\ R SUBSET W /\ mfp_level atlas f V R /\
        compact_in top {x | x IN W /\ a <= f x /\ f x <= b} /\
        {x | x IN W /\ a <= f x /\ f x <= b} SUBSET R /\
        p IN W /\ a <= f p /\ f p <= b /\ a <= f p + drop t /\ f p + drop t <= b
        ==> mfl_flow top atlas (\t. V) (vec 0) t p IN W /\
            f(mfl_flow top atlas (\t. V) (vec 0) t p) = f p + drop t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = {x:A | x IN W /\ a <= f x /\ f x <= b}` THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`;
                 `vec 0:real^1`; `t:real^1`; `p:A`] MFL_FLOW_EXISTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r. r IN segment[vec 0:real^1,t] ==> a <= f(p:A) + drop r /\ f p + drop r <= b`
  (LABEL_TAC "lev") THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC MFP_SEG_LEVEL THEN
    EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN segment[vec 0:real^1,t] ==> (g:real^1->A) r IN topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFL_CURVE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (S:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN]; ALL_TAC] THEN
  (* local intervals inside the segment *)
  SUBGOAL_THEN
   `!r d. r IN segment[vec 0:real^1,t] /\ &0 < d
          ==> is_interval(segment[vec 0,t] INTER ball(r,d)) /\
              segment[vec 0,t] INTER ball(r,d) SUBSET segment[vec 0,t] /\
              open_in (subtopology euclidean (segment[vec 0,t]))
                      (segment[vec 0,t] INTER ball(r,d)) /\
              r IN segment[vec 0,t] INTER ball(r,d)`
  (LABEL_TAC "loc") THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC IS_INTERVAL_INTER THEN
    REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_SEGMENT; CONVEX_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN segment[vec 0:real^1,t] /\ (g:real^1->A) r IN W /\ f(g r) = f(p:A) + drop r} =
    topspace(subtopology euclidean (segment[vec 0,t]))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    SIMP_TAC[]] THEN
  MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN EXISTS_TAC `vec 0:real^1` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT; DROP_VEC; REAL_ADD_RID] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `segment[vec 0:real^1,t]` CONNECTED_IN_EUCLIDEAN) THEN
    REWRITE_TAC[connected_in; TOPSPACE_EUCLIDEAN; SUBSET_UNIV; CONNECTED_SEGMENT];
    SET_TAC[];
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^1->A) r IN R` ASSUME_TAC THENL
     [UNDISCH_TAC `(S:A->bool) SUBSET R` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\t:real. (V:A->real^N)`; `segment[vec 0:real^1,t]`; `g:real^1->A`;
                   `R:A->bool`; `r:real^1`] MFP_CURVE_LOCAL_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "loc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `(r:real^1) IN segment[vec 0,t]`) (ASSUME `&0 < d`)))) THEN
    EXISTS_TAC `segment[vec 0:real^1,t] INTER ball(r,d)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `r':real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `W:A->bool`; `f:A->real`; `V:A->real^N`; `R:A->bool`;
                   `segment[vec 0:real^1,t] INTER ball(r,d)`; `g:real^1->A`; `r:real^1`]
      MFP_LEVEL_CURVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `segment[vec 0:real^1,t]` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `r':real^1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(g:real^1->A) r' IN R` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]];
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(g:real^1->A) r IN S` THENL
     [SUBGOAL_THEN `(g:real^1->A) r IN R /\ g r IN W` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `\t:real. (V:A->real^N)`; `segment[vec 0:real^1,t]`; `g:real^1->A`;
                     `R:A->bool`; `r:real^1`] MFP_CURVE_LOCAL_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "loc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (CONJ (ASSUME `(r:real^1) IN segment[vec 0,t]`) (ASSUME `&0 < d`)))) THEN
      EXISTS_TAC `segment[vec 0:real^1,t] INTER ball(r,d)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `r':real^1` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `W:A->bool`; `f:A->real`; `V:A->real^N`; `R:A->bool`;
                     `segment[vec 0:real^1,t] INTER ball(r,d)`; `g:real^1->A`; `r:real^1`]
        MFP_LEVEL_CURVE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `segment[vec 0:real^1,t]` THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `r':real^1`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((r:real^1) IN segment[vec 0,t] /\ (g:real^1->A) r IN W /\
                     f(g r) = f(p:A) + drop r)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(r':real^1) IN segment[vec 0,t] INTER ball(r,d)` THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(g:real^1->A) r' IN W` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `open_in top (topspace top DIFF (S:A->bool))` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `\t:real. (V:A->real^N)`; `segment[vec 0:real^1,t]`; `g:real^1->A`;
                     `topspace top DIFF (S:A->bool)`; `r:real^1`] MFP_CURVE_LOCAL_BALL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "out"))) THEN
      USE_THEN "loc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (CONJ (ASSUME `(r:real^1) IN segment[vec 0,t]`) (ASSUME `&0 < d`)))) THEN
      EXISTS_TAC `segment[vec 0:real^1,t] INTER ball(r,d)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `r':real^1` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "out" (MP_TAC o SPEC `r':real^1`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC `~((g:real^1->A) r' IN W /\ a <= f(g r') /\ f(g r') <= b)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "lev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A map from an open s that is injective and locally a                     *)
(* parametrization is a parametrization (continuity by PASTING_LEMMA,       *)
(* smoothness by SMOOTH_MAP_ON_LOCAL, the inverse by mfp_pinv).             *)
(* ------------------------------------------------------------------------- *)

let MFP_PINV_INJ = prove
 (`!(e:real^N->A) s.
        (!x y. x IN s /\ y IN s /\ e x = e y ==> x = y)
        ==> (!q. q IN s ==> mfp_pinv e s (e q) = q) /\
            (!y. y IN IMAGE e s ==> mfp_pinv e s y IN s /\ e(mfp_pinv e s y) = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!q. q IN s ==> mfp_pinv (e:real^N->A) s (e q) = q` ASSUME_TAC THENL
   [X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN REWRITE_TAC[mfp_pinv] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `r:real^N` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

let MFP_PARAM_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A).
        smooth_manifold_atlas top atlas /\ open s /\
        (!x y. x IN s /\ y IN s /\ e x = e y ==> x = y) /\
        (!x. x IN s ==> ?u. open u /\ x IN u /\ u SUBSET s /\ mfd_param top atlas u e)
        ==> mfd_param top atlas s e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->real^N->bool` (LABEL_TAC "loc")) THEN
  MP_TAC(ISPECL [`e:real^N->A`; `s:real^N->bool`] MFP_PINV_INJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> open((U:real^N->real^N->bool) x) /\ x IN U x /\ U x SUBSET s /\
            open_in top (IMAGE (e:real^N->A) (U x)) /\
            continuous_map (subtopology euclidean (U x),top) e /\
            continuous_map (subtopology top (IMAGE e (U x)),euclidean) (mfp_pinv e s) /\
            mfd_param top atlas (U x) e`
  (LABEL_TAC "lf") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `e':A->real^N` THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?q. q IN (U:real^N->real^N->bool) x /\ (e:real^N->A) q = y`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(e:real^N->A) q = y`)) THEN
    SUBGOAL_THEN `(q:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param] THEN EXISTS_TAC `mfp_pinv (e:real^N->A) s` THEN
  REWRITE_TAC[mfd_diffeo] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_IN];
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (e:real^N->A) ((U:real^N->real^N->bool) x)` THEN
    USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IMAGE_SUBSET];
    REWRITE_TAC[homeomorphic_maps] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  SUBSET_REFL] THEN
      MATCH_MP_TAC(INST_TYPE [`:real^N`,`:K`] PASTING_LEMMA) THEN
      MAP_EVERY EXISTS_TAC [`\i:real^N. (e:real^N->A)`; `U:real^N->real^N->bool`;
                            `s:real^N->bool`] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:real^N` THEN DISCH_TAC THEN
        USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(i:real^N) IN s`))) THEN
        ASM_SIMP_TAC[OPEN_SUBSET; SET_RULE `(u:real^N->bool) SUBSET s ==> s INTER u = u`];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
        USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM SET_TAC[]] THEN
      MATCH_MP_TAC(INST_TYPE [`:real^N`,`:K`] PASTING_LEMMA) THEN
      MAP_EVERY EXISTS_TAC [`\i:real^N. mfp_pinv (e:real^N->A) s`;
                            `\i:real^N. IMAGE (e:real^N->A) ((U:real^N->real^N->bool) i)`;
                            `s:real^N->bool`] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:real^N` THEN DISCH_TAC THEN
        USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(i:real^N) IN s`))) THEN
        SUBGOAL_THEN `IMAGE (e:real^N->A) s INTER IMAGE e ((U:real^N->real^N->bool) i) =
                      IMAGE e (U i)` SUBST1_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
        EXISTS_TAC `IMAGE (e:real^N->A) ((U:real^N->real^N->bool) i)` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
        SUBGOAL_THEN `?x. x IN s /\ (e:real^N->A) x = y` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `x:real^N` THEN
        USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "y" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
      ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]];
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_ID; INTER_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(U:real^N->real^N->bool) x`; `e:real^N->A`;
                     `c:(A->bool)#(A->real^N)`] MFP_PARAM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXISTS_TAC `{q | q IN (U:real^N->real^N->bool) x /\ (e:real^N->A) q IN
                       FST (c:(A->bool)#(A->real^N))}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:real^N->real^N->bool) x`; `e:real^N->A`;
                   `c:(A->bool)#(A->real^N)`] MFP_PARAM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{q | q IN (U:real^N->real^N->bool) x /\ (e:real^N->A) q IN
                     FST (c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\q. SND (c:(A->bool)#(A->real^N)) ((e:real^N->A) q)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN; mfd_smooth_on] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE (e:real^N->A) ((U:real^N->real^N->bool) x)` THEN
      USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; IMAGE_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x. x IN s /\ (e:real^N->A) x = p` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "lf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:real^N) IN s`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:real^N->real^N->bool) x`; `e:real^N->A`;
                   `c:(A->bool)#(A->real^N)`] MFP_PARAM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                      (FST c INTER IMAGE (e:real^N->A) ((U:real^N->real^N->bool) x))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(e:real^N->A) x = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. mfp_pinv (e:real^N->A) ((U:real^N->real^N->bool) x)
                      (chart_inv (c:(A->bool)#(A->real^N)) y)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `?z. z IN (U:real^N->real^N->bool) x /\ (e:real^N->A) z = q`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^N->A) z = q`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:real^N->real^N->bool) x`; `e:real^N->A`] MFP_PINV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The flow facts used by the product construction: a                       *)
(* one-parameter group of diffeomorphisms Phi t, radial in both neck cores, *)
(* moving levels of f with unit speed inside the slab.                      *)
(* ------------------------------------------------------------------------- *)

let MFP_FLOW_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
        mfd_smooth_on atlas W (\x. lift(f x)) /\ mfd_regular_on atlas W f /\
        compact_in top {x | x IN W /\ a <= f x /\ f x <= b} /\
        mfd_neck_chart top atlas e0 /\ mfd_neck_chart top atlas e1 /\
        IMAGE e0 (annulus (&1 / &2) (&2)) SUBSET W /\
        IMAGE e1 (annulus (&1 / &2) (&2)) SUBSET W /\
        DISJOINT (IMAGE e0 (annulus (&1 / &2) (&2))) (IMAGE e1 (annulus (&1 / &2) (&2))) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e0 x) = a + log(norm x)) /\
        (!x. x IN annulus (&1 / &2) (&2) ==> f(e1 x) = b + log(norm x))
        ==> ?Phi:real->A->A.
              (!t. mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                              (Phi t) (Phi (--t))) /\
              (!x. x IN topspace top ==> Phi (&0) x = x) /\
              (!s t x. x IN topspace top ==> Phi (s + t) x = Phi t (Phi s x)) /\
              (!y t. y IN annulus (&3 / &5) (&5 / &3) /\
                     exp t % y IN annulus (&3 / &5) (&5 / &3)
                     ==> Phi t (e0 y) = e0(exp t % y)) /\
              (!y t. y IN annulus (&3 / &5) (&5 / &3) /\
                     exp t % y IN annulus (&3 / &5) (&5 / &3)
                     ==> Phi t (e1 y) = e1(exp t % y)) /\
              (!p t. p IN W /\ a <= f p /\ f p <= b /\ a <= f p + t /\ f p + t <= b
                     ==> Phi t p IN W /\ f(Phi t p) = f p + t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `f:A->real`; `a:real`; `b:real`;
                 `e0:real^N->A`; `e1:real^N->A`] MFP_FIELD_NECKS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->real^N` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `R:A->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->real^N`; `K:A->bool`] MFP_AUTO_HYP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t:real. (V:A->real^N)`; `(:real^1)`; `K:A->bool`] MFLOW_GEN) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "refl") (CONJUNCTS_THEN2 (LABEL_TAC "coc")
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (K ALL_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_neck_chart]) THEN
  EXISTS_TAC `\t x. mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                      (\t:real. (V:A->real^N)) (vec 0) (lift t) (x:A)` THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN MATCH_MP_TAC MFD_DIFFEO_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`mfl_flow top (atlas:((A->bool)#(A->real^N))->bool) (\t:real. (V:A->real^N))
         (vec 0) (lift t)`;
      `mfl_flow top (atlas:((A->bool)#(A->real^N))->bool) (\t:real. (V:A->real^N))
         (lift t) (vec 0)`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `V:A->real^N`; `K:A->bool`; `lift t`; `vec 0:real^1`; `x:A`]
      MFP_FLOW_SHIFT) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_LZERO; GSYM LIFT_NEG] THEN MESON_TAC[];
    REWRITE_TAC[LIFT_NUM] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC MFP_FLOW_ADD THEN
    EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `V:A->real^N`; `K:A->bool`; `e0:real^N->A`; `y:real^N`; `lift t`]
      MFP_RADIAL_FLOW) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `V:A->real^N`; `K:A->bool`; `e1:real^N->A`; `y:real^N`; `lift t`]
      MFP_RADIAL_FLOW) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `W:A->bool`; `f:A->real`; `V:A->real^N`; `K:A->bool`; `R:A->bool`;
                   `a:real`; `b:real`; `p:A`; `lift t`] MFP_SLAB_FLOW) THEN
    ASM_REWRITE_TAC[LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the product chart.  Scalings are                             *)
(* diffeomorphisms of open sets; the transfer pinv p1 o F o p0 between two  *)
(* parametrizations through a diffeomorphism F of the manifold is smooth on *)
(* the open set where it is defined.                                         *)
(* ------------------------------------------------------------------------- *)

let MFP_SCALE_DIFFEO = prove
 (`!c U:real^N->bool.
        &0 < c /\ open U
        ==> diffeomorphism_on U (IMAGE (\x. c % x) U) (\x. c % x) (\y. inv c % y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  ASM_SIMP_TAC[OPEN_SCALING; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `!x:real^N. inv c % c % x = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ID; OPEN_SCALING; REAL_LT_IMP_NZ]);;

let MFP_TRANSFER_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s0 (p0:real^N->A) s1 p1 Fm Gm.
        smooth_manifold_atlas top atlas /\
        mfd_param top atlas s0 p0 /\ mfd_param top atlas s1 p1 /\
        mfd_diffeo top atlas (topspace top) top atlas (topspace top) Fm Gm
        ==> open {u | u IN s0 /\ Fm(p0 u) IN IMAGE p1 s1} /\
            smooth_map_on {u | u IN s0 /\ Fm(p0 u) IN IMAGE p1 s1}
                          (\u. mfp_pinv p1 s1 (Fm(p0 u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p0':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) s0 p0`)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p1':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) s1 p1`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s1:real^N->bool`; `p1:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term ((=) `Fm:A->A`)) (concl th))) THEN
  ABBREV_TAC `O = {u | u IN s0 /\ (Fm:A->A)((p0:real^N->A) u) IN IMAGE (p1:real^N->A) s1}` THEN
  SUBGOAL_THEN `open (O:real^N->bool) /\ O SUBSET s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN
     `{u | u IN s0 /\ (Fm:A->A)((p0:real^N->A) u) IN IMAGE (p1:real^N->A) s1} =
      {u | u IN s0 /\ (Fm o p0) u IN IMAGE p1 s1}` SUBST1_TAC THENL
     [REWRITE_TAC[o_THM]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuous_map (subtopology top (topspace top),top) (Fm:A->A)` THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!u:real^N. u IN O <=> u IN s0 /\ (Fm:A->A)((p0:real^N->A) u) IN IMAGE (p1:real^N->A) s1`
  (LABEL_TAC "Odef") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) O (p0:real^N->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q0:A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) O p0`)) THEN
  SUBGOAL_THEN
   `mfd_diffeo euclidean (open_set_atlas (:real^N)) O top
               (atlas:((A->bool)#(A->real^N))->bool)
               (IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O)) (Fm o p0) (q0 o (Gm:A->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `IMAGE (p0:real^N->A) O`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`topspace top:A->bool`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `O:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O) SUBSET IMAGE (p1:real^N->A) s1 /\
    open_in top (IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN USE_THEN "Odef" (fun th -> SIMP_TAC[th]);
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo] o
      check (fun th -> can (find_term ((=) `(q0:A->real^N) o (Gm:A->A)`)) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool)
               (IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O))
               euclidean (open_set_atlas (:real^N))
               (IMAGE (p1':A->real^N) (IMAGE Fm (IMAGE p0 O))) p1' p1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (p1:real^N->A) s1`; `s1:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`; `O:real^N->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O)`;
                 `euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `IMAGE (p1':A->real^N) (IMAGE (Fm:A->A) (IMAGE (p0:real^N->A) O))`;
                 `(Fm:A->A) o (p0:real^N->A)`; `(q0:A->real^N) o (Gm:A->A)`;
                 `p1':A->real^N`; `p1:real^N->A`] MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(p1':A->real^N) o (Fm:A->A) o (p0:real^N->A)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(Fm:A->A)((p0:real^N->A) u) IN IMAGE (p1:real^N->A) s1` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The product chart E x = Phi (log|x|) (e0(x/|x|)) from the                *)
(* flow facts: E = e0 near the inner sphere, the levels f(E x) = a + log|x|,*)
(* the transfer g of the level spheres, E = e1 o radial_ext g o scaling     *)
(* near the outer sphere, injectivity, and the slab as image of the shell.  *)
(* ------------------------------------------------------------------------- *)

let mfp_flowdata = new_definition
 `mfp_flowdata (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b
               (e0:real^N->A) e1 (Phi:real->A->A) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
    mfd_param top atlas (annulus (&1 / &2) (&2)) e0 /\
    mfd_param top atlas (annulus (&1 / &2) (&2)) e1 /\
    IMAGE e0 (annulus (&1 / &2) (&2)) SUBSET W /\ IMAGE e1 (annulus (&1 / &2) (&2)) SUBSET W /\
    (!x. x IN annulus (&1 / &2) (&2) ==> f(e0 x) = a + log(norm x)) /\
    (!x. x IN annulus (&1 / &2) (&2) ==> f(e1 x) = b + log(norm x)) /\
    {x | x IN W /\ f x = a} = IMAGE e0 (sphere(vec 0,&1)) /\
    {x | x IN W /\ f x = b} = IMAGE e1 (sphere(vec 0,&1)) /\
    (!t. mfd_diffeo top atlas (topspace top) top atlas (topspace top) (Phi t) (Phi (--t))) /\
    (!x. x IN topspace top ==> Phi (&0) x = x) /\
    (!s t x. x IN topspace top ==> Phi (s + t) x = Phi t (Phi s x)) /\
    (!y t. y IN annulus (&3 / &5) (&5 / &3) /\ exp t % y IN annulus (&3 / &5) (&5 / &3)
           ==> Phi t (e0 y) = e0(exp t % y)) /\
    (!y t. y IN annulus (&3 / &5) (&5 / &3) /\ exp t % y IN annulus (&3 / &5) (&5 / &3)
           ==> Phi t (e1 y) = e1(exp t % y)) /\
    (!p t. p IN W /\ a <= f p /\ f p <= b /\ a <= f p + t /\ f p + t <= b
           ==> Phi t p IN W /\ f(Phi t p) = f p + t)`;;

(* Norm facts.                                                                *)

let MFP_NORMALIZE = prove
 (`!x:real^N.
        ~(x = vec 0)
        ==> &0 < norm x /\ norm(inv(norm x) % x) = &1 /\
            exp(log(norm x)) % (inv(norm x) % x) = x /\
            !c. &0 < c ==> norm(c % x) = c * norm x /\
                           inv(norm(c % x)) % (c % x) = inv(norm x) % x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXP_LOG; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
               REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_INV_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `(inv c * inv n) * c = (inv c * c) * inv n`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let MFP_IN_ANNULUS = prove
 (`!r1 r2 (x:real^N). x IN annulus r1 r2 <=> r1 < norm x /\ norm x < r2`,
  REWRITE_TAC[annulus; IN_ELIM_THM]);;

let MFP_SPHERE_FACTS = prove
 (`!u:real^N. u IN sphere(vec 0,&1)
              ==> norm u = &1 /\ ~(u = vec 0) /\ u IN annulus (&1 / &2) (&2) /\
                  u IN annulus (&3 / &5) (&5 / &3) /\ inv(norm u) % u = u /\
                  !s. norm(exp s % u) = exp s`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[MFP_IN_ANNULUS; NORM_MUL; REAL_ABS_EXP; REAL_MUL_RID; REAL_INV_1;
                  VECTOR_MUL_LID] THEN
  CONJ_TAC THENL [DISCH_TAC THEN UNDISCH_TAC `norm(u:real^N) = &1` THEN
                  ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* E near the inner sphere is e0.                                             *)

let MFP_E_INNER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi x.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\ x IN annulus (&2 / &3) (&3 / &2)
        ==> Phi (log(norm x)) (e0(inv(norm x) % x)) = e0 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfp_flowdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(x:real^N) IN annulus (&2 / &3) (&3 / &2)` THEN
    ASM_REWRITE_TAC[MFP_IN_ANNULUS; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_NORMALIZE) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv(norm x) % (x:real^N)`; `log(norm(x:real^N))`] o
    check (fun th -> can (find_term ((=) `e0:real^N->A`)) (concl th) &&
                     can (find_term ((=) `exp`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN annulus (&2 / &3) (&3 / &2)` THEN
  ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN REAL_ARITH_TAC);;

(* The levels in the middle.                                                  *)

let MFP_E_MIDDLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi x.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\
        &1 <= norm x /\ norm x <= exp(b - a)
        ==> Phi (log(norm x)) (e0(inv(norm x) % x)) IN W /\
            f(Phi (log(norm x)) (e0(inv(norm x) % x))) = a + log(norm x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfp_flowdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 <= norm(x:real^N)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_NORMALIZE) THEN
  ABBREV_TAC `u = inv(norm x) % (x:real^N)` THEN
  SUBGOAL_THEN `(u:real^N) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(norm(x:real^N)) /\ log(norm x) <= b - a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM LOG_1] THEN ASM_SIMP_TAC[LOG_MONO_LE; REAL_LT_01];
      ONCE_REWRITE_TAC[GSYM(SPEC `b - a:real` LOG_EXP)] THEN
      ASM_SIMP_TAC[LOG_MONO_LE; REAL_EXP_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real)((e0:real^N->A) u) = a /\ e0 u IN W` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_1; REAL_ADD_RID] THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(e0:real^N->A) u`; `log(norm(x:real^N))`] o
    check (fun th -> can (find_term ((=) `W:A->bool`)) (concl th) && is_forall (concl th) &&
                     can (find_term ((=) `(Phi:real->A->A)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The transfer of the level spheres.                                         *)

let MFP_G_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> (!u. u IN sphere(vec 0,&1)
                 ==> mfp_pinv e1 (annulus (&1 / &2) (&2)) (Phi (b - a) (e0 u))
                       IN sphere(vec 0,&1) /\
                     e1(mfp_pinv e1 (annulus (&1 / &2) (&2)) (Phi (b - a) (e0 u))) =
                     Phi (b - a) (e0 u)) /\
            (!v. v IN sphere(vec 0,&1)
                 ==> mfp_pinv e0 (annulus (&1 / &2) (&2)) (Phi (a - b) (e1 v))
                       IN sphere(vec 0,&1) /\
                     e0(mfp_pinv e0 (annulus (&1 / &2) (&2)) (Phi (a - b) (e1 v))) =
                     Phi (a - b) (e1 v))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `annulus (&1 / &2) (&2):real^N->bool`; `e0:real^N->A`] MFP_PINV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `annulus (&1 / &2) (&2):real^N->bool`; `e1:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS) THENL
   [SUBGOAL_THEN `(Phi:real->A->A) (b - a) ((e0:real^N->A) u) IN
                  {x | x IN W /\ (f:A->real) x = b}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `(e0:real^N->A) u IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (e0:real^N->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(e0:real^N->A) u`; `b - a:real`] o
        check (fun th -> can (find_term ((=) `W:A->bool`)) (concl th) &&
                         is_forall (concl th) &&
                         can (find_term ((=) `(Phi:real->A->A)`)) (concl th))) THEN
      ASM_SIMP_TAC[LOG_1; REAL_ADD_RID] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `(Phi:real->A->A) (a - b) ((e1:real^N->A) u) IN
                  {x | x IN W /\ (f:A->real) x = a}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `(e1:real^N->A) u IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (e1:real^N->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(e1:real^N->A) u`; `a - b:real`] o
        check (fun th -> can (find_term ((=) `W:A->bool`)) (concl th) &&
                         is_forall (concl th) &&
                         can (find_term ((=) `(Phi:real->A->A)`)) (concl th))) THEN
      ASM_SIMP_TAC[LOG_1; REAL_ADD_RID] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[]]);;

(* E near the outer sphere is e1 o radial_ext g o scaling.                    *)

let MFP_E_OUTER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi x.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\
        x IN annulus (&2 / &3 * exp(b - a)) (&3 / &2 * exp(b - a))
        ==> Phi (log(norm x)) (e0(inv(norm x) % x)) =
            e1(radial_ext (\u. mfp_pinv e1 (annulus (&1 / &2) (&2)) (Phi (b - a) (e0 u)))
                          (exp(a - b) % x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  SUBGOAL_THEN `&0 < exp(a - b) /\ &0 < exp(b - a) /\ exp(a - b) * exp(b - a) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(a - b) + (b - a) = &0`; REAL_EXP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / &3 * exp(b - a) < norm(x:real^N) /\ norm x < &3 / &2 * exp(b - a)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN annulus (&2 / &3 * exp(b - a)) (&3 / &2 * exp(b - a))` THEN
    REWRITE_TAC[MFP_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&2 / &3 * exp(b - a) < norm(x:real^N)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) /\ norm(inv(norm x) % x) = &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFP_NORMALIZE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 / &3 < exp(a - b) * norm(x:real^N) /\ exp(a - b) * norm x < &3 / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(a - b) * (&2 / &3 * exp(b - a)) < exp(a - b) * norm(x:real^N) /\
                  exp(a - b) * norm x < exp(a - b) * (&3 / &2 * exp(b - a))` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `exp(a - b) * exp(b - a) = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(norm x) % (x:real^N)` o CONJUNCT1 o MATCH_MP MFP_G_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u = inv(norm x) % (x:real^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS o
    check (fun th -> concl th = `(u:real^N) IN sphere(vec 0,&1)`)) THEN
  SUBGOAL_THEN `(e0:real^N->A) u IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e0:real^N->A) u IN W` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^N->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `open_in top (W:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v = mfp_pinv (e1:real^N->A) (annulus (&1 / &2) (&2))
                    ((Phi:real->A->A) (b - a) ((e0:real^N->A) u))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS o
    check (fun th -> concl th = `(v:real^N) IN sphere(vec 0,&1)`)) THEN
  ABBREV_TAC `s = log(norm(x:real^N)) - (b - a)` THEN
  SUBGOAL_THEN `exp s = exp(a - b) * norm(x:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_ARITH `l - (b - a) = l + (a - b)`; REAL_EXP_ADD] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(norm(x:real^N)) = (b - a) + s` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`b - a:real`; `s:real`; `(e0:real^N->A) u`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(e1:real^N->A) v = (Phi:real->A->A) (b - a) ((e0:real^N->A) u)`)) THEN
  SUBGOAL_THEN `(Phi:real->A->A) s ((e1:real^N->A) v) = e1(exp s % v)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e1:real^N->A`)) (concl th) &&
      can (find_term ((=) `exp`)) (concl th))) THEN
    ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[radial_ext] THEN
  MP_TAC(SPEC `exp(a - b)` (CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP MFP_NORMALIZE
    (ASSUME `~(x:real^N = vec 0)`)))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]);;

(* Radial extensions of scaled points; bounds near the outer sphere.          *)

let MFP_RADIAL_SCALE = prove
 (`!(g:real^N->real^N) c x.
        &0 < c /\ ~(x = vec 0)
        ==> radial_ext g (c % x) = (c * norm x) % g(inv(norm x) % x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[radial_ext] THEN
  MP_TAC(SPEC `c:real` (CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP MFP_NORMALIZE
    (ASSUME `~(x:real^N = vec 0)`)))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let MFP_OUTER_BOUNDS = prove
 (`!a b (x:real^N).
        x IN annulus (&2 / &3 * exp(b - a)) (&3 / &2 * exp(b - a))
        ==> ~(x = vec 0) /\ &0 < norm x /\ &0 < exp(a - b) /\
            &2 / &3 < exp(a - b) * norm x /\ exp(a - b) * norm x < &3 / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MFP_IN_ANNULUS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp(a - b) /\ &0 < exp(b - a) /\ exp(a - b) * exp(b - a) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(a - b) + (b - a) = &0`; REAL_EXP_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN
  SUBGOAL_THEN `exp(a - b) * (&2 / &3 * exp(b - a)) < exp(a - b) * norm(x:real^N) /\
                exp(a - b) * norm x < exp(a - b) * (&3 / &2 * exp(b - a))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `exp(a - b) * exp(b - a) = &1` THEN REAL_ARITH_TAC);;

(* Basic consequences of the flow data.                                       *)

let MFP_FLOWDATA_BASIC = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> W SUBSET topspace top /\
            (!q. q IN annulus (&1 / &2) (&2) ==> e0 q IN W /\ e0 q IN topspace top) /\
            (!q. q IN annulus (&1 / &2) (&2) ==> e1 q IN W /\ e1 q IN topspace top) /\
            (!t p. p IN topspace top ==> Phi (--t) (Phi t p) = p /\ Phi t (Phi (--t) p) = p) /\
            (!t p. p IN topspace top ==> Phi t p IN topspace top)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfp_flowdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e0:real^N->A) q IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e0:real^N->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(W:A->bool) SUBSET topspace top` THEN
      UNDISCH_TAC `(e0:real^N->A) q IN W` THEN SET_TAC[]];
    X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e1:real^N->A) q IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e1:real^N->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(W:A->bool) SUBSET topspace top` THEN
      UNDISCH_TAC `(e1:real^N->A) q IN W` THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `p:A`] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> MP_TAC(SPECL [`t:real`; `--t:real`; `p:A`] th));
      FIRST_ASSUM(fun th -> MP_TAC(SPECL [`--t:real`; `t:real`; `p:A`] th))] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[REAL_ADD_RINV; REAL_ADD_LINV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `p:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS o SPEC `t:real` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `(p:A) IN topspace top` THEN SET_TAC[]]);;

(* The levels of E on the whole shell.                                        *)

let MFP_E_LEVEL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi x.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\
        x IN annulus (&2 / &3) (&3 / &2 * exp(b - a))
        ==> Phi (log(norm x)) (e0(inv(norm x) % x)) IN W /\
            f(Phi (log(norm x)) (e0(inv(norm x) % x))) = a + log(norm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  SUBGOAL_THEN `&2 / &3 < norm(x:real^N) /\ norm x < &3 / &2 * exp(b - a)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN annulus (&2 / &3) (&3 / &2 * exp(b - a))` THEN
    REWRITE_TAC[MFP_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(b - a)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `norm(x:real^N) < &1` THENL
   [SUBGOAL_THEN `(x:real^N) IN annulus (&2 / &3) (&3 / &2) /\ x IN annulus (&1 / &2) (&2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `x:real^N`] MFP_E_INNER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(x:real^N) <= exp(b - a)` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `x:real^N`] MFP_E_MIDDLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN annulus (&2 / &3 * exp(b - a)) (&3 / &2 * exp(b - a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_OUTER_BOUNDS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                 `Phi:real->A->A`; `x:real^N`] MFP_E_OUTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\u:real^N. mfp_pinv (e1:real^N->A) (annulus (&1 / &2) (&2))
                               ((Phi:real->A->A) (b - a) ((e0:real^N->A) u))`;
                 `exp(a - b)`; `x:real^N`] MFP_RADIAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_SPHERE_0; MFP_NORMALIZE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `inv(norm x) % (x:real^N)` o CONJUNCT1 o MATCH_MP MFP_G_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w = mfp_pinv (e1:real^N->A) (annulus (&1 / &2) (&2))
                    ((Phi:real->A->A) (b - a) ((e0:real^N->A) (inv(norm x) % x)))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS o
    check (fun th -> concl th = `(w:real^N) IN sphere(vec 0,&1)`)) THEN
  SUBGOAL_THEN `norm((exp(a - b) * norm(x:real^N)) % (w:real^N)) = exp(a - b) * norm x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < r ==> abs r = r`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(exp(a - b) * norm(x:real^N)) % (w:real^N) IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(exp(a - b) * norm(x:real^N)) % (w:real^N)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e1:real^N->A`)) (concl th) &&
      can (find_term ((=) `log`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_EXP] THEN REAL_ARITH_TAC);;

(* E is injective on the shell.                                               *)

let MFP_E_INJ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi x y.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\
        x IN annulus (&2 / &3) (&3 / &2 * exp(b - a)) /\
        y IN annulus (&2 / &3) (&3 / &2 * exp(b - a)) /\
        Phi (log(norm x)) (e0(inv(norm x) % x)) = Phi (log(norm y)) (e0(inv(norm y) % y))
        ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  SUBGOAL_THEN `log(norm(x:real^N)) = log(norm(y:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `x:real^N`] MFP_E_LEVEL) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `y:real^N`] MFP_E_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) /\ &0 < norm(y:real^N)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN annulus (&2 / &3) (&3 / &2 * exp(b - a))` THEN
    UNDISCH_TAC `(y:real^N) IN annulus (&2 / &3) (&3 / &2 * exp(b - a))` THEN
    REWRITE_TAC[MFP_IN_ANNULUS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^N = vec 0) /\ ~(y:real^N = vec 0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) IN annulus (&1 / &2) (&2) /\
                inv(norm y) % (y:real^N) IN annulus (&1 / &2) (&2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFP_IN_ANNULUS; MFP_NORMALIZE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(e0:real^N->A) (inv(norm x) % x) = e0 (inv(norm y) % y)` ASSUME_TAC THENL
   [UNDISCH_TAC `(Phi:real->A->A) (log(norm(x:real^N))) ((e0:real^N->A)(inv(norm x) % x)) =
                 Phi (log(norm(y:real^N))) (e0(inv(norm y) % y))` THEN
    REWRITE_TAC[ASSUME `log(norm(x:real^N)) = log(norm(y:real^N))`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(Phi:real->A->A) (--(log(norm(y:real^N))))`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) = inv(norm y) % y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `annulus (&1 / &2) (&2):real^N->bool`; `e0:real^N->A`] MFP_PINV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `inv(norm x) % (x:real^N)` th) THEN
                         MP_TAC(SPEC `inv(norm y) % (y:real^N)` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MFP_NORMALIZE (ASSUME `~(x:real^N = vec 0)`)) THEN
  MP_TAC(MATCH_MP MFP_NORMALIZE (ASSUME `~(y:real^N = vec 0)`)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The slab is the image of the closed shell.                                 *)

let MFP_E_SLAB = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> {p | p IN W /\ a <= f p /\ f p <= b} =
            IMAGE (\x. Phi (log(norm x)) (e0(inv(norm x) % x)))
                  {x | &1 <= norm x /\ norm x <= exp(b - a)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    ABBREV_TAC `t = (f:A->real) p - a` THEN
    SUBGOAL_THEN `&0 <= t /\ t <= b - a` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`p:A`; `--t:real`] o
      check (fun th -> can (find_term ((=) `W:A->bool`)) (concl th) && is_forall (concl th) &&
                       can (find_term ((=) `(Phi:real->A->A)`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(Phi:real->A->A) (--t) p IN {x | x IN W /\ (f:A->real) x = a}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS) THEN
    SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(W:A->bool) SUBSET topspace top` THEN UNDISCH_TAC `(p:A) IN W` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= exp t /\ exp t <= exp(b - a)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `exp t % (u:real^N)` THEN ASM_REWRITE_TAC[LOG_EXP] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_EXP_NZ; VECTOR_MUL_LID] THEN
    UNDISCH_TAC `(Phi:real->A->A) (--t) p = (e0:real^N->A) u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `x:real^N`] MFP_E_MIDDLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= l ==> a <= a + l`) THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `l <= b - a ==> a + l <= b`) THEN
      ONCE_REWRITE_TAC[GSYM(SPEC `b - a:real` LOG_EXP)] THEN
      ASM_SIMP_TAC[LOG_MONO_LE; REAL_EXP_POS_LT]]]);;

(* ------------------------------------------------------------------------- *)
(* M6b.  Near each sphere |x| = r the product chart is                       *)
(* Phi(log r) o e0 o (scaling by 1/r), hence a local parametrization; with   *)
(* injectivity it is a parametrization of the whole shell.  The transfer g   *)
(* of the level spheres and its reverse g' form a sphere diffeomorphism.     *)
(* ------------------------------------------------------------------------- *)

let MFP_SCALED_ANNULUS = prove
 (`!tau (x:real^N).
        x IN annulus (exp tau * &3 / &5) (exp tau * &5 / &3)
        ==> ~(x = vec 0) /\ &0 < norm x /\ &0 < exp(--tau) /\
            norm(exp(--tau) % x) = exp(--tau) * norm x /\
            &3 / &5 < exp(--tau) * norm x /\ exp(--tau) * norm x < &5 / &3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MFP_IN_ANNULUS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp tau /\ &0 < exp(--tau) /\ exp(--tau) * exp tau = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD; REAL_ADD_LINV; REAL_EXP_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM NORM_POS_LT; NORM_MUL; REAL_ABS_EXP] THEN
  SUBGOAL_THEN `exp(--tau) * (exp tau * &3 / &5) < exp(--tau) * norm(x:real^N) /\
                exp(--tau) * norm x < exp(--tau) * (exp tau * &5 / &3)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `exp(--tau) * exp tau = &1` THEN REAL_ARITH_TAC);;

(* Locally E = Phi tau o e0 o scaling.                                        *)

let MFP_E_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi tau x.
        mfp_flowdata top atlas W f a b e0 e1 Phi /\
        x IN annulus (exp tau * &3 / &5) (exp tau * &5 / &3)
        ==> Phi (log(norm x)) (e0(inv(norm x) % x)) = Phi tau (e0(exp(--tau) % x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SCALED_ANNULUS) THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_SPHERE_0; MFP_NORMALIZE]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SPHERE_FACTS o
    check (fun th -> concl th = `inv(norm x) % (x:real^N) IN sphere(vec 0,&1)`)) THEN
  ABBREV_TAC `sg = log(norm(x:real^N)) - tau` THEN
  SUBGOAL_THEN `exp sg = exp(--tau) * norm(x:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN REWRITE_TAC[real_sub; REAL_EXP_ADD] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(norm(x:real^N)) = sg + tau` SUBST1_TAC THENL
   [EXPAND_TAC "sg" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`sg:real`; `tau:real`;
                                      `(e0:real^N->A)(inv(norm x) % x)`] th)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(Phi:real->A->A) sg ((e0:real^N->A)(inv(norm x) % x)) =
                e0(exp sg % (inv(norm x) % x))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e0:real^N->A`)) (concl th) &&
      can (find_term ((=) `exp`)) (concl th))) THEN
    ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID]);;

let MFP_E_PARAM_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi tau.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> mfd_param top atlas (annulus (exp tau * &3 / &5) (exp tau * &5 / &3))
                      (\x. Phi (log(norm x)) (e0(inv(norm x) % x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `(Phi:real->A->A) tau o (e0:real^N->A) o (\x. exp(--tau) % x)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `tau:real`; `x:real^N`] MFP_E_LOCAL) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `IMAGE (\x:real^N. exp(--tau) % x)
                      (annulus (exp tau * &3 / &5) (exp tau * &5 / &3)) SUBSET
                annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_SCALED_ANNULUS) THEN
    ASM_REWRITE_TAC[MFP_IN_ANNULUS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `topspace top:A->bool`; `topspace top:A->bool`;
                        `(Phi:real->A->A) (--tau)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`annulus (&1 / &2) (&2):real^N->bool`;
      `IMAGE (\x:real^N. exp(--tau) % x) (annulus (exp tau * &3 / &5) (exp tau * &5 / &3))`;
      `\y:real^N. inv(exp(--tau)) % y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFP_SCALE_DIFFEO THEN
    REWRITE_TAC[OPEN_ANNULUS; REAL_EXP_POS_LT];
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (\x:real^N. exp(--tau) % x)
                       (annulus (exp tau * &3 / &5) (exp tau * &5 / &3)) SUBSET
                 annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

(* M6b product chart: a parametrization of the whole shell.                   *)

let MFP_E_PARAM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> mfd_param top atlas (annulus (&2 / &3) (&3 / &2 * exp(b - a)))
                      (\x. Phi (log(norm x)) (e0(inv(norm x) % x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  MATCH_MP_TAC MFP_PARAM_LOCAL THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^N->A`; `e1:real^N->A`;
                   `Phi:real->A->A`; `x:real^N`; `y:real^N`] MFP_E_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(x0:real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^N) IN annulus (&2 / &3) (&3 / &2 * exp(b - a))` THEN
    REWRITE_TAC[MFP_IN_ANNULUS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(annulus (exp(log(norm(x0:real^N))) * &3 / &5) (exp(log(norm x0)) * &5 / &3)
               :real^N->bool) INTER annulus (&2 / &3) (&3 / &2 * exp(b - a))` THEN
  SIMP_TAC[OPEN_INTER; OPEN_ANNULUS; INTER_SUBSET] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[EXP_LOG; MFP_IN_ANNULUS] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `annulus (exp(log(norm(x0:real^N))) * &3 / &5) (exp(log(norm x0)) * &5 / &3)
                :real^N->bool` THEN
    SIMP_TAC[OPEN_INTER; OPEN_ANNULUS; INTER_SUBSET] THEN
    FIRST_ASSUM(ACCEPT_TAC o SPEC `log(norm(x0:real^N))` o MATCH_MP MFP_E_PARAM_LOCAL)]);;

(* The transfer of the level spheres is a sphere diffeomorphism.              *)

let MFP_G_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (f:A->real) a b e0 e1 Phi.
        mfp_flowdata top atlas W f a b e0 e1 Phi
        ==> sphere_diffeo (\u. mfp_pinv e1 (annulus (&1 / &2) (&2)) (Phi (b - a) (e0 u)))
                          (\v. mfp_pinv e0 (annulus (&1 / &2) (&2)) (Phi (a - b) (e1 v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFP_FLOWDATA_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfp_flowdata]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `annulus (&1 / &2) (&2):real^N->bool`; `e0:real^N->A`] MFP_PINV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `annulus (&1 / &2) (&2):real^N->bool`; `e1:real^N->A`] MFP_PINV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `!u:real^N. u IN sphere(vec 0,&1) ==> u IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL [MESON_TAC[MFP_SPHERE_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:A. p IN topspace top
                      ==> (Phi:real->A->A) (a - b) (Phi (b - a) p) = p /\
                          Phi (b - a) (Phi (a - b) p) = p`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `a - b = --(b - a)` SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[sphere_diffeo; smooth_near] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `annulus (&1 / &2) (&2):real^N->bool`; `e0:real^N->A`;
                   `annulus (&1 / &2) (&2):real^N->bool`; `e1:real^N->A`;
                   `(Phi:real->A->A) (b - a)`; `(Phi:real->A->A) (--(b - a))`]
      MFP_TRANSFER_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{u:real^N | u IN annulus (&1 / &2) (&2) /\
                            (Phi:real->A->A) (b - a) ((e0:real^N->A) u) IN
                            IMAGE (e1:real^N->A) (annulus (&1 / &2) (&2))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o CONJUNCT1 o MATCH_MP MFP_G_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `mfp_pinv (e1:real^N->A) (annulus (&1 / &2) (&2))
                         ((Phi:real->A->A) (b - a) ((e0:real^N->A) u))` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `annulus (&1 / &2) (&2):real^N->bool`; `e1:real^N->A`;
                   `annulus (&1 / &2) (&2):real^N->bool`; `e0:real^N->A`;
                   `(Phi:real->A->A) (a - b)`; `(Phi:real->A->A) (--(a - b))`]
      MFP_TRANSFER_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{u:real^N | u IN annulus (&1 / &2) (&2) /\
                            (Phi:real->A->A) (a - b) ((e1:real^N->A) u) IN
                            IMAGE (e0:real^N->A) (annulus (&1 / &2) (&2))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o CONJUNCT2 o MATCH_MP MFP_G_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `mfp_pinv (e0:real^N->A) (annulus (&1 / &2) (&2))
                         ((Phi:real->A->A) (a - b) ((e1:real^N->A) u))` THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o CONJUNCT1 o MATCH_MP MFP_G_FACTS) THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^N` o CONJUNCT2 o MATCH_MP MFP_G_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e0:real^N->A) u IN topspace top /\ (e1:real^N->A) u IN topspace top`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* M6b: the two-ended product structure between two neck spheres.             *)

let SMT_PRODUCT2 = prove
 (`!u:A->bool. SMT_PRODUCT2_STATEMENT u`,
  REWRITE_TAC[SMT_PRODUCT2_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `f:A->real`; `a:real`; `b:real`; `e0:real^3->A`; `e1:real^3->A`]
    MFP_FLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Phi:real->A->A`) THEN
  SUBGOAL_THEN `mfp_flowdata top (atlas:((A->bool)#(A->real^3))->bool) W (f:A->real) a b
                             (e0:real^3->A) e1 (Phi:real->A->A)` ASSUME_TAC THENL
   [REWRITE_TAC[mfp_flowdata] THEN ASM_REWRITE_TAC[GSYM mfd_neck_chart]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. (Phi:real->A->A) (log(norm x)) ((e0:real^3->A)(inv(norm x) % x))`;
    `\u:real^3. mfp_pinv (e1:real^3->A) (annulus (&1 / &2) (&2))
                         ((Phi:real->A->A) (b - a) ((e0:real^3->A) u))`;
    `\v:real^3. mfp_pinv (e0:real^3->A) (annulus (&1 / &2) (&2))
                         ((Phi:real->A->A) (a - b) ((e1:real^3->A) v))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MFP_E_PARAM);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MFP_G_DIFFEO);
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^3->A`; `e1:real^3->A`;
                   `Phi:real->A->A`; `x:real^3`] MFP_E_INNER) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^3->A`; `e1:real^3->A`;
                   `Phi:real->A->A`; `x:real^3`] MFP_E_OUTER) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `f:A->real`; `a:real`; `b:real`; `e0:real^3->A`; `e1:real^3->A`;
                   `Phi:real->A->A`; `x:real^3`] MFP_E_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MFP_E_SLAB)]);;

