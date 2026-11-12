(* ========================================================================= *)
(* Unit pc_pde_mloc (PDE layer, tools for the linear theory on M and the     *)
(* Ricci-DeTurck flow): smoothness of tensor fields from a finite cover,     *)
(* fields defined by a chart representative, partitions of unity subordinate *)
(* to the cutoffs of a cover, transplants of families to the torus,          *)
(* localization and transport of the chart-wise norms pde_mnorm2 between     *)
(* charts.                                                                   *)
(*                                                                           *)
(* First open chart preimages and smoothness of tensor fields from the       *)
(* interiors of the pieces of a cover (PDM_TENSOR_SMOOTH_COVER).             *)
(* ========================================================================= *)

needs "src/pc_pde_mnorm.ml";;

prioritize_real();;
type_invention_error := true;;

let PDM_CHART_PREIMAGE_OPEN = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) G.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ open G
        ==> open_in top {p | p IN FST c /\ SND c p IN G}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^N)topology` THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX]);;

(* Chart representatives on overlaps are pullbacks, as maps on the overlap  *)
(* image (pair-free form of METRIC_LOCAL_TRANS).                             *)

let PDM_METRIC_LOCAL_TRANS_C = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' (v:A->real^N^N) z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        z IN IMAGE (SND c) (FST c INTER FST c')
        ==> metric_local atlas c v z =
            mpullback (chart_trans c c') (metric_local atlas c' v) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `v:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* Pullbacks of smooth matrix fields by smooth maps are smooth. *)

let PDM_MPULLBACK_SMOOTH = prove
 (`!s0 t0 (tau:real^N->real^N) (G:real^N->real^N^N).
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        smooth_map_on t0 ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
        ==> smooth_map_on s0 ((vectorize:real^N^N->real^(N,N)finite_prod) o mpullback tau G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o mpullback (tau:real^N->real^N) G =
    (\y. vsum(1..dimindex(:(N,N)finite_prod))
          (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o G) (tau y))$q %
               (vectorize:real^N^N->real^(N,N)finite_prod)
                 (transp(matrix(frechet_derivative tau (at y))) **
                  (matrify(basis q):real^N^N) **
                  matrix(frechet_derivative tau (at y)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; PDM_MPULLBACK_FORM] THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^N->bool`; `tau:real^N->real^N`;
                 `\q y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (transp(matrix(frechet_derivative (tau:real^N->real^N) (at y))) **
                           (matrify(basis q):real^N^N) **
                           matrix(frechet_derivative tau (at y)))`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`]
                PDM_FORM_SMOOTH) THEN
  ASM_SIMP_TAC[PDM_PULLBACK_COEFF_SMOOTH]);;

let PDM_TENSOR_SMOOTH_COVER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks (v:A->real^N^N).
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks
        ==> (pde_tensor_smooth atlas v <=>
             !i. i < n0 ==> smooth_map_on (interior(ks i))
                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               metric_local atlas (cs i) v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cover] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cov") ASSUME_TAC)) THEN
  EQ_TAC THENL
   [REWRITE_TAC[pde_tensor_smooth] THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[pde_tensor_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?y. chart_inv (c:(A->bool)#(A->real^N)) z = chart_inv (cs i) y /\
        y IN interior((ks:num->real^N->bool) i)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "cov" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `W = {p:A | p IN FST((cs:num->(A->bool)#(A->real^N)) i) /\
               SND(cs i) p IN interior((ks:num->real^N->bool) i)}` THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC PDM_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET FST((cs:num->(A->bool)#(A->real^N)) i)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
  ASSUME_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) z` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o
              mpullback (chart_trans (c:(A->bool)#(A->real^N)) (cs i))
                        (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) v)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDM_METRIC_LOCAL_TRANS_C THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                           ==> (x:real^N) IN IMAGE (f:A->real^N) s ==> x IN IMAGE f t`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDM_MPULLBACK_SMOOTH THEN
  EXISTS_TAC `interior((ks:num->real^N->bool) i)` THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                      (FST c INTER FST((cs:num->(A->bool)#(A->real^N)) i))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST((cs:num->(A->bool)#(A->real^N)) i)`;
                   `SND((cs:num->(A->bool)#(A->real^N)) i)`] CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST((cs:num->(A->bool)#(A->real^N)) i)`;
                 `SND((cs:num->(A->bool)#(A->real^N)) i)`; `p:A`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `(p:A) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* A partition of unity subordinate to the cutoffs of a cover                *)
(* (each phi_i vanishes off a compact set inside an open set where psi_i is *)
(* 1), via a shrinking of the open sets where the cutoffs are 1.            *)
(* ------------------------------------------------------------------------- *)

(* Closed and open chart balls inside an open set. *)

let PDM_CHART_BALL_PIECE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W y r.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        cball(y,r) SUBSET IMAGE phi (U INTER W)
        ==> compact_in top {p | p IN U /\ phi p IN cball(y,r)} /\
            {p | p IN U /\ phi p IN cball(y,r)} SUBSET W /\
            open_in top {p | p IN U /\ phi p IN ball(y,r)} /\
            {p | p IN U /\ phi p IN ball(y,r)} SUBSET {p | p IN U /\ phi p IN cball(y,r)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:A->real^N) p IN IMAGE phi (U INTER W)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `p:A = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `U:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`y:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[]]);;

(* Shrinking: compact sets C i inside open sets W i where psi i = 1 cover    *)
(* the space.                                                                *)

let PDM_CUTOFF_SHRINK = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs psi.
        smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cutoffs (top,atlas) n0 cs psi
        ==> ?C W. (!i. i < n0
                       ==> compact_in top (C i) /\ open_in top (W i) /\ C i SUBSET W i /\
                           !x. x IN W i ==> psi i x = &1) /\
                  (!x. x IN topspace top ==> ?i. i < n0 /\ x IN C i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cutoffs] THEN STRIP_TAC THEN
  ABBREV_TAC
   `W = \i. UNIONS {V | open_in top V /\ !z:A. z IN V ==> (psi:num->A->real) i z = &1}` THEN
  SUBGOAL_THEN
   `!i. open_in top ((W:num->A->bool) i) /\ !x. x IN W i ==> (psi:num->A->real) i x = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "W" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNIONS THEN SIMP_TAC[IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top ==> ?i. i < n0 /\ x IN (W:num->A->bool) i`
  (LABEL_TAC "inW") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> can (term_match [] `!x:A. x IN topspace top ==> P x`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?II UU PH RR. !x:A. x IN topspace top
        ==> II x < n0 /\ x IN (W:num->A->bool) (II x) /\
            (UU x,PH x) IN atlas /\ x IN UU x /\ &0 < RR x /\
            cball((PH x:A->real^N) x,&2 * RR x) SUBSET IMAGE (PH x) (UU x INTER W (II x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "inW" (fun th -> MP_TAC(MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFDC_LOCAL_BALL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> cball((PH x:A->real^N) x,RR x) SUBSET
              IMAGE (PH x) (UU x INTER (W:num->A->bool) (II x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball((PH:A->A->real^N) x x,&2 * RR x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CBALL THEN
      SUBGOAL_THEN `&0 < (RR:A->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?FF. FINITE FF /\ FF SUBSET topspace top /\
        topspace top SUBSET
        UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                                  (PH x:A->real^N) p IN ball(PH x x,RR x)}) FF)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in] o
      GEN_REWRITE_RULE I [compact_space]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\x:A. {p | p IN UU x /\ (PH x:A->real^N) p IN ball(PH x x,RR x)})
            (topspace top)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
        ASM_SIMP_TAC[ETA_AX];
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
        ASM_SIMP_TAC[CENTRE_IN_BALL]];
      ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> (a /\ b) /\ c`] THEN
      REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC
   `\i. UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                                  (PH x:A->real^N) p IN cball(PH x x,RR x)})
                      {x | x IN FF /\ (II:A->num) x = i})` THEN
  EXISTS_TAC `W:num->A->bool` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(UU:A->A->bool) x`; `(PH:A->A->real^N) x`;
                     `(W:num->A->bool) ((II:A->num) x)`; `(PH:A->A->real^N) x x`;
                     `(RR:A->real) x`] PDM_CHART_BALL_PIECE) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(UU:A->A->bool) x`; `(PH:A->A->real^N) x`;
                     `(W:num->A->bool) ((II:A->num) x)`; `(PH:A->A->real^N) x x`;
                     `(RR:A->real) x`] PDM_CHART_BALL_PIECE) THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?f:A. f IN FF /\ x IN UU f /\ (PH f:A->real^N) x IN ball(PH f f,RR f)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `topspace top SUBSET
        UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                                  (PH x:A->real^N) p IN ball(PH x x,RR x)}) FF)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(II:A->num) f` THEN
    SUBGOAL_THEN `(f:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `f:A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]]);;

(* The partition of unity. *)

let PDM_CUTOFF_PARTITION = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs psi.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cutoffs (top,atlas) n0 cs psi
        ==> ?phi. (!i. i < n0
                       ==> mfd_smooth atlas (\x. lift(phi i x)) /\
                           (!x. &0 <= phi i x /\ phi i x <= &1) /\
                           ?L V. compact_in top L /\ open_in top V /\ L SUBSET V /\
                                 (!x. ~(x IN L) ==> phi i x = &0) /\
                                 (!x. x IN V ==> psi i x = &1)) /\
                  (!x. x IN topspace top ==> sum {i | i < n0} (\i. phi i x) = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `psi:num->A->real`] PDM_CUTOFF_SHRINK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num->A->bool` (X_CHOOSE_THEN `W:num->A->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "CW") (LABEL_TAC "cov")))) THEN
  SUBGOAL_THEN
   `!i. ?chi V L. i < n0
           ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift(chi x)) /\
               (!x:A. &0 <= chi x /\ chi x <= &1) /\
               open_in top V /\ (C:num->A->bool) i SUBSET V /\ (!x. x IN V ==> chi x = &1) /\
               compact_in top L /\ L SUBSET (W:num->A->bool) i /\
               (!x. x IN topspace top DIFF L ==> chi x = &0)`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC MFD_SMOOTH_CUTOFF THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `chi:num->A->real` (X_CHOOSE_THEN `V:num->A->bool`
      (X_CHOOSE_THEN `L:num->A->bool` (LABEL_TAC "chi"))))] THEN
  ABBREV_TAC `S = \x:A. sum {i | i < n0} (\i. (chi:num->A->real) i x)` THEN
  SUBGOAL_THEN `!x:A. &0 <= (S:A->real) x /\
                      !i. i < n0 ==> (chi:num->A->real) i x <= S x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN EXPAND_TAC "S" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`{i:num}`; `{i:num | i < n0}`; `\j. (chi:num->A->real) j x`]
                    SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SUBSET; IN_SING; IN_ELIM_THM; IN_DIFF] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> &1 <= (S:A->real) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "cov" (fun th -> MP_TAC(MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(chi:num->A->real) i x` THEN
    ASM_SIMP_TAC[] THEN
    USE_THEN "chi" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\i (x:A). if x IN topspace top then (chi:num->A->real) i x / (S:A->real) x
                        else &0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "chi" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[mfd_smooth] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC
       `\z. lift(drop(((\x:A. lift((chi:num->A->real) i x)) o chart_inv c) z) /
                 drop((\z. lift(sum {j | j < n0}
                          (\j. drop(((\x:A. lift(chi j x)) o
                                     chart_inv (c:(A->bool)#(A->real^N))) z)))) z))` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN EXPAND_TAC "S" THEN REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                                (\x. lift((chi:num->A->real) i x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; ETA_AX] THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        USE_THEN "chi" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
        STRIP_TAC THEN
        UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                                (\x. lift((chi:num->A->real) j x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; o_THM] THEN
        SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `&1 <= (S:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z)` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "S" THEN REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> ~(x = &0)`) THEN
                             ACCEPT_TAC th)];
      X_GEN_TAC `x:A` THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
      SUBGOAL_THEN `&1 <= (S:A->real) x` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (S:A->real) x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID];
      MAP_EVERY EXISTS_TAC [`(L:num->A->bool) i`; `(W:num->A->bool) i`] THEN
      USE_THEN "CW" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(chi:num->A->real) i x = &0` (fun th -> REWRITE_TAC[th; real_div;
                                                                   REAL_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; SUM_RMUL] THEN
    SUBGOAL_THEN `sum {i | i < n0} (\i. (chi:num->A->real) i x) = (S:A->real) x` SUBST1_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN
    SUBGOAL_THEN `&1 <= (S:A->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Space-time cutoffs and periodization in the space variable                *)
(* (maps on S PCROSS U, S a set of times), for families smooth up to an     *)
(* initial time (pde_upto): cutoff and periodization of families,          *)
(* dilation, and the transplant of families PDM_TRANSPLANT_UPTO.            *)
(* ------------------------------------------------------------------------- *)

(* Space-time cutoff in the space variable and zero extension. *)

let PDM_ST_CUTOFF_EXT = prove
 (`!S U (FF:real^(1,N)finite_sum->real^K) (chi:real^N->real) k.
        open S /\ open U /\ smooth_map_on (S PCROSS U) FF /\
        smooth_map_on (:real^N) (\y. lift(chi y)) /\
        compact k /\ k SUBSET U /\ (!y. ~(y IN k) ==> chi y = &0)
        ==> smooth_map_on (S PCROSS (:real^N))
              (\z. if sndcart z IN U then chi(sndcart z) % FF z else vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN X_GEN_TAC `z0:real^(1,N)finite_sum` THEN
  DISCH_TAC THEN ASM_CASES_TAC `sndcart(z0:real^(1,N)finite_sum) IN U` THENL
   [EXISTS_TAC `(S:real^1->bool) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z0:real^(1,N)finite_sum) IN S PCROSS (:real^N)` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. drop((\y. lift((chi:real^N->real) y)) (sndcart z)) %
                                         (FF:real^(1,N)finite_sum->real^K) z` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; ETA_AX] THEN
    SUBGOAL_THEN
     `(\z:real^(1,N)finite_sum. lift((chi:real^N->real) (sndcart z))) =
      (\y. lift(chi y)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`(S:real^1->bool) PCROSS (U:real^N->bool)`;
                   `\x:real^(1,N)finite_sum. x`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    EXISTS_TAC `(S:real^1->bool) PCROSS ((:real^N) DIFF k)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z0:real^(1,N)finite_sum) IN S PCROSS (:real^N)` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                  IN_DIFF; IN_UNIV] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. vec 0:real^K` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_DIFF; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* Periodization in the space variable. *)

let PDM_ST_PERIODIZE_SMOOTH = prove
 (`!S (FF:real^(1,N)finite_sum->real^K) a.
        open S /\ smooth_map_on (S PCROSS (:real^N)) FF /\ &0 < a /\ a <= &1 / &2 /\
        (!z. ~(sndcart z IN interval[a % vec 1:real^N,(&1 - a) % vec 1]) ==> FF z = vec 0)
        ==> smooth_map_on (S PCROSS (:real^N))
              (\z. FF(pastecart (fstcart z) (pdm_frac(sndcart z))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN X_GEN_TAC `z0:real^(1,N)finite_sum` THEN
  DISCH_TAC THEN
  EXISTS_TAC `((S:real^1->bool) PCROSS (:real^N)) INTER ball(z0:real^(1,N)finite_sum,a)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_UNIV; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z. (FF:real^(1,N)finite_sum->real^K)
                    (z - pastecart (vec 0) (pdm_floorv(sndcart(z0:real^(1,N)finite_sum))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`\y:real^N. (FF:real^(1,N)finite_sum->real^K)
                                  (pastecart (fstcart(z:real^(1,N)finite_sum)) y)`;
                   `a:real`; `sndcart(z0:real^(1,N)finite_sum)`;
                   `sndcart(z:real^(1,N)finite_sum)`] PDM_PERIODIZE_LOCAL) THEN
    REWRITE_TAC[pdm_periodize] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[SNDCART_PASTECART];
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `dist(z0:real^(1,N)finite_sum,z)` THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(sndcart(z:real^(1,N)finite_sum) - sndcart(z0:real^(1,N)finite_sum))` THEN
        REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM] THEN
        REWRITE_TAC[GSYM SNDCART_SUB; NORM_SNDCART]];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART;
                  FSTCART_SUB; SNDCART_SUB] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `(S:real^1->bool) PCROSS (:real^N)` THEN REWRITE_TAC[INTER_SUBSET] THEN
  SUBGOAL_THEN
   `(\z. (FF:real^(1,N)finite_sum->real^K)
           (z - pastecart (vec 0) (pdm_floorv(sndcart(z0:real^(1,N)finite_sum))))) =
    FF o (\z. z - pastecart (vec 0) (pdm_floorv(sndcart z0)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(S:real^1->bool) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                FSTCART_SUB; SNDCART_SUB; IN_UNIV; VECTOR_SUB_RZERO] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART; IN_UNIV] THEN
    SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

(* Families smooth up to the initial time: congruence, cutoff and           *)
(* periodization, affine change of the space variable.                       *)

let PDM_UPTO_CONG = prove
 (`!a b U (G:real->real^N->real^K) H.
        pde_upto a b U G /\ (!t y. a <= t /\ t < b /\ y IN U ==> H t y = G t y)
        ==> pde_upto a b U H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^K`] THEN
  ASM_SIMP_TAC[]);;

let PDM_UPTO_CUTOFF_PERIODIZE = prove
 (`!a b U (G:real->real^N->real^K) (chi:real^N->real) k aa.
        open U /\ pde_upto a b U G /\
        smooth_map_on (:real^N) (\y. lift(chi y)) /\
        compact k /\ k SUBSET U /\ (!y. ~(y IN k) ==> chi y = &0) /\
        &0 < aa /\ aa <= &1 / &2 /\ k SUBSET interval[aa % vec 1,(&1 - aa) % vec 1]
        ==> pde_upto a b (:real^N)
              (\t. pdm_periodize (\y. if y IN U then chi y % G t y else vec 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC
   `\z. (\w:real^(1,N)finite_sum. if sndcart w IN U
                                  then (chi:real^N->real)(sndcart w) %
                                       (FF:real^(1,N)finite_sum->real^K) w
                                  else vec 0)
          (pastecart (fstcart z) (pdm_frac(sndcart z)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDM_ST_PERIODIZE_SMOOTH THEN EXISTS_TAC `aa:real` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDM_ST_CUTOFF_EXT THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[OPEN_INTERVAL];
      X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(chi:real^N->real) (sndcart(z:real^(1,N)finite_sum)) = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[pdm_periodize; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let PDM_UPTO_AFFINE = prove
 (`!a b (G:real->real^N->real^K) lam d.
        pde_upto a b (:real^N) G
        ==> pde_upto a b (:real^N) (\t x. G t (lam % x + d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `(FF:real^(1,N)finite_sum->real^K) o
              (\z. pastecart (fstcart z) (lam % sndcart z + d))` THEN
  ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`interval(lift(a - e),lift b) PCROSS (:real^N)`;
                     `\x:real^(1,N)finite_sum. x`] SMOOTH_MAP_ON_FSTCART_OPEN) THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
      MP_TAC(ISPECL [`interval(lift(a - e),lift b) PCROSS (:real^N)`;
                     `\x:real^(1,N)finite_sum. x`] SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]]]);;

(* Transplants of families supported in a compact subset of the ball of     *)
(* radius lam/4 are smooth up to the initial time and Z^N-periodic.          *)

let PDM_TRANSPLANT_UPTO = prove
 (`!a b lam (G:real->real^N->real^K) k.
        &0 < lam /\ compact k /\ k SUBSET ball(vec 0,lam / &4) /\
        pde_upto a b (:real^N) G /\
        (!t z. a <= t /\ t < b /\ ~(z IN k) ==> G t z = vec 0)
        ==> pde_upto a b (:real^N) (\t. pdm_transplant lam (G t)) /\
            (!t. pde_zper (pdm_transplant lam (G t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[PDM_TRANSPLANT_ZPER] THEN
  ABBREV_TAC `c:real^N = inv(&2) % vec 1` THEN
  ABBREV_TAC `chi = \y:real^N. smooth_bump (&1 / &4) (&1 / &3) (y - c)` THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `(:real^N)`;
                 `\t x. (G:real->real^N->real^K) t (lam % x + --(lam % c))`;
                 `chi:real^N->real`; `cball(c:real^N,&1 / &3)`; `&1 / &6`]
                PDM_UPTO_CUTOFF_PERIODIZE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDM_UPTO_AFFINE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "chi" THEN
      MP_TAC(ISPECL [`\x:real^N. lift(smooth_bump (&1 / &4) (&1 / &3) x)`; `--c:real^N`]
                    PDE_SMOOTH_TRANSLATE) THEN
      REWRITE_TAC[GSYM VECTOR_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      X_GEN_TAC `y:real^N` THEN EXPAND_TAC "chi" THEN
      REWRITE_TAC[IN_CBALL; dist; REAL_NOT_LE] THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_BUMP_0 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_INTERVAL; dist] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs((c:real^N)$j - (y:real^N)$j) <= &1 / &3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(c - y:real^N)` THEN
        ASM_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM];
        ALL_TAC] THEN
      EXPAND_TAC "c" THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN MATCH_MP_TAC PDM_UPTO_CONG THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(concl th)) THEN
                          CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[pdm_transplant] THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN `lam % x + --(lam % c) = lam % (x - c:real^N)` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `norm(x - c:real^N) <= &1 / &4` THENL
   [SUBGOAL_THEN `(chi:real^N->real) x = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    EXPAND_TAC "chi" THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->real^N->real^K) t (lam % (x - c)) = vec 0`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(lam % (x - c:real^N)) IN ball(vec 0,lam / &4)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  UNDISCH_TAC `~(norm(x - c:real^N) <= &1 / &4)` THEN
  UNDISCH_TAC `&0 < lam` THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  SPEC_TAC(`norm(x - c:real^N)`,`u:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lam * &1 / &4 < lam * u` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Back from the torus (norms of x -> u(x / lam + c) on the                  *)
(* box of half-width lam/2, the preimage of the unit cube), and the          *)
(* coefficient transplants for the torus theory (cutoff and periodization  *)
(* of families of coefficients, identity outside the patch for the          *)
(* principal part).                                                          *)
(* ------------------------------------------------------------------------- *)

let PDM_UNTRANSPLANT_TERM = prove
 (`!lam (u:real^N->real^K) l.
        &1 <= lam /\ smooth_map_on (:real^N) u
        ==> drop(integral (interval[--(lam / &2) % vec 1,(lam / &2) % vec 1])
                   (\z. lift(norm(iterated_partial l
                          (\z. u(inv lam % z + inv(&2) % vec 1)) z) pow 2)))
            <= lam pow dimindex(:N) *
               drop(integral (interval[vec 0,vec 1])
                      (\x. lift(norm(iterated_partial l u x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[PDM_ITERATED_PARTIAL_AFFINE; NORM_MUL; REAL_POW_MUL; REAL_ABS_POW;
               REAL_ABS_INV; REAL_ARITH `&0 < lam ==> abs lam = lam`; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2)`;
                 `integral (interval[vec 0,vec 1])
                    (\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2))`;
                 `interval[vec 0:real^N,vec 1]`; `inv lam`; `inv(&2) % vec 1:real^N`]
                HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; PDE_SQNORM_INTEGRABLE; REAL_INV_EQ_0;
               REAL_LT_IMP_NZ; REAL_INV_INV; REAL_ABS_INV; REAL_POW_INV;
               REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY; VEC_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `~(&1 < &0)`] THEN
  SUBGOAL_THEN
   `lam % vec 0 + --(lam % inv(&2) % vec 1) = --(lam / &2) % vec 1:real^N /\
    lam % vec 1 + --(lam % inv(&2) % vec 1) = (lam / &2) % vec 1:real^N`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  MP_TAC(ISPECL [`\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2)`;
                 `interval[vec 0:real^N,vec 1]`; `inv lam`; `inv(&2) % vec 1:real^N`]
                INTEGRABLE_AFFINITY) THEN
  ASM_SIMP_TAC[PDE_SQNORM_INTEGRABLE; REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_INV_INV] THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY; VEC_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `~(&1 < &0)`] THEN
  SUBGOAL_THEN
   `lam % vec 0 + --(lam % inv(&2) % vec 1) = --(lam / &2) % vec 1:real^N /\
    lam % vec 1 + --(lam % inv(&2) % vec 1) = (lam / &2) % vec 1:real^N`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_CMUL; REAL_INV_INV] THEN
  ABBREV_TAC `I0 = drop(integral (interval[vec 0:real^N,vec 1])
                    (\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[PDE_SQNORM_INTEGRABLE; LIFT_DROP; REAL_POW_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_POW_POW] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POW_LE] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]);;

let PDM_UNTRANSPLANT_NORM = prove
 (`!lam (u:real^N->real^K) s.
        &1 <= lam /\ smooth_map_on (:real^N) u
        ==> sum (pde_index_lists s (:N))
              (\l. drop(integral (interval[--(lam / &2) % vec 1,(lam / &2) % vec 1])
                     (\z. lift(norm(iterated_partial l
                            (\z. u(inv lam % z + inv(&2) % vec 1)) z) pow 2))))
            <= lam pow dimindex(:N) * pde_hs2 s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_UNTRANSPLANT_TERM THEN ASM_REWRITE_TAC[]);;

(* Smooth Euclidean cutoffs: 1 on an open neighbourhood of a compact set,   *)
(* values in [0,1], vanishing off a compact subset of an open set.  The      *)
(* proof is that of GRGE_EUCLID_CUTOFF (pc_mfd_embmetric, not in this load   *)
(* closure), keeping the open set where the cutoff is 1.                     *)

let PDM_OPEN_SET_CHART_INV = prove
 (`!(U:real^K->bool) y. y IN U ==> chart_inv (U,(\x:real^K. x)) y = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_inv; FST; SND] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

let PDM_EUCLID_CUTOFF = prove
 (`!k w:real^K->bool.
        compact k /\ open w /\ k SUBSET w
        ==> ?psi V L. smooth_map_on (:real^K) (\z. lift(psi z)) /\
                      (!z. &0 <= psi z /\ psi z <= &1) /\
                      open V /\ k SUBSET V /\ (!z. z IN V ==> psi z = &1) /\
                      compact L /\ L SUBSET w /\
                      (!z. ~(z IN L) ==> psi z = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^K)topology`; `open_set_atlas (:real^K)`;
                 `k:real^K->bool`; `w:real^K->bool`] MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; COMPACT_IN_EUCLIDEAN; GSYM OPEN_IN] THEN
    MP_TAC(ISPEC `(:real^K)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `V:real^K->bool`
    (X_CHOOSE_THEN `L:real^K->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`psi:real^K->real`; `V:real^K->bool`; `L:real^K->bool`] THEN
  ASM_REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth (open_set_atlas (:real^K)) (\x. lift((psi:real^K->real) x))`
       THEN
    REWRITE_TAC[mfd_smooth; open_set_atlas; IN_SING; FORALL_UNWIND_THM2; FST; SND;
                IMAGE_ID] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(\x. lift((psi:real^K->real) x)) o chart_inv((:real^K),(\x:real^K. x))` THEN
    ASM_SIMP_TAC[OPEN_UNIV; o_THM; PDM_OPEN_SET_CHART_INV; IN_UNIV];
    ASM_REWRITE_TAC[OPEN_IN];
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_DIFF; IN_UNIV]]);;

(* Families: subtracting a constant, cutoff with zero extension. *)

let PDM_UPTO_SUB_CONST = prove
 (`!a b U (G:real->real^N->real^K) c.
        open U /\ pde_upto a b U G ==> pde_upto a b U (\t y. G t y - c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum. (FF:real^(1,N)finite_sum->real^K) z - c` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; OPEN_PCROSS; OPEN_INTERVAL; ETA_AX]);;

let PDM_UPTO_CUTOFF_EXT = prove
 (`!a b U (G:real->real^N->real^K) (chi:real^N->real) k.
        open U /\ pde_upto a b U G /\
        smooth_map_on (:real^N) (\y. lift(chi y)) /\
        compact k /\ k SUBSET U /\ (!y. ~(y IN k) ==> chi y = &0)
        ==> pde_upto a b (:real^N) (\t y. if y IN U then chi y % G t y else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum. if sndcart w IN U
                                       then (chi:real^N->real)(sndcart w) %
                                            (FF:real^(1,N)finite_sum->real^K) w
                                       else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDM_ST_CUTOFF_EXT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL];
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* Cutoff and transplant of a family of coefficients given near a compact   *)
(* patch k: smooth up to the initial time, periodic, and equal to the       *)
(* family on an open neighbourhood of k (in the coordinates z = lam (x - c)). *)

let PDM_CUTOFF_TRANSPLANT_FAMILY = prove
 (`!a b lam (G:real->real^N->real^K) U k.
        &0 < lam /\ open U /\ compact k /\ k SUBSET U /\ k SUBSET ball(vec 0,lam / &4) /\
        pde_upto a b U G
        ==> ?chi V. (!z. &0 <= chi z /\ chi z <= &1) /\ open V /\ k SUBSET V /\ V SUBSET U /\
                    pde_upto a b (:real^N)
                      (\t. pdm_transplant lam (\z. if z IN U then chi z % G t z else vec 0)) /\
                    (!t. pde_zper
                           (pdm_transplant lam (\z. if z IN U then chi z % G t z else vec 0))) /\
                    (!t z. a <= t /\ t < b /\ z IN V
                           ==> pdm_transplant lam (\z. if z IN U then chi z % G t z else vec 0)
                                 (inv lam % z + inv(&2) % vec 1) = G t z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(U:real^N->bool) INTER ball(vec 0,lam / &4)`]
                PDM_EUCLID_CUTOFF) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; SUBSET_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `V:real^N->bool`
    (X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `chi:real^N->real` THEN
  EXISTS_TAC `(V:real^N->bool) INTER U INTER ball(vec 0,lam / &4)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; PDM_TRANSPLANT_ZPER] THEN
  SUBGOAL_THEN
   `!t z. ~(z IN L) ==> (if z IN U then (chi:real^N->real) z % (G:real->real^N->real^K) t z
                         else vec 0) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    SET_TAC[];
    MP_TAC(ISPECL [`a:real`; `b:real`; `lam:real`;
                   `\t z. if z IN U then (chi:real^N->real) z % (G:real->real^N->real^K) t z
                          else vec 0`; `L:real^N->bool`] PDM_TRANSPLANT_UPTO) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC PDM_UPTO_CUTOFF_EXT THEN EXISTS_TAC `L:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`lam:real`;
                   `\z. if z IN U then (chi:real^N->real) z % (G:real->real^N->real^K) t z
                        else vec 0`;
                   `inv lam % z + inv(&2) % vec 1:real^N`] PDM_TRANSPLANT_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(y:real^N) IN ball(vec 0,lam / &4)` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs(inv lam * (z:real^N)$j) < &1 / &4` MP_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(z:real^N)` THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
        UNDISCH_TAC `(z:real^N) IN ball(vec 0,lam / &4)` THEN
        REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `(a % z + c) - c:real^N = a % z`; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; VECTOR_MUL_LID]]]);;

let PDM_COEFF_TRANSPLANT_LOWER = prove
 (`!a b lam (G:real->real^N->real^K) U k.
        &0 < lam /\ open U /\ compact k /\ k SUBSET U /\ k SUBSET ball(vec 0,lam / &4) /\
        pde_upto a b U G
        ==> ?H. pde_upto a b (:real^N) H /\ (!t. pde_zper (H t)) /\
                ?V. open V /\ k SUBSET V /\
                    !t z. a <= t /\ t < b /\ z IN V
                          ==> H t (inv lam % z + inv(&2) % vec 1) = G t z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PDM_CUTOFF_TRANSPLANT_FAMILY) THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `V:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\t. pdm_transplant lam
                    (\z. if z IN U then (chi:real^N->real) z % (G:real->real^N->real^K) t z
                         else vec 0)` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* Convex combinations of a symmetric elliptic matrix with the identity.     *)

let PDM_MIX_ELLIPTIC = prove
 (`!c lam0 (A:real^N^N).
        &0 <= c /\ c <= &1 /\ &0 < lam0 /\ transp A = A /\
        (!v. lam0 * norm v pow 2 <= v dot (A ** v))
        ==> transp(mat 1 + c %% (A - mat 1)) = mat 1 + c %% (A - mat 1) /\
            !v. min lam0 (&1) * norm v pow 2 <= v dot ((mat 1 + c %% (A - mat 1)) ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MATRIX_SUB; TRANSP_MAT];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
              MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID;
              DOT_RADD; DOT_RMUL; DOT_RSUB; GSYM NORM_POW_2] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
  ABBREV_TAC `X = (v:real^N) dot ((A:real^N^N) ** v)` THEN
  ABBREV_TAC `Y = norm(v:real^N) pow 2` THEN
  SUBGOAL_THEN `&0 <= Y` MP_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `lam0 <= &1` THENL
   [ASM_SIMP_TAC[REAL_ARITH `l <= &1 ==> min l (&1) = l`] THEN
    SUBGOAL_THEN `c * (lam0 * Y - Y) <= c * (X - Y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - lam0) * (&1 - c) * Y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(l <= &1) ==> min l (&1) = &1`; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 <= c * (X - Y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `Y <= lam0 * Y` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* The principal coefficient: identity plus the cut-off transplant of        *)
(* AA - I; symmetric, elliptic with constant min(lam0,1), periodic, equal to *)
(* AA near the patch.                                                        *)

let PDM_COEFF_TRANSPLANT_PRINCIPAL = prove
 (`!a b lam lam0 (AA:real->real^N->real^N^N) U k.
        &0 < lam /\ &0 < lam0 /\ open U /\ compact k /\ k SUBSET U /\
        k SUBSET ball(vec 0,lam / &4) /\
        pde_upto a b U (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (AA t z)) /\
        (!t z. a <= t /\ t < b /\ z IN U
               ==> transp(AA t z) = AA t z /\ !v. lam0 * norm v pow 2 <= v dot (AA t z ** v))
        ==> ?BB. pde_upto a b (:real^N)
                   (\t x. (vectorize:real^N^N->real^(N,N)finite_prod) (BB t x)) /\
                 (!t. pde_zper (BB t)) /\
                 (!t x. a <= t /\ t < b
                        ==> transp(BB t x) = BB t x /\
                            !v. min lam0 (&1) * norm v pow 2 <= v dot (BB t x ** v)) /\
                 ?V. open V /\ k SUBSET V /\
                     !t z. a <= t /\ t < b /\ z IN V
                           ==> BB t (inv lam % z + inv(&2) % vec 1) = AA t z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `lam:real`;
                 `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((AA:real->real^N->real^N^N) t z) -
                        (vectorize:real^N^N->real^(N,N)finite_prod) (mat 1)`;
                 `U:real^N->bool`; `k:real^N->bool`] PDM_CUTOFF_TRANSPLANT_FAMILY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                   `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                            ((AA:real->real^N->real^N^N) t z)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) (mat 1)`]
                  PDM_UPTO_SUB_CONST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `V:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `H = \t. pdm_transplant lam
              (\z. if z IN U
                   then (chi:real^N->real) z %
                        ((vectorize:real^N^N->real^(N,N)finite_prod)
                           ((AA:real->real^N->real^N^N) t z) -
                         (vectorize:real^N^N->real^(N,N)finite_prod) (mat 1))
                   else vec 0)` THEN
  SUBGOAL_THEN
   `!t (x:real^N). a <= t /\ t < b
          ==> (matrify:real^(N,N)finite_prod->real^N^N)
                ((H:real->real^N->real^(N,N)finite_prod) t x) = mat 0 \/
              ?z. z IN U /\ matrify(H t x) = chi z %% ((AA:real->real^N->real^N^N) t z - mat 1)`
  (LABEL_TAC "Hform") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[pdm_transplant; pdm_periodize] THEN
    COND_CASES_TAC THENL
     [DISJ2_TAC THEN
      EXISTS_TAC `lam % (pdm_frac (x:real^N) - inv(&2) % vec 1)` THEN
      ASM_REWRITE_TAC[MATRIFY_CMUL; MATRIFY_SUB; MATRIFY_VECTORIZE];
      DISJ1_TAC THEN
      REWRITE_TAC[CART_EQ; MATRIFY_COMPONENT; LAMBDA_BETA] THEN
      SIMP_TAC[matrify; LAMBDA_BETA; VEC_COMPONENT; MAT_COMPONENT] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\t (x:real^N). mat 1 + (matrify:real^(N,N)finite_prod->real^N^N)
                                    ((H:real->real^N->real^(N,N)finite_prod) t x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDM_UPTO_CONG THEN
    EXISTS_TAC `\t y. (H:real->real^N->real^(N,N)finite_prod) t y -
                      --((vectorize:real^N^N->real^(N,N)finite_prod) (mat 1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDM_UPTO_SUB_CONST THEN REWRITE_TAC[OPEN_UNIV] THEN
      EXPAND_TAC "H" THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_MATRIFY] THEN
      VECTOR_ARITH_TAC];
    X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`(H:real->real^N->real^(N,N)finite_prod) (t:real)`;
                         `\h. mat 1 + (matrify:real^(N,N)finite_prod->real^N^N) h`]
                        PDE_ZPER_COMPOSE)) THEN
    EXPAND_TAC "H" THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^N`] THEN STRIP_TAC THEN
    USE_THEN "Hform" (fun th -> MP_TAC(MP (SPECL [`t:real`; `x:real^N`] th)
                                          (CONJ (ASSUME `a <= t`) (ASSUME `t < b`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[MATRIX_ADD_RID; TRANSP_MAT; MATRIX_VECTOR_MUL_LID; GSYM NORM_POW_2] THEN
      GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC PDM_MIX_ELLIPTIC THEN ASM_SIMP_TAC[]];
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "H" THEN ASM_SIMP_TAC[MATRIFY_SUB; MATRIFY_VECTORIZE] THEN
    MATRIX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tensor fields defined by a chart representative W in a                    *)
(* chart c (pdm_chart_field): values, representatives in every chart        *)
(* (pullbacks of W by the transition maps), and smoothness when W has       *)
(* compact support in the chart image.                                       *)
(* ------------------------------------------------------------------------- *)

let pdm_chart_field = new_definition
 `pdm_chart_field (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
                  (W:real^N->real^N^N) (x:A) =
    if x IN FST c
    then mpullback (chart_trans (chart_at atlas x) c) W (SND(chart_at atlas x) x)
    else mat 0`;;

(* Pair-free forms of the chart facts at a point. *)

let PDM_CHART_AT_C = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> x IN topspace top /\ chart_at atlas x IN atlas /\ x IN FST(chart_at atlas x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[CHART_AT]]);;

let PDM_CHART_TRANS_AT_C = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> chart_trans c c' (SND c x) = SND c' x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `x:A`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[PAIR]);;

let PDM_CHART_JAC_CHAIN_C = prove
 (`!top atlas (c1:(A->bool)#(A->real^N)) c2 c3 x.
        smooth_manifold_atlas top atlas /\ c1 IN atlas /\ c2 IN atlas /\ c3 IN atlas /\
        x IN FST c1 /\ x IN FST c2 /\ x IN FST c3
        ==> matrix(chart_jac c1 c3 x) =
            matrix(chart_jac c2 c3 x) ** matrix(chart_jac c1 c2 x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                 `FST(c2:(A->bool)#(A->real^N))`; `SND(c2:(A->bool)#(A->real^N))`;
                 `FST(c3:(A->bool)#(A->real^N))`; `SND(c3:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MATRIX_COMPOSE THEN CONJ_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[PAIR] (ISPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`; `x:A`]
    CHART_JAC_LINEAR)) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]);;

let PDM_CHART_FIELD_AT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) W x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> pdm_chart_field atlas c W x =
            transp(matrix(chart_jac (chart_at atlas x) c x)) ** W(SND c x) **
            matrix(chart_jac (chart_at atlas x) c x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pdm_chart_field; mpullback; chart_jac] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_TRANS_AT_C) THEN
  ASM_SIMP_TAC[]);;

(* The representative in any chart c' is the pullback of W by the           *)
(* transition from c' to c on the overlap image.                             *)

let PDM_CHART_FIELD_LOCAL = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' W z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        z IN IMAGE (SND c') (FST c' INTER FST c)
        ==> metric_local atlas c' (pdm_chart_field atlas c W) z =
            mpullback (chart_trans c' c) W z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[metric_local; PDM_CHART_FIELD_AT] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (chart_trans (c':(A->bool)#(A->real^N)) c) (at (SND c' x)) =
                chart_jac c' c (x:A)` SUBST1_TAC THENL
   [REWRITE_TAC[chart_jac]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_JAC_CHAIN_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `W:real^N->real^N^N`; `x:A`]
                PDM_CHART_FIELD_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let PDM_CHART_FIELD_SELF = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) W z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ z IN IMAGE (SND c) (FST c)
        ==> metric_local atlas c (pdm_chart_field atlas c W) z = W z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                 `W:real^N->real^N^N`; `z:real^N`] PDM_CHART_FIELD_LOCAL) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (chart_trans (c:(A->bool)#(A->real^N)) c) (at (SND c x)) =
                chart_jac c c (x:A)` SUBST1_TAC THENL
   [REWRITE_TAC[chart_jac]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let PDM_CHART_FIELD_OFF = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' W x.
        smooth_manifold_atlas top atlas /\ c' IN atlas /\ x IN FST c' /\ ~(x IN FST c)
        ==> metric_local atlas c' (pdm_chart_field atlas c W) (SND c' x) = mat 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_SIMP_TAC[metric_local; pdm_chart_field; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]);;

(* Fields from compactly supported smooth representatives are smooth.        *)

let PDM_CHART_FIELD_SMOOTH = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W:real^N->real^N^N) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
        compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
        smooth_map_on (IMAGE (SND c) (FST c))
          ((vectorize:real^N^N->real^(N,N)finite_prod) o W) /\
        (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN K) ==> W z = mat 0)
        ==> pde_tensor_smooth atlas (pdm_chart_field atlas c W)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_tensor_smooth] THEN
  X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kc = {x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN K}` THEN
  SUBGOAL_THEN `closed_in top (Kc:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `K:real^N->bool`] MFDC_CHART_COMPACT) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z0:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `chart_inv (c':(A->bool)#(A->real^N)) z0 IN FST(c:(A->bool)#(A->real^N))` THENL
   [EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' INTER FST(c:(A->bool)#(A->real^N)))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c':(A->bool)#(A->real^N)) z0` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o
                mpullback (chart_trans (c':(A->bool)#(A->real^N)) c) W` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDM_CHART_FIELD_LOCAL THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PDM_MPULLBACK_SMOOTH THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                    PDM_CHART_TRANS_AT_C) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' DIFF (Kc:A->bool))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF] THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c':(A->bool)#(A->real^N)) z0` THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "Kc" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z:real^N. vec 0:real^(N,N)finite_prod` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; FORALL_IN_IMAGE; IN_DIFF; o_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `W:real^N->real^N^N`; `x:A`] PDM_CHART_FIELD_OFF) THEN
    ASM_SIMP_TAC[VECTORIZE_0]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `W:real^N->real^N^N`; `SND(c':(A->bool)#(A->real^N)) x`]
                PDM_CHART_FIELD_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(W:real^N->real^N^N) (SND(c:(A->bool)#(A->real^N)) (x:A)) = mat 0`
    (fun th -> REWRITE_TAC[th; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; VECTORIZE_0]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~((x:A) IN Kc)` THEN EXPAND_TAC "Kc" THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Integrals over compact sets and changes of variables: the                 *)
(* integrals of squared jets of forms over a compact set are bounded by the *)
(* integrals of the squared jets of g over the image (PDM_CV_JET_INTEGRAL).  *)
(* ------------------------------------------------------------------------- *)

(* (sum a)^2 <= |s| sum a^2. *)

let PDM_SUM_SQUARE_LE = prove
 (`!s (a:A->real). FINITE s ==> (sum s a) pow 2 <= &(CARD s) * sum s (\i. a i pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\i:A. sum s (\j. (a i * a i + a j * a j) / &2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `(a:A->real) i - a j` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN
     `!i:A. sum s (\j. (a i * a i + a j * a j) / &2) =
            (&(CARD(s:A->bool)) * (a i * a i) + sum s (\j. a j * a j)) / &2`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN ASM_SIMP_TAC[real_div; SUM_RMUL; SUM_ADD; SUM_CONST]; ALL_TAC] THEN
    ASM_SIMP_TAC[real_div; SUM_RMUL; SUM_ADD; SUM_CONST; SUM_LMUL] THEN
    ABBREV_TAC `AA = sum s (\i:A. a i * a i)` THEN REAL_ARITH_TAC]);;

(* Continuous maps are absolutely integrable on compact sets. *)

let PDM_INTEGRABLE_CONTINUOUS_COMPACT = prove
 (`!(f:real^M->real^N) k.
        f continuous_on k /\ compact k
        ==> f absolutely_integrable_on k /\ f integrable_on k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SUBGOAL_THEN `bounded (IMAGE (f:real^M->real^N) k)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift B` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]);;

(* The Jacobian determinant of a smooth map is bounded away from 0 on       *)
(* compact subsets where it does not vanish.                                 *)

let PDM_DET_LOWER_COMPACT = prove
 (`!s0 (tau:real^N->real^N) k.
        open s0 /\ smooth_map_on s0 tau /\
        (!z. z IN s0 ==> ~(det(matrix(frechet_derivative tau (at z))) = &0)) /\
        compact k /\ k SUBSET s0
        ==> ?d. &0 < d /\
                !z. z IN k ==> d <= abs(det(matrix(frechet_derivative tau (at z))))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. abs(det(matrix(frechet_derivative (tau:real^N->real^N) (at z))))`;
                 `k:real^N->bool`] CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`] LRG_SMOOTH_JACOBIAN) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs(det(matrix(frechet_derivative (tau:real^N->real^N) (at z0))))` THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* Change of variables, as an inequality for nonnegative integrands. *)

let PDM_CV_INTEGRAL_LE = prove
 (`!s0 (tau:real^N->real^N) k d (h:real^N->real^1).
        open s0 /\ smooth_map_on s0 tau /\
        (!x y. x IN s0 /\ y IN s0 /\ tau x = tau y ==> x = y) /\
        compact k /\ k SUBSET s0 /\ &0 < d /\
        (!z. z IN k ==> d <= abs(det(matrix(frechet_derivative tau (at z))))) /\
        h continuous_on (IMAGE tau k) /\ (!y. y IN IMAGE tau k ==> &0 <= drop(h y))
        ==> drop(integral k (\z. h(tau z))) <= inv d * drop(integral (IMAGE tau k) h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(tau:real^N->real^N) continuous_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (tau:real^N->real^N) k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN k ==> ((tau:real^N->real^N) has_derivative frechet_derivative tau (at z))
                   (at z within k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN k /\ y IN k /\ (tau:real^N->real^N) x = tau y ==> x = y`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^1`; `tau:real^N->real^N`;
                 `\z. frechet_derivative (tau:real^N->real^N) (at z)`; `k:real^N->bool`]
                INTEGRAL_CHANGE_OF_VARIABLES) THEN
  MP_TAC(ISPECL [`h:real^N->real^1`; `tau:real^N->real^N`;
                 `\z. frechet_derivative (tau:real^N->real^N) (at z)`; `k:real^N->bool`]
                ABSOLUTELY_INTEGRABLE_CHANGE_OF_VARIABLES) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; PDM_INTEGRABLE_CONTINUOUS_COMPACT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral k
                (\z. inv d % (abs(det(matrix(frechet_derivative (tau:real^N->real^N) (at z)))) %
                              (h:real^N->real^1)(tau z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\z. (h:real^N->real^1)((tau:real^N->real^N) z)) continuous_on k`
      MP_TAC THENL
       [SUBGOAL_THEN `(\z. (h:real^N->real^1)((tau:real^N->real^N) z)) = h o tau`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[PDM_INTEGRABLE_CONTINUOUS_COMPACT]];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_MUL_LID];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]]);;

(* Integrals of finite sums of real-valued integrands. *)

let PDM_INTEGRAL_SUM_DROP = prove
 (`!(f:A->real^N->real) s k.
        FINITE s /\ (!a. a IN s ==> (\x. lift(f a x)) integrable_on k)
        ==> (\x. lift(sum s (\a. f a x))) integrable_on k /\
            drop(integral k (\x. lift(sum s (\a. f a x)))) =
            sum s (\a. drop(integral k (\x. lift(f a x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\a:A. \x:real^N. lift(f a x)`; `k:real^N->bool`; `s:A->bool`]
                  INTEGRABLE_VSUM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\a:A. \x:real^N. lift(f a x)`; `k:real^N->bool`; `s:A->bool`]
                  INTEGRAL_VSUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_VSUM; o_DEF]]);;

(* The core: squared jets of forms integrated over a compact set are bounded *)
(* by the squared jets of g integrated over the image.                       *)

let PDM_CV_JET_INTEGRAL = prove
 (`!s0 t0 (tau:real^N->real^N) k (c:num->real^N->real^Q).
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        (!x y. x IN s0 /\ y IN s0 /\ tau x = tau y ==> x = y) /\
        (!z. z IN s0 ==> ~(det(matrix(frechet_derivative tau (at z))) = &0)) /\
        compact k /\ k SUBSET s0 /\ (!q. smooth_map_on s0 (c q))
        ==> !n. ?C. &0 <= C /\
                !(g:real^N->real^P) l.
                    smooth_map_on t0 g /\ LENGTH l = n /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                    ==> drop(integral k
                          (\z. lift(norm(iterated_partial l
                                 (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y)) z)
                                 pow 2)))
                        <= C * sum (pde_index_lists n (:N))
                                 (\l'. drop(integral (IMAGE tau k)
                                         (\y. lift(norm(iterated_partial l' g y) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^N->bool`; `tau:real^N->real^N`;
                 `k:real^N->bool`] PDM_COMPOSE_JET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPECL [`n:num`; `c:num->real^N->real^Q`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "jet"))) THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`; `k:real^N->bool`]
                PDM_DET_LOWER_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C0 pow 2 * &(CARD(pde_index_lists n (:N))) * inv d` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^P`; `l:num list`] THEN STRIP_TAC THEN
  ABBREV_TAC `CC = C0 pow 2 * &(CARD(pde_index_lists n (:N)))` THEN
  SUBGOAL_THEN `&0 <= CC` ASSUME_TAC THENL
   [EXPAND_TAC "CC" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^N->real^N) continuous_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l':num list. (\y. lift(norm(iterated_partial l' (g:real^N->real^P) y) pow 2))
                  continuous_on IMAGE (tau:real^N->real^N) k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `t0:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l':num list.
      (\z. lift(norm(iterated_partial l' (g:real^N->real^P) ((tau:real^N->real^N) z)) pow 2))
      integrable_on k`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\z. lift(norm(iterated_partial l' (g:real^N->real^P) ((tau:real^N->real^N) z)) pow 2)) =
      (\y. lift(norm(iterated_partial l' g y) pow 2)) o tau`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(\y. lift(norm(iterated_partial l' (g:real^N->real^P) y) pow 2)) o
                    (tau:real^N->real^N)`; `k:real^N->bool`]
                  PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s0
      (\y. vsum(1..dimindex(:P))
             (\q. ((g:real^N->real^P)((tau:real^N->real^N) y))$q %
                  (c:num->real^N->real^Q) q y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_FORM_SMOOTH THEN EXISTS_TAC `t0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral k
      (\z. lift(CC * sum (pde_index_lists n (:N))
                     (\l'. norm(iterated_partial l' (g:real^N->real^P)
                                 ((tau:real^N->real^N) z)) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\z. lift(norm(iterated_partial l
                (\y. vsum(1..dimindex(:P))
                       (\q. ((g:real^N->real^P)((tau:real^N->real^N) y))$q %
                            (c:num->real^N->real^Q) q y)) z) pow 2)`;
        `k:real^N->bool`] PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
        SIMP_TAC[]];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MP_TAC(ISPECL
       [`\l' z. norm(iterated_partial l' (g:real^N->real^P) ((tau:real^N->real^N) z)) pow 2`;
        `pde_index_lists n (:N)`; `k:real^N->bool`] PDM_INTEGRAL_SUM_DROP) THEN
      ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN SIMP_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      EXPAND_TAC "CC" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(C0 * pde_jetn n (g:real^N->real^P) ((tau:real^N->real^N) z)) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        USE_THEN "jet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_LE_POW_2; pde_jetn] THEN
        MP_TAC(ISPECL [`pde_index_lists n (:N)`;
                       `\l'. norm(iterated_partial l' (g:real^N->real^P)
                                    ((tau:real^N->real^N) z))`] PDM_SUM_SQUARE_LE) THEN
        REWRITE_TAC[PDE_INDEX_LISTS_FINITE]]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  MP_TAC(ISPECL
   [`\l' z. norm(iterated_partial l' (g:real^N->real^P) ((tau:real^N->real^N) z)) pow 2`;
    `pde_index_lists n (:N)`; `k:real^N->bool`] PDM_INTEGRAL_SUM_DROP) THEN
  ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
  EXPAND_TAC "CC" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l':num list` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`; `k:real^N->bool`; `d:real`;
                 `\y. lift(norm(iterated_partial l' (g:real^N->real^P) y) pow 2)`]
                PDM_CV_INTEGRAL_LE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Transition maps as changes of variables (injective, with                  *)
(* invertible derivative), restriction of chart integrals to compact        *)
(* supports, and squared norms of finite sums.                               *)
(* ------------------------------------------------------------------------- *)

let PDM_CHART_TRANS_INJ = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' z1 z2.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        z1 IN IMAGE (SND c) (FST c INTER FST c') /\
        z2 IN IMAGE (SND c) (FST c INTER FST c') /\
        chart_trans c c' z1 = chart_trans c c' z2
        ==> z1 = z2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`] THEN
  ASM_REWRITE_TAC[PAIR] THEN
  UNDISCH_TAC `chart_trans (c:(A->bool)#(A->real^N)) c' z1 = chart_trans c c' z2` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_SIMP_TAC[]);;

let PDM_CHART_TRANS_DET = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        z IN IMAGE (SND c) (FST c INTER FST c')
        ==> ~(det(matrix(frechet_derivative (chart_trans c c') (at z))) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_REWRITE_TAC[GSYM chart_jac] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_JAC_CHAIN_C) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID] THEN DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
  REWRITE_TAC[DET_I; DET_MUL] THEN
  ASM_CASES_TAC `det(matrix(chart_jac (c:(A->bool)#(A->real^N)) c' (x:A))) = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

(* Chart integrals of squared partials of maps vanishing off a compact set. *)

let PDM_SQNORM_INTEGRAL_RESTRICT = prove
 (`!s k (w:real^M->real^N) l.
        open s /\ compact k /\ k SUBSET s /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0)
        ==> integral s (\y. lift(norm(iterated_partial l w y) pow 2)) =
            integral k (\y. lift(norm(iterated_partial l w y) pow 2))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  ASM_CASES_TAC `(y:real^M) IN k` THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `iterated_partial l (w:real^M->real^N) y = vec 0`
    (fun th -> REWRITE_TAC[th; NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
               REWRITE_TAC[LIFT_NUM]) THEN
  MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `k:real^M->bool`] THEN ASM_REWRITE_TAC[]);;

(* Squared norms of finite sums. *)

let PDM_NORM_VSUM_SQ_LE = prove
 (`!s (f:A->real^N).
        FINITE s ==> norm(vsum s f) pow 2 <= &(CARD s) * sum s (\i. norm(f i) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sum s (\i:A. norm((f:A->real^N) i))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC VSUM_NORM THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:A->bool`; `\i:A. norm((f:A->real^N) i)`] PDM_SUM_SQUARE_LE) THEN
    ASM_REWRITE_TAC[]]);;

(* Smooth real functions on a manifold: products. *)

let PDM_MFD_SMOOTH_MUL = prove
 (`!top atlas (f:A->real) g.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas (\x. lift(f x)) /\ mfd_smooth atlas (\x. lift(g x))
        ==> mfd_smooth atlas (\x. lift(f x * g x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x:A. lift(f x * g x)) o chart_inv (c:(A->bool)#(A->real^N)) =
    (\z. lift(drop(((\x. lift(f x)) o chart_inv c) z) *
              drop(((\x. lift(g x)) o chart_inv c) z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* Chart images of compact subsets of a chart domain are compact. *)

let PDM_CHART_IMAGE_COMPACT = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) k.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ compact_in top k /\ k SUBSET FST c
        ==> compact(IMAGE (SND c) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology top (FST(c:(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o CONJUNCT2 o CONJUNCT2) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX]);;

(* The main estimate for pieces: a cutoff rho with compact support Kr in    *)
(* the overlap of charts a and b, times the pullback to chart a of a matrix *)
(* map G on chart b: the chart-a integrals of its squared jets are bounded  *)
(* by those of G over the chart-b image of Kr.                               *)

let PDM_PULLBACK_PIECE_BOUND = prove
 (`!top atlas (a:(A->bool)#(A->real^N)) b (rho:A->real) Kr n.
        smooth_manifold_atlas top atlas /\ a IN atlas /\ b IN atlas /\
        mfd_smooth atlas (\x. lift(rho x)) /\ compact_in top Kr /\
        Kr SUBSET FST a INTER FST b /\ (!x. ~(rho x = &0) ==> x IN Kr)
        ==> ?C. &0 <= C /\
                !(G:real^N->real^N^N) l.
                   smooth_map_on (IMAGE (SND b) (FST b))
                     ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                   LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                   ==> drop(integral (IMAGE (SND a) (FST a))
                          (\z. lift(norm(iterated_partial l
                                 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                      (rho(chart_inv a z) %% mpullback (chart_trans a b) G z))
                                 z) pow 2)))
                       <= C * sum (pde_index_lists n (:N))
                                (\l'. drop(integral (IMAGE (SND b) Kr)
                                        (\y. lift(norm(iterated_partial l'
                                               ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                               y) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a INTER FST(b:(A->bool)#(A->real^N)))` THEN
  ABBREV_TAC `tau = chart_trans (a:(A->bool)#(A->real^N)) b` THEN
  ABBREV_TAC `Kc = IMAGE (SND(a:(A->bool)#(A->real^N))) Kr` THEN
  SUBGOAL_THEN `open(S:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(Kc:real^N->bool) /\ Kc SUBSET S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (S:real^N->bool) (tau:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "tau" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(a:(A->bool)#(A->real^N))`; `SND(a:(A->bool)#(A->real^N))`;
                   `FST(b:(A->bool)#(A->real^N))`; `SND(b:(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN FST(a:(A->bool)#(A->real^N)) /\ x IN FST(b:(A->bool)#(A->real^N))
          ==> (tau:real^N->real^N) (SND a x) = SND b x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tau" THEN MATCH_MP_TAC PDM_CHART_TRANS_AT_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (tau:real^N->real^N) S SUBSET IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (tau:real^N->real^N) Kc = IMAGE (SND(b:(A->bool)#(A->real^N))) Kr`
  ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `cq = \q z. (rho:A->real) (chart_inv (a:(A->bool)#(A->real^N)) z) %
               (vectorize:real^N^N->real^(N,N)finite_prod)
                 (transp(matrix(frechet_derivative (tau:real^N->real^N) (at z))) **
                  (matrify(basis q):real^N^N) **
                  matrix(frechet_derivative tau (at z)))` THEN
  SUBGOAL_THEN `!q. smooth_map_on (S:real^N->bool) ((cq:num->real^N->real^(N,N)finite_prod) q)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "cq" THEN
    SUBGOAL_THEN
     `(\z. (rho:A->real) (chart_inv (a:(A->bool)#(A->real^N)) z) %
           (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix(frechet_derivative (tau:real^N->real^N) (at z))) **
              (matrify(basis q):real^N^N) **
              matrix(frechet_derivative tau (at z)))) =
      (\z. drop(((\x. lift(rho x)) o chart_inv a) z) %
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix(frechet_derivative (tau:real^N->real^N) (at z))) **
              (matrify(basis q):real^N^N) **
              matrix(frechet_derivative tau (at z)))) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)` THEN CONJ_TAC THENL
       [EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((rho:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC PDM_PULLBACK_COEFF_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                 `tau:real^N->real^N`; `Kc:real^N->bool`;
                 `cq:num->real^N->real^(N,N)finite_prod`]
                (INST_TYPE [`:(N,N)finite_prod`,`:P`] PDM_CV_JET_INTEGRAL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z1:real^N`; `z2:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC PDM_CHART_TRANS_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `a:(A->bool)#(A->real^N)`; `b:(A->bool)#(A->real^N)`] THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "tau" THEN
      MATCH_MP_TAC PDM_CHART_TRANS_DET THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cv"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `l:num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
          ((rho:A->real) (chart_inv (a:(A->bool)#(A->real^N)) z) %%
           mpullback (tau:real^N->real^N) G z)) =
    (\y. vsum(1..dimindex(:(N,N)finite_prod))
          (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o G) (tau y))$q %
               (cq:num->real^N->real^(N,N)finite_prod) q y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[VECTORIZE_CMUL; PDM_MPULLBACK_FORM] THEN EXPAND_TAC "cq" THEN
    SIMP_TAC[GSYM VSUM_LMUL; FINITE_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a) /\ ~(z IN Kc)
        ==> vsum(1..dimindex(:(N,N)finite_prod))
              (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o G) ((tau:real^N->real^N) z))$q %
                   (cq:num->real^N->real^(N,N)finite_prod) q z) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN EXPAND_TAC "cq" THEN
    SUBGOAL_THEN `(rho:A->real) (chart_inv (a:(A->bool)#(A->real^N)) z) = &0`
      (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VSUM_0]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (a:(A->bool)#(A->real^N)) z IN Kr` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((z:real^N) IN Kc)` THEN EXPAND_TAC "Kc" THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `chart_inv (a:(A->bool)#(A->real^N)) z` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`; `Kc:real^N->bool`;
                 `\y. vsum(1..dimindex(:(N,N)finite_prod))
                       (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                               ((tau:real^N->real^N) y))$q %
                            (cq:num->real^N->real^(N,N)finite_prod) q y)`;
                 `l:num list`] PDM_SQNORM_INTEGRAL_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "cv" (MP_TAC o SPECL [`(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`;
                                 `l:num list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b = c ==> a <= c`) th)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The chart-wise norm of a field defined by a compactly                     *)
(* supported chart representative (PDM_CHART_FIELD_NORM) and the           *)
(* localization of the chart-wise norm to any chart (PDM_MNORM_LOCALIZE).   *)
(* ------------------------------------------------------------------------- *)

(* Integrals over compact subsets are dominated by the chart integral.       *)

let PDM_SQNORM_SUBSET_LE = prove
 (`!s k k' (w:real^N->real^K) l.
        open s /\ compact k /\ k SUBSET s /\ smooth_map_on s w /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0) /\ compact k' /\ k' SUBSET s
        ==> drop(integral k' (\y. lift(norm(iterated_partial l w y) pow 2))) <=
            drop(integral s (\y. lift(norm(iterated_partial l w y) pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y. lift(norm(iterated_partial l (w:real^N->real^K) y) pow 2)`;
                   `k':real^N->bool`] PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
    MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`; `w:real^N->real^K`; `l:num list`]
                  PDM_ZERO_EXT_INTEGRAL) THEN
    ASM_SIMP_TAC[]]);;

(* In any chart a, a cutoff times the field of a compactly supported chart  *)
(* representative is the cutoff times chi times the pullback of W.           *)

let PDM_CHART_FIELD_CUTOFF_EQ = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) a (W:real^N->real^N^N) K (chi:A->real) L
    (psi:A->real) z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ a IN atlas /\
        (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN K) ==> W z = mat 0) /\
        (!x. x IN FST c /\ SND c x IN K ==> chi x = &1) /\
        L SUBSET FST c /\ (!x. x IN topspace top DIFF L ==> chi x = &0) /\
        z IN IMAGE (SND a) (FST a)
        ==> psi(chart_inv a z) %% metric_local atlas a (pdm_chart_field atlas c W) z =
            (psi(chart_inv a z) * chi(chart_inv a z)) %% mpullback (chart_trans a c) W z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (a:(A->bool)#(A->real^N)) z` THEN
  SUBGOAL_THEN `(x:A) IN FST(a:(A->bool)#(A->real^N)) /\ SND a x = z` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `a:(A->bool)#(A->real^N)`;
                   `W:real^N->real^N^N`; `z:real^N`] PDM_CHART_FIELD_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_CASES_TAC `SND(c:(A->bool)#(A->real^N)) (x:A) IN K` THENL
     [ASM_SIMP_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    SUBGOAL_THEN `mpullback (chart_trans (a:(A->bool)#(A->real^N)) c) (W:real^N->real^N^N) z =
                  mat 0` (fun th -> REWRITE_TAC[th; MATRIX_CMUL_RZERO]) THEN
    REWRITE_TAC[mpullback] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                  PDM_CHART_TRANS_AT_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(W:real^N->real^N^N) (SND(c:(A->bool)#(A->real^N)) x) = mat 0`
      (fun th -> REWRITE_TAC[th; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `a:(A->bool)#(A->real^N)`;
                 `W:real^N->real^N^N`; `x:A`] PDM_CHART_FIELD_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(chi:A->real) x = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO; MATRIX_CMUL_LZERO; MATRIX_CMUL_RZERO]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* The chart-wise norm of the field of a compactly supported representative *)
(* W in a chart c is bounded by the chart-c norm of W.                      *)

let PDM_CHART_FIELD_NORM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (c:(A->bool)#(A->real^N)) K s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c)
        ==> ?C. !W:real^N->real^N^N.
                  smooth_map_on (IMAGE (SND c) (FST c))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o W) /\
                  (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN K) ==> W z = mat 0)
                  ==> pde_tensor_smooth atlas (pdm_chart_field atlas c W) /\
                      pde_mnorm2 atlas n0 cs psi s (pdm_chart_field atlas c W) <=
                      C * sum (pde_index_lists s (:N))
                            (\l. drop(integral (IMAGE (SND c) (FST c))
                                   (\y. lift(norm(iterated_partial l
                                          ((vectorize:real^N^N->real^(N,N)finite_prod) o W) y)
                                          pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kc = {x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN K}` THEN
  SUBGOAL_THEN `compact_in top (Kc:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `K:real^N->bool`] MFDC_CHART_COMPACT) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Kc:A->bool`; `FST(c:(A->bool)#(A->real^N))`] MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `V:A->bool`
    (X_CHOOSE_THEN `L:A->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!j. ?C. j < n0
            ==> !n. &0 <= C n /\
                    !(G:real^N->real^N^N) l.
                      smooth_map_on (IMAGE (SND c) (FST c))
                        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                      LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                      ==> drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j))
                                                   (FST(cs j)))
                             (\z. lift(norm(iterated_partial l
                                    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                         (((\x. (psi:num->A->real) j x * (chi:A->real) x))
                                            (chart_inv (cs j) z) %%
                                          mpullback (chart_trans (cs j) c) G z)) z) pow 2)))
                          <= C n * sum (pde_index_lists n (:N))
                                    (\l'. drop(integral
                                            (IMAGE (SND c)
                                               ({x | x IN FST(cs j) /\ SND(cs j) x IN ks j}
                                                INTER L))
                                            (\y. lift(norm(iterated_partial l'
                                                   ((vectorize:real^N^N->real^(N,N)finite_prod)
                                                    o G) y) pow 2))))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`; `c:(A->bool)#(A->real^N)`;
                   `\x. (psi:num->A->real) j x * (chi:A->real) x`;
                   `{x | x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\
                         SND(cs j) x IN (ks:num->real^N->bool) j} INTER (L:A->bool)`;
                   `n:num`] PDM_PULLBACK_PIECE_BOUND) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN
     `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\
      compact((ks:num->real^N->bool) j) /\ ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
      mfd_smooth atlas (\x. lift((psi:num->A->real) j x))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[pde_cover]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[pde_cover]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[pde_cover]; ASM_MESON_TAC[pde_cutoffs]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_INV_C) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((cs:num->(A->bool)#(A->real^N)) j)`;
                     `SND((cs:num->(A->bool)#(A->real^N)) j)`;
                     `(ks:num->real^N->bool) j`] MFDC_CHART_COMPACT) THEN
      ASM_REWRITE_TAC[PAIR];
      ASM SET_TAC[];
      X_GEN_TAC `x:A` THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) j))
                                   ((ks:num->real^N->bool) j)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:num->num->real` (LABEL_TAC "piece")) THEN
  EXISTS_TAC `sum {j:num | j < n0}
                (\j. sum (pde_index_lists s (:N)) (\l. (CC:num->num->real) j (LENGTH l)))` THEN
  X_GEN_TAC `W:real^N->real^N^N` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDM_CHART_FIELD_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `K:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `TT = sum (pde_index_lists s (:N))
          (\l. drop(integral (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (\y. lift(norm(iterated_partial l
                        ((vectorize:real^N^N->real^(N,N)finite_prod) o (W:real^N->real^N^N)) y)
                        pow 2))))` THEN
  REWRITE_TAC[pde_mnorm2; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(l:num list) <= s /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists s (:N)` THEN
    SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) j IN atlas`
  ASSUME_TAC THENL [ASM_MESON_TAC[pde_cover]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
      (\y. lift(norm(iterated_partial l
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  ((psi:num->A->real) j (chart_inv (cs j) z) %%
                   metric_local atlas (cs j) (pdm_chart_field atlas c (W:real^N->real^N^N)) z))
             y) pow 2)) =
    integral (IMAGE (SND(cs j)) (FST(cs j)))
      (\y. lift(norm(iterated_partial l
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  ((psi j (chart_inv (cs j) z) * (chi:A->real) (chart_inv (cs j) z)) %%
                   mpullback (chart_trans (cs j) c) W z)) y) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC PDM_CHART_FIELD_CUTOFF_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `K:real^N->bool`; `L:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(Kc:A->bool) SUBSET V` THEN EXPAND_TAC "Kc" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "piece" (fun th -> MP_TAC(SPEC `LENGTH(l:num list)`
                               (MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`W:real^N->real^N^N`; `l:num list`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b <= c ==> a <= c`) th)) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "TT" THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\ ~(y IN K)
        ==> ((vectorize:real^N^N->real^(N,N)finite_prod) o (W:real^N->real^N^N)) y = vec 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[o_THM; VECTORIZE_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `compact(IMAGE (SND(c:(A->bool)#(A->real^N)))
              ({x | x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\
                    SND(cs j) x IN (ks:num->real^N->bool) j} INTER L)) /\
    IMAGE (SND c) ({x | x IN FST(cs j) /\ SND(cs j) x IN ks j} INTER L) SUBSET
    IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC COMPACT_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST((cs:num->(A->bool)#(A->real^N)) j)`;
                   `SND((cs:num->(A->bool)#(A->real^N)) j)`;
                   `(ks:num->real^N->bool) j`] MFDC_CHART_COMPACT) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[pde_cover];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists (LENGTH(l:num list)) (:N))
      (\l'. drop(integral (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
              (\y. lift(norm(iterated_partial l'
                     ((vectorize:real^N^N->real^(N,N)finite_prod) o (W:real^N->real^N^N)) y)
                     pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l':num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDM_SQNORM_SUBSET_LE THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO] THEN
    X_GEN_TAC `l':num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `K:real^N->bool`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o (W:real^N->real^N^N)`;
                   `l':num list`] PDM_ZERO_EXT_INTEGRAL) THEN
    ASM_SIMP_TAC[]]);;

(* The pieces rho (pullback of G) are smooth on the chart image and vanish  *)
(* off the chart image of the support Kr.                                    *)

let PDM_PULLBACK_PIECE_SMOOTH = prove
 (`!top atlas (a:(A->bool)#(A->real^N)) b (rho:A->real) Kr (G:real^N->real^N^N).
        smooth_manifold_atlas top atlas /\ a IN atlas /\ b IN atlas /\
        mfd_smooth atlas (\x. lift(rho x)) /\ compact_in top Kr /\
        Kr SUBSET FST a INTER FST b /\ (!x. ~(rho x = &0) ==> x IN Kr) /\
        smooth_map_on (IMAGE (SND b) (FST b))
          ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
        ==> smooth_map_on (IMAGE (SND a) (FST a))
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (rho(chart_inv a z) %% mpullback (chart_trans a b) G z)) /\
            (!z. z IN IMAGE (SND a) (FST a) /\ ~(z IN IMAGE (SND a) Kr)
                 ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                       (rho(chart_inv a z) %% mpullback (chart_trans a b) G z) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a) /\ ~(z IN IMAGE (SND a) Kr)
        ==> (vectorize:real^N^N->real^(N,N)finite_prod)
              ((rho:A->real) (chart_inv a z) %%
               mpullback (chart_trans a (b:(A->bool)#(A->real^N))) G z) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rho:A->real) (chart_inv (a:(A->bool)#(A->real^N)) z) = &0`
      (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LZERO; VECTORIZE_0]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((z:real^N) IN IMAGE (SND(a:(A->bool)#(A->real^N))) Kr)` THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `chart_inv (a:(A->bool)#(A->real^N)) z` THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `compact(IMAGE (SND(a:(A->bool)#(A->real^N))) Kr)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z0:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(z0:real^N) IN IMAGE (SND(a:(A->bool)#(A->real^N))) Kr` THENL
   [ALL_TAC;
    EXISTS_TAC `IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a) DIFF IMAGE (SND a) Kr` THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^N. vec 0:real^(N,N)finite_prod` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF] THEN ASM_MESON_TAC[]] THEN
  EXISTS_TAC `IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a INTER FST(b:(A->bool)#(A->real^N)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    UNDISCH_TAC `(z0:real^N) IN IMAGE (SND(a:(A->bool)#(A->real^N))) Kr` THEN
    UNDISCH_TAC `(Kr:A->bool) SUBSET FST(a:(A->bool)#(A->real^N)) INTER FST(b:(A->bool)#(A->real^N))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\y. vsum(1..dimindex(:(N,N)finite_prod))
          (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                 (chart_trans (a:(A->bool)#(A->real^N)) b y))$q %
               ((rho:A->real)(chart_inv a y) %
                (vectorize:real^N^N->real^(N,N)finite_prod)
                  (transp(matrix(frechet_derivative (chart_trans a b) (at y))) **
                   (matrify(basis q):real^N^N) **
                   matrix(frechet_derivative (chart_trans a b) (at y)))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[VECTORIZE_CMUL; PDM_MPULLBACK_FORM] THEN
    SIMP_TAC[GSYM VSUM_LMUL; FINITE_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a INTER FST(b:(A->bool)#(A->real^N)))`;
                 `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                 `chart_trans (a:(A->bool)#(A->real^N)) b`;
                 `\q y. (rho:A->real)(chart_inv (a:(A->bool)#(A->real^N)) y) %
                        (vectorize:real^N^N->real^(N,N)finite_prod)
                          (transp(matrix(frechet_derivative (chart_trans a b) (at y))) **
                           (matrify(basis q):real^N^N) **
                           matrix(frechet_derivative (chart_trans a (b:(A->bool)#(A->real^N))) (at y)))`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`]
                PDM_FORM_SMOOTH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a INTER FST(b:(A->bool)#(A->real^N))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a INTER FST(b:(A->bool)#(A->real^N))))
                  (chart_trans a b)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(a:(A->bool)#(A->real^N))`; `SND(a:(A->bool)#(A->real^N))`;
                   `FST(b:(A->bool)#(A->real^N))`; `SND(b:(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:(A->bool)#(A->real^N)`; `b:(A->bool)#(A->real^N)`; `x:A`]
                  PDM_CHART_TRANS_AT_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `q:num` THEN
    SUBGOAL_THEN
     `(\y. (rho:A->real)(chart_inv (a:(A->bool)#(A->real^N)) y) %
           (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix(frechet_derivative (chart_trans a (b:(A->bool)#(A->real^N))) (at y))) **
              (matrify(basis q):real^N^N) **
              matrix(frechet_derivative (chart_trans a b) (at y)))) =
      (\y. drop(((\x. lift(rho x)) o chart_inv a) y) %
           (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix(frechet_derivative (chart_trans a b) (at y))) **
              (matrify(basis q):real^N^N) **
              matrix(frechet_derivative (chart_trans a b) (at y)))) y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((rho:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC PDM_PULLBACK_COEFF_SMOOTH THEN ASM_REWRITE_TAC[]]]);;

(* Decomposition of a localized field by a partition of unity subordinate   *)
(* to the cutoffs: in chart c, theta v is the sum of the pullbacks of the   *)
(* chart pieces psi_j v of the cover.                                        *)

let PDM_LOCALIZE_DECOMP = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) n0 cs (psi:num->A->real) (phi:num->A->real)
    (theta:A->real) (v:A->real^N^N) z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        (!j. j < n0 ==> cs j IN atlas) /\
        (!x. x IN topspace top ==> sum {j | j < n0} (\j. phi j x) = &1) /\
        (!j x. j < n0 /\ ~(phi j x = &0) ==> x IN FST(cs j) /\ psi j x = &1) /\
        z IN IMAGE (SND c) (FST c)
        ==> (vectorize:real^N^N->real^(N,N)finite_prod)
              (theta(chart_inv c z) %% metric_local atlas c v z) =
            vsum {j | j < n0}
              (\j. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((theta(chart_inv c z) * phi j (chart_inv c z)) %%
                      mpullback (chart_trans c (cs j))
                        (\y. (matrify:real^(N,N)finite_prod->real^N^N)
                               ((vectorize:real^N^N->real^(N,N)finite_prod)
                                  (psi j (chart_inv (cs j) y) %%
                                   metric_local atlas (cs j) v y))) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) z` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = z /\ x IN topspace top`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "x" THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTORIZE_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_MUL_RID] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
                            [GSYM(MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`))]) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM VSUM_RMUL] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[VECTORIZE_CMUL] THEN
  ASM_CASES_TAC `(phi:num->A->real) j x = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) j) /\ (psi:num->A->real) j x = &1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) j IN atlas` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) j`;
                 `v:A->real^N^N`; `z:real^N`] PDM_METRIC_LOCAL_TRANS_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE] THEN
  UNDISCH_TAC `SND(c:(A->bool)#(A->real^N)) (x:A) = z` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) j`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_INV_C) THEN
  ASM_SIMP_TAC[MATRIX_CMUL_LID]);;

(* Chart integrals of squared partials of finite sums of compactly          *)
(* supported smooth maps.                                                    *)

let PDM_SQNORM_INTEGRAL_VSUM_LE = prove
 (`!s (R:B->real^N->real^K) (k:B->real^N->bool) J l.
        open s /\ FINITE J /\
        (!j. j IN J ==> smooth_map_on s (R j) /\ compact(k j) /\ k j SUBSET s /\
                        !y. y IN s /\ ~(y IN k j) ==> R j y = vec 0)
        ==> drop(integral s
                  (\y. lift(norm(iterated_partial l (\z. vsum J (\j. R j z)) y) pow 2)))
            <= &(CARD J) *
               sum J (\j. drop(integral s
                                (\y. lift(norm(iterated_partial l (R j) y) pow 2))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j IN J ==> (\y. lift(norm(iterated_partial l ((R:B->real^N->real^K) j) y) pow 2))
                   integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(k:B->real^N->bool) j`; `(R:B->real^N->real^K) j`;
                   `l:num list`] PDM_ZERO_EXT_INTEGRAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN s ==> iterated_partial l (\z. vsum J (\j. (R:B->real^N->real^K) j z)) y =
                   vsum J (\j. iterated_partial l (R j) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_ITERATED_PARTIAL_VSUM_OPEN THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\y. lift(norm(iterated_partial l (\z. vsum J (\j. (R:B->real^N->real^K) j z)) y)
                        pow 2)) =
    integral s (\y. lift(norm(vsum J (\j. iterated_partial l (R j) y)) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\j y. norm(iterated_partial l ((R:B->real^N->real^K) j) y) pow 2`;
                 `J:B->bool`; `s:real^N->bool`] PDM_INTEGRAL_SUM_DROP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\y. lift(&(CARD(J:B->bool)) *
                   sum J (\j. norm(iterated_partial l ((R:B->real^N->real^K) j) y) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\y. lift(norm(iterated_partial l
                        (\z. vsum J (\j. (R:B->real^N->real^K) j z)) y) pow 2)` THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `UNIONS (IMAGE (k:B->real^N->bool) J)`;
                     `\z. vsum J (\j. (R:B->real^N->real^K) j z)`; `l:num list`]
                    PDM_ZERO_EXT_INTEGRAL) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_SIMP_TAC[COMPACT_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE; UNIONS_SUBSET] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `j:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((y:real^N) IN (k:B->real^N->bool) j)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((y:real^N) IN UNIONS (IMAGE (k:B->real^N->bool) J))` THEN
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC PDM_NORM_VSUM_SQ_LE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]]);;

(* Localization of the chart-wise norm to any chart: for a cutoff theta     *)
(* supported in the chart image of a compact K in the chart c, the chart-c  *)
(* norm of theta v is bounded by pde_mnorm2.                                *)

let PDM_MNORM_LOCALIZE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (c:(A->bool)#(A->real^N)) (theta:A->real) K s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        c IN atlas /\ mfd_smooth atlas (\x. lift(theta x)) /\
        compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
        (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) K)
        ==> ?C. !(v:A->real^N^N).
                  pde_tensor_smooth atlas v
                  ==> sum (pde_index_lists s (:N))
                        (\l. drop(integral (IMAGE (SND c) (FST c))
                               (\y. lift(norm(iterated_partial l
                                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                           (theta (chart_inv c z) %%
                                            metric_local atlas c v z)) y) pow 2))))
                      <= C * pde_mnorm2 atlas n0 cs psi s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  (* the partition of unity *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `psi:num->A->real`] PDM_CUTOFF_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->A->real` (CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM])
    (LABEL_TAC "sum1"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num->A->bool` (X_CHOOSE_THEN `V:num->A->bool`
    (LABEL_TAC "phi"))) THEN
  ABBREV_TAC `Kth = {x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN K}` THEN
  SUBGOAL_THEN `compact_in top (Kth:A->bool) /\ IMAGE (chart_inv (c:(A->bool)#(A->real^N))) K = Kth`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kth" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `K:real^N->bool`] MFDC_CHART_COMPACT) THEN
      ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC PDE_CHART_BALL_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j x. j < n0 /\ x IN (V:num->A->bool) j
          ==> x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\ (psi:num->A->real) j x = &1`
  (LABEL_TAC "inV") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "phi" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(psi:num->A->real) j x = &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) j))
                                 ((ks:num->real^N->bool) j)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> can (term_match [] `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                                                  ==> P i x`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\
                  (ks:num->real^N->bool) j SUBSET IMAGE (SND(cs j)) (FST(cs j))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pde_cover]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j x. j < n0 /\ ~((phi:num->A->real) j x = &0) ==> x IN (L:num->A->bool) j`
  (LABEL_TAC "inL") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "phi" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n0 ==> (cs:num->(A->bool)#(A->real^N)) j IN atlas /\
                   compact((ks:num->real^N->bool) j) /\
                   ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
                   mfd_smooth atlas (\x. lift((psi:num->A->real) j x)) /\
                   mfd_smooth atlas (\x. lift((phi:num->A->real) j x)) /\
                   compact_in top ((L:num->A->bool) j) /\
                   L j SUBSET FST(cs j)`
  (LABEL_TAC "facts") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "phi" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[pde_cover]; ASM_MESON_TAC[pde_cover]; ASM_MESON_TAC[pde_cover];
      ASM_MESON_TAC[pde_cutoffs];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "inV" (MP_TAC o SPECL [`j:num`; `x:A`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the piece bounds for the charts of the cover *)
  SUBGOAL_THEN
   `!j. ?C. j < n0
            ==> !n. &0 <= C n /\
                    !(G:real^N->real^N^N) l.
                      smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
                        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                      LENGTH l = n /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                      ==> drop(integral (IMAGE (SND c) (FST c))
                             (\z. lift(norm(iterated_partial l
                                    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                         (((theta:A->real) (chart_inv c z) *
                                           (phi:num->A->real) j (chart_inv c z)) %%
                                          mpullback (chart_trans c (cs j)) G z)) z) pow 2)))
                          <= C n * sum (pde_index_lists n (:N))
                                    (\l'. drop(integral
                                            (IMAGE (SND(cs j)) (Kth INTER (L:num->A->bool) j))
                                            (\y. lift(norm(iterated_partial l'
                                                   ((vectorize:real^N^N->real^(N,N)finite_prod)
                                                    o G) y) pow 2))))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "facts" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) j`;
                   `\x. (theta:A->real) x * (phi:num->A->real) j x`;
                   `(Kth:A->bool) INTER (L:num->A->bool) j`; `n:num`]
                  PDM_PULLBACK_PIECE_BOUND) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_INTER THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Kth" THEN ASM SET_TAC[];
      X_GEN_TAC `x:A` THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM; IN_INTER] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv (c:(A->bool)#(A->real^N))) K` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
        USE_THEN "inL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:num->num->real` (LABEL_TAC "piece")) THEN
  EXISTS_TAC `sum (pde_index_lists s (:N))
                (\l. &n0 * sum {j:num | j < n0} (\j. (CC:num->num->real) j (LENGTH l)))` THEN
  X_GEN_TAC `v:A->real^N^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(l:num list) <= s /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists s (:N)` THEN
    SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kth:A->bool) SUBSET FST(c:(A->bool)#(A->real^N))` (LABEL_TAC "KthC") THENL
   [UNDISCH_TAC `{x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN K} = Kth` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the chart pieces of v and their pullbacks *)
  SUBGOAL_THEN
   `!j. j < n0
        ==> smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
              (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((psi:num->A->real) j (chart_inv (cs j) y) %%
                      metric_local atlas (cs j) (v:A->real^N^N) y)) /\
            (!y. y IN IMAGE (SND(cs j)) (FST(cs j)) /\ ~(y IN (ks:num->real^N->bool) j)
                 ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                       (psi j (chart_inv (cs j) y) %% metric_local atlas (cs j) v y) = vec 0)`
  (LABEL_TAC "wj") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "facts" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MATCH_MP_TAC PDM_CHART_PIECE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                            ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                           ((ks:num->real^N->bool) i)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `R = \j z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (((theta:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z) *
                  (phi:num->A->real) j (chart_inv c z)) %%
                 mpullback (chart_trans c ((cs:num->(A->bool)#(A->real^N)) j))
                   (\y. (matrify:real^(N,N)finite_prod->real^N^N)
                          ((vectorize:real^N^N->real^(N,N)finite_prod)
                             ((psi:num->A->real) j (chart_inv (cs j) y) %%
                              metric_local atlas (cs j) (v:A->real^N^N) y))) z)` THEN
  SUBGOAL_THEN
   `!j. j < n0
        ==> smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
              ((R:num->real^N->real^(N,N)finite_prod) j) /\
            compact (IMAGE (SND c) ((Kth:A->bool) INTER (L:num->A->bool) j)) /\
            IMAGE (SND c) (Kth INTER L j) SUBSET IMAGE (SND c) (FST c) /\
            (!y. y IN IMAGE (SND c) (FST c) /\ ~(y IN IMAGE (SND c) (Kth INTER L j))
                 ==> R j y = vec 0)`
  (LABEL_TAC "Rj") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "facts" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    USE_THEN "wj" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) j`;
                   `\x. (theta:A->real) x * (phi:num->A->real) j x`;
                   `(Kth:A->bool) INTER (L:num->A->bool) j`;
                   `\y. (matrify:real^(N,N)finite_prod->real^N^N)
                          ((vectorize:real^N^N->real^(N,N)finite_prod)
                             ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) y) %%
                              metric_local atlas (cs j) (v:A->real^N^N) y))`]
                  PDM_PULLBACK_PIECE_SMOOTH) THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_IN_INTER THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(L:num->A->bool) j SUBSET FST((cs:num->(A->bool)#(A->real^N)) j)` THEN
        USE_THEN "KthC" MP_TAC THEN SET_TAC[];
        X_GEN_TAC `x:A` THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM; IN_INTER] THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv (c:(A->bool)#(A->real^N))) K` MP_TAC THENL
           [MATCH_MP_TAC(ASSUME `!x:A. ~((theta:A->real) x = &0)
                                       ==> x IN IMAGE (chart_inv (c:(A->bool)#(A->real^N))) K`) THEN
            ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[]];
          USE_THEN "inL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[COMPACT_IN_INTER] THEN USE_THEN "KthC" MP_TAC THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN USE_THEN "KthC" MP_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the decomposition of the integrand *)
  SUBGOAL_THEN
   `!j x. j < n0 /\ ~((phi:num->A->real) j x = &0)
          ==> x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\ (psi:num->A->real) j x = &1`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "inV" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "phi" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    STRIP_TAC THEN
    MP_TAC(ASSUME `(L:num->A->bool) j SUBSET (V:num->A->bool) j`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "inL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (IMAGE (SND c) (FST c))
      (\y. lift(norm(iterated_partial l
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  ((theta:A->real) (chart_inv (c:(A->bool)#(A->real^N)) z) %%
                   metric_local atlas c (v:A->real^N^N) z)) y) pow 2)) =
    integral (IMAGE (SND c) (FST c))
      (\y. lift(norm(iterated_partial l
             (\z. vsum {j:num | j < n0}
                    (\j. (R:num->real^N->real^(N,N)finite_prod) j z)) y) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDM_LOCALIZE_DECOMP THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "facts" (fun th ->
      REWRITE_TAC[CONJUNCT1(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))]);
    ALL_TAC] THEN
  (* the sum of the pieces *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {j:num | j < n0}) *
              sum {j:num | j < n0}
                (\j. drop(integral (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                       (\y. lift(norm(iterated_partial l
                              ((R:num->real^N->real^(N,N)finite_prod) j) y) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDM_SQNORM_INTEGRAL_VSUM_LE THEN
    EXISTS_TAC `\j. IMAGE (SND(c:(A->bool)#(A->real^N)))
                          ((Kth:A->bool) INTER (L:num->A->bool) j)` THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "Rj" (fun th -> REWRITE_TAC[MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`)]);
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG_LT; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  (* one piece *)
  USE_THEN "facts" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
  USE_THEN "wj" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j))
                   ((Kth:A->bool) INTER (L:num->A->bool) j)) /\
    IMAGE (SND(cs j)) (Kth INTER L j) SUBSET IMAGE (SND(cs j)) (FST(cs j))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PDM_CHART_IMAGE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[COMPACT_IN_INTER] THEN
      UNDISCH_TAC `(L:num->A->bool) j SUBSET FST((cs:num->(A->bool)#(A->real^N)) j)` THEN
      SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `(L:num->A->bool) j SUBSET FST((cs:num->(A->bool)#(A->real^N)) j)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "piece" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
  DISCH_THEN(MP_TAC o SPEC `LENGTH(l:num list)`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`\y. (matrify:real^(N,N)finite_prod->real^N^N)
            ((vectorize:real^N^N->real^(N,N)finite_prod)
               ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) y) %%
                metric_local atlas (cs j) (v:A->real^N^N) y))`; `l:num list`])) THEN
  REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "R" THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists (LENGTH(l:num list)) (:N))
      (\l'. drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
              (\y. lift(norm(iterated_partial l'
                     (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) j (chart_inv (cs j) z) %%
                           metric_local atlas (cs j) (v:A->real^N^N) z)) y) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l':num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PDM_SQNORM_SUBSET_LE THEN EXISTS_TAC `(ks:num->real^N->bool) j` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `v:A->real^N^N`; `s:num`] PDM_MNORM2_TERMS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* Smooth limits.  Uniform limits on an open set of smooth                   *)
(* maps whose iterated partials are uniformly Cauchy are smooth, with the   *)
(* partials converging uniformly (open-set form with jets of                *)
(* WAN_SEQ_SMOOTH_LIMIT of pc_wan_psmooth, which is stated on the whole     *)
(* space without the jets; same method: UNIFORMLY_CONVERGENT_EQ_CAUCHY,     *)
(* HAS_DERIVATIVE_SEQUENCE on balls, SMOOTH_MAP_ON_PARTIAL_FAMILY).         *)
(* Then the tools for smooth tensors on M: locality of pde_tensor_smooth,   *)
(* recovery of a tensor from its chart representative, and the smooth      *)
(* limit of a sequence Cauchy in every pde_mnorm2 s.                        *)
(* ------------------------------------------------------------------------- *)

let PDM_SEQ_SMOOTH_LIMIT = prove
 (`!s (f:num->real^M->real^K).
     open s /\ (!n. smooth_map_on s (f n)) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> !e. &0 < e
                  ==> ?N. !m n x. N <= m /\ N <= n /\ x IN s
                                  ==> norm(iterated_partial l (f m) x -
                                           iterated_partial l (f n) x) < e)
     ==> ?g. smooth_map_on s g /\
             !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
                 ==> !e. &0 < e
                         ==> ?N. !n x. N <= n /\ x IN s
                                       ==> norm(iterated_partial l (f n) x -
                                                iterated_partial l g x) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cau"))) THEN
  SUBGOAL_THEN
   `?G. !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
            ==> !e. &0 < e
                    ==> ?N. !n x. N <= n /\ x IN s
                                  ==> dist(iterated_partial l ((f:num->real^M->real^K) n) x,
                                           G l x) < e`
  (X_CHOOSE_THEN `G:(num)list->real^M->real^K` (LABEL_TAC "un")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^M. x IN s`;
                   `\n. iterated_partial l ((f:num->real^M->real^K) n)`]
                  UNIFORMLY_CONVERGENT_EQ_CAUCHY) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[dist] THEN USE_THEN "cau" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
          ==> ((\n. iterated_partial l ((f:num->real^M->real^K) n) x) -->
               (G:(num)list->real^M->real^K) l x) sequentially`
  (LABEL_TAC "pt") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "un" (fun th -> MP_TAC(SPEC `e:real` (MP (SPEC `l:(num)list` th)
      (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) l`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^M`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
          ==> ((G:(num)list->real^M->real^K) l has_derivative
               (\v. vsum(1..dimindex(:M)) (\i. v$i % G (CONS i l) x))) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^M) IN ball(x,r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`ball(x:real^M,r)`; `\n. iterated_partial l ((f:num->real^M->real^K) n)`;
      `\n (y:real^M) (v:real^M). vsum(1..dimindex(:M))
                 (\i. v$i % iterated_partial (CONS i l) ((f:num->real^M->real^K) n) y)`;
      `\(y:real^M) (v:real^M). vsum(1..dimindex(:M))
               (\i. v$i % (G:(num)list->real^M->real^K) (CONS i l) y)`]
     HAS_DERIVATIVE_SEQUENCE) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        REWRITE_TAC[iterated_partial] THEN
        MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN ASM SET_TAC[];
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(ISPECL
         [`\i N. !n (y:real^M). N <= n /\ y IN s
                  ==> dist(iterated_partial (CONS i l) ((f:num->real^M->real^K) n) y,
                           (G:(num)list->real^M->real^K) (CONS i l) y) <
                      e / (&(dimindex(:M)) + &1)`;
          `dimindex(:M)`] TEXT_FINITE_N_MAX) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MESON_TAC[LE_TRANS];
            X_GEN_TAC `i:num` THEN STRIP_TAC THEN
            SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:M)) (CONS i l)` ASSUME_TAC THENL
             [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
            USE_THEN "un" (fun th -> MP_TAC(MP (SPEC `CONS (i:num) l` th)
              (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) (CONS i l)`))) THEN
            DISCH_THEN(MP_TAC o SPEC `e / (&(dimindex(:M)) + &1)`) THEN
            ANTS_TAC THENL
             [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
              MESON_TAC[]]];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NN")) THEN EXISTS_TAC `N:num` THEN
        MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`; `h:real^M`] THEN
        REWRITE_TAC[GE] THEN STRIP_TAC THEN REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
        TRANS_TAC REAL_LE_TRANS
         `sum(1..dimindex(:M)) (\i. norm(h:real^M) * (e / (&(dimindex(:M)) + &1)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
          ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
          USE_THEN "NN" (fun th -> MP_TAC(SPECL [`n:num`; `y:real^M`]
            (MP (SPEC `i:num` th) (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:M)`))))) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[dist] THEN REAL_ARITH_TAC];
          REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
          SUBGOAL_THEN `&(dimindex(:M)) * (norm(h:real^M) * e / (&(dimindex(:M)) + &1)) =
                        (norm h * e) * (&(dimindex(:M)) / (&(dimindex(:M)) + &1))`
          SUBST1_TAC THENL
           [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
          GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `e * n = (n * e) * &1`] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE] THEN
          SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN REAL_ARITH_TAC];
        MAP_EVERY EXISTS_TAC [`x:real^M`; `(G:(num)list->real^M->real^K) l x`] THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gg:real^M->real^K` (LABEL_TAC "hd")) THEN
    SUBGOAL_THEN `!y. y IN ball(x:real^M,r) ==> (gg:real^M->real^K) y = G (l:(num)list) y`
    (LABEL_TAC "eqg") THENL
     [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. iterated_partial l ((f:num->real^M->real^K) n) y` THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
       [USE_THEN "hd" (fun th -> REWRITE_TAC[MP (SPEC `y:real^M` th)
          (ASSUME `(y:real^M) IN ball(x,r)`)]);
        USE_THEN "pt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`gg:real^M->real^K`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN USE_THEN "eqg" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`gg:real^M->real^K`;
                     `\v:real^M. vsum(1..dimindex(:M))
                            (\i. v$i % (G:(num)list->real^M->real^K) (CONS i l) x)`;
                     `x:real^M`; `ball(x:real^M,r)`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "hd" (fun th -> REWRITE_TAC[MP (SPEC `x:real^M` th)
        (ASSUME `(x:real^M) IN ball(x,r)`)])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `G:(num)list->real^M->real^K`]
                SMOOTH_MAP_ON_PARTIAL_FAMILY_ITERATED) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `G:(num)list->real^M->real^K`]
                SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN
  REWRITE_TAC[ALL] THEN DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `(G:(num)list->real^M->real^K) []` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "un" (fun th -> MP_TAC(SPEC `e:real` (MP (SPEC `l:(num)list` th)
    (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:M)) l`)))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `iterated_partial l ((G:(num)list->real^M->real^K) []) y = G l y`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`l:(num)list`; `[]:(num)list`; `y:real^M`] o
      check (fun th -> can (term_match [] `!(l:(num)list) (l':(num)list) (x:real^M).
                                         (P:(num)list->(num)list->real^M->bool) l l' x`)
                                   (concl th))) THEN
    ASM_REWRITE_TAC[ALL; APPEND_NIL];
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Limits of congruences, chart representatives and chart fields.          *)
(* ------------------------------------------------------------------------- *)

let PDM_LIM_CONGRUENCE = prove
 (`!net (f:B->real^N^N) A (J:real^N^N).
     ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (f n)) --> vectorize A) net
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (transp J ** f n ** J)) -->
          vectorize(transp J ** A ** J)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(B)net`;
                 `\a:real^(N,N)finite_prod.
                    (vectorize:real^N^N->real^(N,N)finite_prod)
                      (transp(J:real^N^N) ** matrify a ** J)`;
                 `\n. (vectorize:real^N^N->real^(N,N)finite_prod) ((f:B->real^N^N) n)`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) A`] LIM_LINEAR) THEN
  ASM_REWRITE_TAC[MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; VECTORIZE_ADD; VECTORIZE_CMUL]);;

let PDM_METRIC_LOCAL_LIM = prove
 (`!atlas (c:(A->bool)#(A->real^N)) (vv:B->A->real^N^N) v z net.
     ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (vv n (chart_inv c z))) -->
      vectorize(v (chart_inv c z))) net
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (metric_local atlas c (vv n) z)) -->
          vectorize(metric_local atlas c v z)) net`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_local] THEN
  MATCH_MP_TAC PDM_LIM_CONGRUENCE THEN ASM_REWRITE_TAC[]);;

let PDM_CHART_FIELD_METRIC_LOCAL = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> pdm_chart_field atlas c (metric_local atlas c g) x = g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `x:A`] PDM_CHART_FIELD_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let PDM_CHART_FIELD_LIM = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (vv:B->A->real^N^N)
    (Wc:real^N->real^(N,N)finite_prod) x net.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c /\
     ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas c (vv n) (SND c x))) --> Wc (SND c x)) net
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (vv n x)) -->
          vectorize(pdm_chart_field atlas c (matrify o Wc) x)) net`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (vv:B->A->real^N^N) n x =
        pdm_chart_field atlas (c:(A->bool)#(A->real^N)) (metric_local atlas c (vv n)) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDM_CHART_FIELD_METRIC_LOCAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(GEN `W:real^N->real^N^N`
    (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
             `c:(A->bool)#(A->real^N)`; `W:real^N->real^N^N`; `x:A`] PDM_CHART_FIELD_AT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC PDM_LIM_CONGRUENCE THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY]);;

(* Smoothness of tensors on M is local.                                      *)

let PDM_TENSOR_SMOOTH_LOCAL = prove
 (`!top atlas (v:A->real^N^N).
        smooth_manifold_atlas top atlas /\
        (!x. x IN topspace top
             ==> ?U u. open_in top U /\ x IN U /\ pde_tensor_smooth atlas u /\
                       !y. y IN U ==> v y = u y)
        ==> pde_tensor_smooth atlas v`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")) THEN
  REWRITE_TAC[pde_tensor_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z0:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `chart_inv (c:(A->bool)#(A->real^N)) z0`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `u:A->real^N^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER U)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) z0` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o
                metric_local atlas (c:(A->bool)#(A->real^N)) (u:A->real^N^N)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        UNDISCH_TAC `pde_tensor_smooth atlas (u:A->real^N^N)` THEN
        REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]]]);;

(* The chart piece of a difference.                                          *)

let PDM_PIECE_SUB = prove
 (`!atlas (c:(A->bool)#(A->real^N)) (f:A->real) (g:A->real^N^N) h.
     (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
            (f(chart_inv c z) %% metric_local atlas c (\x. g x - h x) z)) =
     (\z. vectorize(f(chart_inv c z) %% metric_local atlas c g z) -
          vectorize(f(chart_inv c z) %% metric_local atlas c h z))`,
  REWRITE_TAC[METRIC_LOCAL_SUB; MATRIX_CMUL_SUB_LDISTRIB; VECTORIZE_SUB]);;

(* Uniform bounds of the jets of the chart pieces by the norms.            *)

let PDM_MNORM_PIECE_SUP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi j l.
        smooth_manifold_atlas top atlas /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        j < n0 /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> ?C. &0 < C /\
                !(v:A->real^N^N) z.
                  pde_tensor_smooth atlas v /\ z IN IMAGE (SND(cs j)) (FST(cs j))
                  ==> norm(iterated_partial l
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (psi j (chart_inv (cs j) z) %%
                                   metric_local atlas (cs j) v z)) z) pow 2 <=
                      C * pde_mnorm2 atlas n0 cs psi (dimindex(:N) + LENGTH l) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
    ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
    mfd_smooth atlas (\x. lift((psi:num->A->real) j x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
    REWRITE_TAC[pde_cover; pde_cutoffs] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(ks:num->real^N->bool) j`
    (INST_TYPE [`:(N,N)finite_prod`,`:K`] PDM_SOBOLEV_COMPACT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:A->real^N^N`; `z:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`; `(psi:num->A->real) j`;
                 `v:A->real^N^N`; `(ks:num->real^N->bool) j`] PDM_CHART_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                            ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                           ((ks:num->real^N->bool) i)`) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `C * sum (pde_index_lists (dimindex(:N) + LENGTH(l:num list)) (:N))
          (\l'. drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
                  (\y. lift(norm(iterated_partial l'
                         (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              ((psi:num->A->real) j (chart_inv (cs j) z) %%
                               metric_local atlas (cs j) (v:A->real^N^N) z)) y) pow 2))))` THEN
  CONJ_TAC THENL
   [USE_THEN "sob" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `v:A->real^N^N`;
                   `dimindex(:N) + LENGTH(l:num list)`] PDM_MNORM2_TERMS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[LE_REFL]]);;

(* Integrals of squared jets bounded by the sup over the support.           *)

let PDM_SQNORM_INTEGRAL_SUP = prove
 (`!s k (w:real^M->real^K) l d.
        open s /\ compact k /\ k SUBSET s /\ smooth_map_on s w /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0) /\
        (!y. y IN s ==> norm(iterated_partial l w y) <= d)
        ==> drop(integral s (\y. lift(norm(iterated_partial l w y) pow 2))) <=
            d pow 2 * measure k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`; `w:real^M->real^K`; `l:num list`]
                PDM_SQNORM_INTEGRAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral k (\y:real^M. lift(d pow 2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y. lift(norm(iterated_partial l (w:real^M->real^K) y) pow 2)`;
                     `k:real^M->bool`] PDM_INTEGRABLE_CONTINUOUS_COMPACT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL];
      REWRITE_TAC[INTEGRABLE_ON_CONST] THEN ASM_SIMP_TAC[MEASURABLE_COMPACT];
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_COMPACT; DROP_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[REAL_MUL_SYM; REAL_LE_REFL]]);;

(* Finite sums of sequences tending to 0.                                    *)

let PDM_REALLIM_SUM_0 = prove
 (`!net (f:B->A->real) s.
        FINITE s /\ (!i. i IN s ==> ((\x. f i x) ---> &0) net)
        ==> ((\x. sum s (\i. f i x)) ---> &0) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:B->A->real`; `\i:B. &0`; `s:B->bool`] REALLIM_SUM) THEN
  ASM_REWRITE_TAC[SUM_0]);;

(* A sequence Cauchy in every norm: the chart pieces converge with all     *)
(* their jets, uniformly on the chart images, to smooth maps vanishing off  *)
(* the compact pieces.                                                       *)

let PDM_MNORM_CHART_LIMITS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (vv:num->A->real^N^N).
        smooth_manifold_atlas top atlas /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        (!n. pde_tensor_smooth atlas (vv n)) /\
        (!s e. &0 < e
               ==> ?N0. !m n. N0 <= m /\ N0 <= n
                              ==> pde_mnorm2 atlas n0 cs psi s (\x. vv m x - vv n x) < e)
        ==> ?W. !j. j < n0
                    ==> smooth_map_on (IMAGE (SND(cs j)) (FST(cs j)))
                          ((W:num->real^N->real^(N,N)finite_prod) j) /\
                        (!z. z IN IMAGE (SND(cs j)) (FST(cs j)) /\ ~(z IN ks j)
                             ==> W j z = vec 0) /\
                        !l. ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                            ==> !e. &0 < e
                                    ==> ?N. !n z. N <= n /\ z IN IMAGE (SND(cs j)) (FST(cs j))
                                                  ==> norm(iterated_partial l
                                                       (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                            (psi j (chart_inv (cs j) z) %%
                                                             metric_local atlas (cs j) (vv n) z)) z -
                                                     iterated_partial l (W j) z) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sm") (LABEL_TAC "cauchy")))))) THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
    ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
    mfd_smooth atlas (\x. lift((psi:num->A->real) j x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
    REWRITE_TAC[pde_cover; pde_cutoffs] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                 ((psi:num->A->real) j (chart_inv (cs j) z) %%
                  metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)) /\
        (!z. z IN IMAGE (SND(cs j)) (FST(cs j)) /\ ~(z IN (ks:num->real^N->bool) j)
             ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                   (psi j (chart_inv (cs j) z) %% metric_local atlas (cs j) (vv n) z) = vec 0)`
  (LABEL_TAC "wn") THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC PDM_CHART_PIECE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sm" (fun th -> REWRITE_TAC[SPEC `n:num` th]) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                            ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                           ((ks:num->real^N->bool) i)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                 `\n z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                           metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)`]
                PDM_SEQ_SMOOTH_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `j:num`; `l:num list`] PDM_MNORM_PIECE_SUP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup"))) THEN
    USE_THEN "cauchy" (MP_TAC o SPECL [`dimindex(:N) + LENGTH(l:num list)`; `e pow 2 / C`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0")) THEN EXISTS_TAC `N0:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `z:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`l:num list`; `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                           metric_local atlas (cs j) ((vv:num->A->real^N^N) m) z)`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                           metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)`]
                  TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    USE_THEN "wn" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM PDM_PIECE_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C * pde_mnorm2 atlas n0 cs psi (dimindex(:N) + LENGTH(l:num list))
                      (\x. (vv:num->A->real^N^N) m x - vv n x)` THEN
    CONJ_TAC THENL
     [USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
      MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[GSYM PDM_TENSOR_SMOOTH_EQ; ETA_AX];
      USE_THEN "N0" (fun th -> MP_TAC(MP (SPECL [`m:num`; `n:num`] th)
        (CONJ (ASSUME `N0:num <= m`) (ASSUME `N0:num <= n`)))) THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < C`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^(N,N)finite_prod` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial] THEN
  ASM_CASES_TAC `(g:real^N->real^(N,N)finite_prod) z = vec 0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `norm((g:real^N->real^(N,N)finite_prod) z)`) THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`N:num`; `z:real^N`]) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  USE_THEN "wn" (fun th -> MP_TAC(MP (SPEC `z:real^N` (CONJUNCT2(SPEC `N:num` th)))
    (CONJ (ASSUME `(z:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`)
          (ASSUME `~((z:real^N) IN (ks:num->real^N->bool) j)`)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_SUB_LZERO; NORM_NEG; REAL_LT_REFL]);;

(* Squared jet integrals of differences tending to 0 under uniform         *)
(* convergence of the jets on a common compact support.                      *)

let PDM_PIECE_INTEGRAL_LIM = prove
 (`!s k (w:num->real^N->real^K) W l.
        open s /\ compact k /\ k SUBSET s /\
        (!n. smooth_map_on s (w n)) /\ smooth_map_on s W /\
        (!n y. y IN s /\ ~(y IN k) ==> w n y = vec 0) /\
        (!y. y IN s /\ ~(y IN k) ==> W y = vec 0) /\
        (!e. &0 < e
             ==> ?N. !n y. N <= n /\ y IN s
                           ==> norm(iterated_partial l (w n) y - iterated_partial l W y) < e)
        ==> ((\n. drop(integral s
                    (\y. lift(norm(iterated_partial l (\z. w n z - W z) y) pow 2))))
             ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "un")))))))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `mk = measure(k:real^N->bool)` THEN
  SUBGOAL_THEN `&0 <= mk` ASSUME_TAC THENL
   [EXPAND_TAC "mk" THEN MATCH_MP_TAC MEASURE_POS_LE THEN ASM_SIMP_TAC[MEASURABLE_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC `d = sqrt(e / (mk + &1))` THEN
  SUBGOAL_THEN `&0 < d /\ d pow 2 = e / (mk + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "un" (fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\z. (w:num->real^N->real^K) n z - W z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN s /\ ~(y IN k) ==> (\z. (w:num->real^N->real^K) n z - W z) y = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`;
                 `\z. (w:num->real^N->real^K) n z - W z`; `l:num list`]
                PDM_ZERO_EXT_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d pow 2 * mk` THEN CONJ_TAC THENL
   [EXPAND_TAC "mk" THEN MATCH_MP_TAC PDM_SQNORM_INTEGRAL_SUP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `s:real^N->bool`; `(w:num->real^N->real^K) n`;
                   `W:real^N->real^K`] TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_ARITH `&0 <= mk ==> &0 < mk + &1`; ASSUME `&0 <= mk`; REAL_LT_LDIV_EQ;
             real_div; REAL_ARITH `(e * inv m) * k = (e * k) * inv m`] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= mk ==> &0 < mk + &1`; ASSUME `&0 <= mk`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ &0 <= e * mk ==> e * mk < e * (mk + &1)`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]]);;

(* Points where a cutoff does not vanish lie in its chart.                  *)

let PDM_SUPPORT_IN_CHART = prove
 (`!top atlas n0 cs ks (psi:num->A->real) i x.
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        i < n0 /\ ~(psi i x = &0)
        ==> x IN FST((cs:num->(A->bool)#(A->real^N)) i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
                (ks:num->real^N->bool) i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                               ((ks:num->real^N->bool) i)` MP_TAC THENL
   [MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                           ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                          ((ks:num->real^N->bool) i)`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The smooth limit: a sequence of smooth tensors Cauchy in every            *)
(* pde_mnorm2 s has a smooth limit (pointwise on M, mat 0 off M) to which it *)
(* converges in every pde_mnorm2 s.                                          *)
(* ------------------------------------------------------------------------- *)

let PDM_MNORM_LIMIT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (vv:num->A->real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        (!n. pde_tensor_smooth atlas (vv n)) /\
        (!s e. &0 < e
               ==> ?N0. !m n. N0 <= m /\ N0 <= n
                              ==> pde_mnorm2 atlas n0 cs psi s (\x. vv m x - vv n x) < e)
        ==> ?v. pde_tensor_smooth atlas v /\
                (!x. ~(x IN topspace top) ==> v x = mat 0) /\
                (!x. x IN topspace top
                     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (vv n x)) -->
                          vectorize(v x)) sequentially) /\
                (!s. ((\n. pde_mnorm2 atlas n0 cs psi s (\x. vv n x - v x)) ---> &0)
                     sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `vv:num->A->real^N^N`] PDM_MNORM_CHART_LIMITS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->real^N->real^(N,N)finite_prod` (LABEL_TAC "W")) THEN
  (* chart facts *)
  SUBGOAL_THEN
   `!j. j < n0
        ==> (cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
            ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
            mfd_smooth atlas (\x. lift((psi:num->A->real) j x)) /\
            open(IMAGE (SND(cs j)) (FST(cs j))) /\ FST(cs j) SUBSET topspace top /\
            (!x. x IN FST(cs j) ==> chart_inv (cs j) (SND(cs j) x) = x) /\
            (!z. z IN IMAGE (SND(cs j)) (FST(cs j))
                 ==> chart_inv (cs j) z IN FST(cs j) /\ SND(cs j) (chart_inv (cs j) z) = z)`
  (LABEL_TAC "cf") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
      ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
      mfd_smooth atlas (\x. lift((psi:num->A->real) j x))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
      UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
      REWRITE_TAC[pde_cover; pde_cutoffs] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the chart pieces converge pointwise *)
  SUBGOAL_THEN
   `!j z. j < n0 /\ z IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))
          ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((psi:num->A->real) j (chart_inv (cs j) z) %%
                       metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)) -->
               (W:num->real^N->real^(N,N)finite_prod) j z) sequentially`
  (LABEL_TAC "ptw") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "W" (fun th -> MP_TAC(SPEC `[]:num list`
      (CONJUNCT2(CONJUNCT2(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`)))))) THEN
    REWRITE_TAC[ALL; iterated_partial] THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `z:real^N`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the values converge where a cutoff is 1 *)
  SUBGOAL_THEN
   `!j x. j < n0 /\ x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\ (psi:num->A->real) j x = &1
          ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) ((vv:num->A->real^N^N) n x)) -->
               vectorize(pdm_chart_field atlas (cs j)
                 ((matrify:real^(N,N)finite_prod->real^N^N) o
                  (W:num->real^N->real^(N,N)finite_prod) j) x)) sequentially`
  (LABEL_TAC "cfl") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MATCH_MP_TAC PDM_CHART_FIELD_LIM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv ((cs:num->(A->bool)#(A->real^N)) j) (SND(cs j) x) = x`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "ptw" (MP_TAC o SPECL [`j:num`; `SND((cs:num->(A->bool)#(A->real^N)) j) x`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[MATRIX_CMUL_LID]];
    ALL_TAC] THEN
  (* the limit *)
  ABBREV_TAC
   `vlim = \x:A. if x IN topspace top
                 then (matrify:real^(N,N)finite_prod->real^N^N)
                        (lim sequentially
                          (\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 ((vv:num->A->real^N^N) n x)))
                 else mat 0` THEN
  SUBGOAL_THEN
   `!j x. j < n0 /\ x IN FST((cs:num->(A->bool)#(A->real^N)) j) /\ (psi:num->A->real) j x = &1
          ==> (vlim:A->real^N^N) x =
              pdm_chart_field atlas (cs j)
                ((matrify:real^(N,N)finite_prod->real^N^N) o
                 (W:num->real^N->real^(N,N)finite_prod) j) x`
  (LABEL_TAC "vq") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    EXPAND_TAC "vlim" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `FST((cs:num->(A->bool)#(A->real^N)) j) SUBSET topspace top` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cfl" (MP_TAC o SPECL [`j:num`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `lim sequentially (\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                              ((vv:num->A->real^N^N) n x)) =
      vectorize(pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
                  ((matrify:real^(N,N)finite_prod->real^N^N) o
                   (W:num->real^N->real^(N,N)finite_prod) j) x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC TENDSTO_LIM THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
      REWRITE_TAC[MATRIFY_VECTORIZE]];
    ALL_TAC] THEN
  (* every point has a neighbourhood where some cutoff is 1 *)
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?j V. j < n0 /\ open_in top V /\ x IN V /\
                  (!y. y IN V ==> (psi:num->A->real) j y = &1 /\
                                  y IN FST((cs:num->(A->bool)#(A->real^N)) j))`
  (LABEL_TAC "nb") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
    REWRITE_TAC[pde_cutoffs] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `V:A->bool`] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC PDM_SUPPORT_IN_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                          `ks:num->real^N->bool`; `psi:num->A->real`] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  (* pointwise convergence *)
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) ((vv:num->A->real^N^N) n x)) -->
             vectorize((vlim:A->real^N^N) x)) sequentially`
  (LABEL_TAC "ptv") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "nb" (fun th -> MP_TAC(MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(psi:num->A->real) j x = &1 /\ x IN FST((cs:num->(A->bool)#(A->real^N)) j)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "vq" (MP_TAC o SPECL [`j:num`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "cfl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the chart pieces of the limit are the limits of the chart pieces *)
  SUBGOAL_THEN
   `!j z. j < n0 /\ z IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))
          ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                ((psi:num->A->real) j (chart_inv (cs j) z) %%
                 metric_local atlas (cs j) (vlim:A->real^N^N) z) =
              (W:num->real^N->real^(N,N)finite_prod) j z`
  (LABEL_TAC "pv") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                       metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTORIZE_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN
      MATCH_MP_TAC PDM_METRIC_LOCAL_LIM THEN USE_THEN "ptv" MATCH_MP_TAC THEN
      UNDISCH_TAC `FST((cs:num->(A->bool)#(A->real^N)) j) SUBSET topspace top` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      USE_THEN "ptw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `vlim:A->real^N^N` THEN REPEAT CONJ_TAC THENL
   [(* smoothness *)
    MATCH_MP_TAC PDM_TENSOR_SMOOTH_LOCAL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "nb" (fun th -> MP_TAC(MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    USE_THEN "W" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
    MAP_EVERY EXISTS_TAC
     [`V:A->bool`;
      `pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) j)
         ((matrify:real^(N,N)finite_prod->real^N^N) o
          (W:num->real^N->real^(N,N)finite_prod) j)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDM_CHART_FIELD_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `(ks:num->real^N->bool) j`] THEN
      ASM_REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX] THEN
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_0];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "vq" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    (* off M *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "vlim" THEN ASM_REWRITE_TAC[];
    (* pointwise *)
    USE_THEN "ptv" ACCEPT_TAC;
    ALL_TAC] THEN
  (* convergence in every norm *)
  X_GEN_TAC `s:num` THEN REWRITE_TAC[pde_mnorm2] THEN
  MATCH_MP_TAC PDM_REALLIM_SUM_0 THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC PDM_REALLIM_SUM_0 THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l` ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists s (:N)` THEN
    SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  USE_THEN "W" (fun th -> LABEL_TAC "Wj" (MP (SPEC `j:num` th) (ASSUME `(j:num) < n0`))) THEN
  USE_THEN "Wj" (fun th -> LABEL_TAC "unl" (MP (SPEC `l:num list` (CONJUNCT2(CONJUNCT2 th)))
    (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`))) THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                 ((psi:num->A->real) j (chart_inv (cs j) z) %%
                  metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)) /\
        (!z. z IN IMAGE (SND(cs j)) (FST(cs j)) /\ ~(z IN (ks:num->real^N->bool) j)
             ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                   (psi j (chart_inv (cs j) z) %% metric_local atlas (cs j) (vv n) z) = vec 0)`
  (LABEL_TAC "wn") THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC PDM_CHART_PIECE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                            ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                           ((ks:num->real^N->bool) i)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                 `(ks:num->real^N->bool) j`;
                 `\n z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                           metric_local atlas (cs j) ((vv:num->A->real^N^N) n) z)`;
                 `(W:num->real^N->real^(N,N)finite_prod) j`; `l:num list`]
                PDM_PIECE_INTEGRAL_LIM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      USE_THEN "wn" (fun th -> REWRITE_TAC[th]);
      USE_THEN "Wj" (fun th -> REWRITE_TAC[th]);
      USE_THEN "wn" (fun th -> REWRITE_TAC[th]);
      USE_THEN "Wj" (fun th -> REWRITE_TAC[th]);
      USE_THEN "unl" ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
  EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[METRIC_LOCAL_SUB; MATRIX_CMUL_SUB_LDISTRIB; VECTORIZE_SUB; ETA_AX] THEN
  USE_THEN "pv" (fun th -> REWRITE_TAC[MP (SPECL [`j:num`; `z:real^N`] th)
    (CONJ (ASSUME `(j:num) < n0`)
          (ASSUME `(z:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`))]));;

(* ------------------------------------------------------------------------- *)
(* Families.  Continuity is local; space-time pullbacks are smooth;          *)
(* pde_tfam_from is pde_upto in every chart; chart fields of families smooth *)
(* up to time a are pde_tfam_from families.                                  *)
(* ------------------------------------------------------------------------- *)

let PDM_CONTINUOUS_ON_LOCAL = prove
 (`!(f:real^M->real^N) s.
        (!x. x IN s ==> ?u. open u /\ x IN u /\ f continuous_on (s INTER u))
        ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `x:real^M`; `s:real^M->bool`;
                 `s INTER (u:real^M->bool)`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `(f:real^M->real^N) continuous_on (s INTER u)` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* Pullbacks of space-time families of matrices along a smooth map of the   *)
(* space variable.                                                           *)

let PDM_MPULLBACK_SMOOTH_ST = prove
 (`!(i0:real^1->bool) s0 t0 (tau:real^N->real^N)
    (G:real^(1,N)finite_sum->real^(N,N)finite_prod).
        open i0 /\ open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        smooth_map_on (i0 PCROSS t0) G
        ==> smooth_map_on (i0 PCROSS s0)
              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (mpullback tau
                        (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                               (G(pastecart (fstcart w) z)))
                        (sndcart w)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PDM_MPULLBACK_FORM; o_THM; VECTORIZE_MATRIFY] THEN
  MP_TAC(ISPECL [`(i0:real^1->bool) PCROSS (s0:real^N->bool)`;
                 `(i0:real^1->bool) PCROSS (t0:real^N->bool)`;
                 `\w:real^(1,N)finite_sum. pastecart (fstcart w) ((tau:real^N->real^N) (sndcart w))`;
                 `\q (w:real^(1,N)finite_sum). (vectorize:real^N^N->real^(N,N)finite_prod)
                     (transp(matrix(frechet_derivative (tau:real^N->real^N) (at (sndcart w)))) **
                      (matrify(basis q):real^N^N) **
                      matrix(frechet_derivative tau (at (sndcart w))))`;
                 `G:real^(1,N)finite_sum->real^(N,N)finite_prod`] PDM_FORM_SMOOTH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[OPEN_PCROSS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; ETA_AX; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
      SUBGOAL_THEN `(\w:real^(1,N)finite_sum. (tau:real^N->real^N) (sndcart w)) = tau o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s0:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
        SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    X_GEN_TAC `q:num` THEN
    SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
         (transp(matrix(frechet_derivative (tau:real^N->real^N) (at (sndcart w)))) **
          (matrify(basis q):real^N^N) ** matrix(frechet_derivative tau (at (sndcart w))))) =
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
         (transp(matrix(frechet_derivative tau (at y))) **
          (matrify(basis q):real^N^N) ** matrix(frechet_derivative tau (at y)))) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; PDM_PULLBACK_COEFF_SMOOTH] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]]);;

(* pde_tfam_from is pde_upto of the chart representatives in every chart. *)

let PDM_TFAM_FROM_UPTO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) a b (v:real->A->real^N^N).
        pde_tfam_from atlas a b v <=>
        !c. c IN atlas
            ==> pde_upto a b (IMAGE (SND c) (FST c))
                  (\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c (v t) y))`,
  REWRITE_TAC[pde_tfam_from; pde_upto]);;

(* Chart fields of families: the chart fields of a family of chart         *)
(* representatives smooth up to time a and vanishing off a compact set for  *)
(* a <= t < b form a pde_tfam_from family.                                   *)

let PDM_CHART_FIELD_TFAM = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (W:real->real^N->real^N^N) K a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\
        compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
        pde_upto a b (IMAGE (SND c) (FST c))
          (\t z. (vectorize:real^N^N->real^(N,N)finite_prod) (W t z)) /\
        (!t z. a <= t /\ t < b /\ z IN IMAGE (SND c) (FST c) /\ ~(z IN K)
               ==> W t z = mat 0)
        ==> pde_tfam_from atlas a b (\t. pdm_chart_field atlas c (W t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "Wz"))))))) THEN
  REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  (* cut off the extension in space *)
  MP_TAC(ISPECL [`K:real^N->bool`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`]
                PDE_RN_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `L:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `F1 = \w:real^(1,N)finite_sum.
                     chi(sndcart w) % (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w` THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift(a - e),lift b) PCROSS
                   IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                  (F1:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN
    SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. chi(sndcart w) %
                                (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w) =
      (\w. drop(((\y. lift(chi y)) o sndcart) w) % FF w)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(sndcart w IN L) ==> (F1:real^(1,N)finite_sum->real^(N,N)finite_prod) w = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "F1" THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. a <= t /\ t < b /\ z IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
          ==> (matrify:real^(N,N)finite_prod->real^N^N)
                ((F1:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) z)) =
              (W:real->real^N->real^N^N) t z`
  (LABEL_TAC "F1W") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "F1" THEN REWRITE_TAC[SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[] THEN ASM_CASES_TAC `(z:real^N) IN K` THENL
     [ASM_SIMP_TAC[VECTOR_MUL_LID; MATRIFY_VECTORIZE];
      USE_THEN "Wz" (fun th -> REWRITE_TAC[MP (SPECL [`t:real`; `z:real^N`] th)
        (CONJ (ASSUME `a <= t`) (CONJ (ASSUME `t < b`)
          (CONJ (ASSUME `(z:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`)
                (ASSUME `~((z:real^N) IN K)`))))]) THEN
      REWRITE_TAC[VECTORIZE_0; VECTOR_MUL_RZERO; MATRIFY_0]];
    ALL_TAC] THEN
  (* the chart representatives in any chart c' *)
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[pde_upto] THEN EXISTS_TAC `e:real` THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      if chart_inv (c':(A->bool)#(A->real^N)) (sndcart w) IN FST(c:(A->bool)#(A->real^N))
      then (vectorize:real^N^N->real^(N,N)finite_prod)
             (mpullback (chart_trans c' c)
                (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                       ((F1:real^(1,N)finite_sum->real^(N,N)finite_prod)
                          (pastecart (fstcart w) z)))
                (sndcart w))
      else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `chart_inv (c':(A->bool)#(A->real^N)) y IN FST c' /\
                  SND c' (chart_inv c' y) = y` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                     `(W:real->real^N->real^N^N) t`; `y:real^N`] PDM_CHART_FIELD_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        EXISTS_TAC `chart_inv (c':(A->bool)#(A->real^N)) y` THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[mpullback] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                     `chart_inv (c':(A->bool)#(A->real^N)) y`] PDM_CHART_TRANS_AT_C) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "F1W" (fun th -> REWRITE_TAC[MP (SPECL [`t:real`;
          `SND(c:(A->bool)#(A->real^N)) (chart_inv (c':(A->bool)#(A->real^N)) y)`] th)
        (CONJ (ASSUME `a <= t`) (CONJ (ASSUME `t < b`)
          (MATCH_MP (ISPEC `SND(c:(A->bool)#(A->real^N))` FUN_IN_IMAGE)
                    (ASSUME `chart_inv (c':(A->bool)#(A->real^N)) y IN
                                          FST(c:(A->bool)#(A->real^N))`))))]);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                     `(W:real->real^N->real^N^N) t`;
                     `chart_inv (c':(A->bool)#(A->real^N)) y`] PDM_CHART_FIELD_OFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTORIZE_0]]] THEN
  (* smoothness *)
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c':(A->bool)#(A->real^N)) y0 IN FST c' /\
                SND c' (chart_inv c' y0) = y0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `chart_inv (c':(A->bool)#(A->real^N)) y0 IN FST(c:(A->bool)#(A->real^N))` THENL
   [EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' INTER FST(c:(A->bool)#(A->real^N)))` THEN
    SUBGOAL_THEN
     `open(IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' INTER FST(c:(A->bool)#(A->real^N))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c':(A->bool)#(A->real^N)) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
        (mpullback (chart_trans (c':(A->bool)#(A->real^N)) c)
           (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                  ((F1:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (fstcart w) z)))
           (sndcart w))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PDM_MPULLBACK_SMOOTH_ST THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                    PDM_CHART_TRANS_AT_C) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* away from the support *)
  ABBREV_TAC `Lc = {x:A | x IN FST(c:(A->bool)#(A->real^N)) /\ SND c x IN L}` THEN
  SUBGOAL_THEN `closed_in top (Lc:A->bool) /\ Lc SUBSET FST(c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Lc" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `L:real^N->bool`] MFDC_CHART_COMPACT) THEN
      ASM_REWRITE_TAC[PAIR];
      EXPAND_TAC "Lc" THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
              IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' DIFF (Lc:A->bool))` THEN
  SUBGOAL_THEN `open(IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c' DIFF (Lc:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c':(A->bool)#(A->real^N)) y0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Lc:A->bool) SUBSET FST(c:(A->bool)#(A->real^N))` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum. vec 0:real^(N,N)finite_prod` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(F1:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (pastecart t (SND(c:(A->bool)#(A->real^N)) (x:A))) = vec 0`
    (fun th -> REWRITE_TAC[th; MATRIFY_0; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; VECTORIZE_0]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SNDCART_PASTECART] THEN
  UNDISCH_TAC `~((x:A) IN Lc)` THEN EXPAND_TAC "Lc" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* pde_upto is local in space (via the classical characterization and      *)
(* PDE_SEELEY).                                                              *)
(* ------------------------------------------------------------------------- *)

let PDM_APPROACH_SEQ = prove
 (`!a b. a < b
         ==> (!n. a < a + (b - a) * inv(&n + &2) /\ a + (b - a) * inv(&n + &2) < b) /\
             ((\n. lift(a + (b - a) * inv(&n + &2))) --> lift a) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> a < a + x`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < b - a ==> a + x < b`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    GEN_REWRITE_TAC LAND_CONV
      [GSYM(INST [`b - a:real`,`c:real`] (INST_TYPE [`:1`,`:N`] VECTOR_MUL_RZERO))] THEN
    MATCH_MP_TAC LIM_CMUL THEN REWRITE_TAC[SEQ_HARMONIC_OFFSET]]);;

let PDM_UPTO_LOCAL = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ a < b /\
        (!y. y IN U ==> ?V. open V /\ y IN V /\ V SUBSET U /\ pde_upto a b V u)
        ==> pde_upto a b U u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> ?V. open V /\ y IN V /\ V SUBSET U /\
                (\w. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)) continuous_on
                  {pastecart (lift t) z | a <= t /\ t < b /\ z IN V} /\
                pde_upto_classical a b V u`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^N` th) (ASSUME `(y:real^N) IN U`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_UPTO_IMP_CLASSICAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`] PDM_APPROACH_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dn") (LABEL_TAC "dlim")) THEN
  MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[pde_upto_classical] THEN
  REPEAT CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC PDM_CONTINUOUS_ON_LOCAL THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
    STRIP_TAC THEN USE_THEN "cl" (fun th -> MP_TAC(MP (SPEC `y:real^N` th) (ASSUME `(y:real^N) IN U`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(:real^1) PCROSS (V:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{pastecart (lift t) z | a <= t /\ t < b /\ (z:real^N) IN V}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real` (X_CHOOSE_THEN `z':real^N`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t':real`; `z':real^N`] THEN ASM_REWRITE_TAC[];
    (* smoothness *)
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "cl" (fun th -> MP_TAC(MP (SPEC `y:real^N` th) (ASSUME `(y:real^N) IN U`))) THEN
    REWRITE_TAC[pde_upto_classical] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (V:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS];
    (* the jets have continuous extensions *)
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    EXISTS_TAC
     `\w:real^(1,N)finite_sum.
        if a < drop(fstcart w)
        then iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z)) w
        else lim sequentially
               (\n. iterated_partial l (\z. u (drop(fstcart z)) (sndcart z))
                      (pastecart (lift(a + (b - a) * inv(&n + &2))) (sndcart w)))` THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC PDM_CONTINUOUS_ON_LOCAL THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
    STRIP_TAC THEN USE_THEN "cl" (fun th -> MP_TAC(MP (SPEC `y:real^N` th) (ASSUME `(y:real^N) IN U`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `pde_upto_classical a b (V:real^N->bool) (u:real->real^N->real^K)` THEN
    REWRITE_TAC[pde_upto_classical] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(:real^1) PCROSS (V:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `h:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{pastecart (lift t) z | a <= t /\ t < b /\ (z:real^N) IN V}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real` (X_CHOOSE_THEN `z':real^N`
        STRIP_ASSUME_TAC)) MP_TAC) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`t':real`; `z':real^N`] THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real` (X_CHOOSE_THEN `z':real^N`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN DISCH_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    COND_CASES_TAC THENL [MATCH_MP_TAC(ASSUME `!t y. a < t /\ t < b /\ (y:real^N) IN V
                     ==> (h:real^(1,N)finite_sum->real^K) (pastecart (lift t) y) =
                         iterated_partial l
                           (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z))
                           (pastecart (lift t) y)`) THEN
                          ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `t':real = a` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC TENDSTO_LIM THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. (h:real^(1,N)finite_sum->real^K)
                      (pastecart (lift(a + (b - a) * inv(&n + &2))) z')` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!t y. a < t /\ t < b /\ (y:real^N) IN V
                     ==> (h:real^(1,N)finite_sum->real^K) (pastecart (lift t) y) =
                         iterated_partial l
                           (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z))
                           (pastecart (lift t) y)`) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "dn" (fun th -> REWRITE_TAC[SPEC `n:num` th]);
      ALL_TAC] THEN
    UNDISCH_TAC `(h:real^(1,N)finite_sum->real^K) continuous_on
                   {pastecart (lift t) z | a <= t /\ t < b /\ (z:real^N) IN V}` THEN
    REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPECL
      [`\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z':real^N)`;
       `pastecart (lift a) (z':real^N)`]) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real`; `z':real^N`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      X_GEN_TAC `n:num` THEN
      MAP_EVERY EXISTS_TAC [`a + (b - a) * inv(&n + &2)`; `z':real^N`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "dn" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[LIM_CONST]]]);;

(* pde_tfam_from can be checked on the interiors of the pieces of a cover. *)

let PDM_TFAM_FROM_COVER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks a b
    (v:real->A->real^N^N).
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\ a < b /\
        (!i. i < n0
             ==> pde_upto a b (interior(ks i))
                   (\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (cs i) (v t) y)))
        ==> pde_tfam_from atlas a b v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cov")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "up")))) THEN
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC PDM_UPTO_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y0 IN FST c /\ SND c (chart_inv c y0) = y0`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?i z0. i < n0 /\ z0 IN interior((ks:num->real^N->bool) i) /\
           chart_inv (c:(A->bool)#(A->real^N)) y0 =
           chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cov" (MP_TAC o CONJUNCT2 o REWRITE_RULE[pde_cover]) THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_inv (c:(A->bool)#(A->real^N)) y0`) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z0:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `z0:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
    (ks:num->real^N->bool) i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cov" (MP_TAC o SPEC `i:num` o CONJUNCT1 o REWRITE_RULE[pde_cover]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Vi = {p:A | p IN FST((cs:num->(A->bool)#(A->real^N)) i) /\
                          SND(cs i) p IN interior((ks:num->real^N->bool) i)}` THEN
  SUBGOAL_THEN `open_in top (Vi:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Vi" THEN MATCH_MP_TAC PDM_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y0 IN (Vi:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Vi" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z0:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `(ks:num->real^N->bool) i` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Vi:A->bool) SUBSET FST((cs:num->(A->bool)#(A->real^N)) i)` ASSUME_TAC THENL
   [EXPAND_TAC "Vi" THEN SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER (Vi:A->bool))` THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER (Vi:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "up" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
  REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
      (mpullback (chart_trans (c:(A->bool)#(A->real^N)) ((cs:num->(A->bool)#(A->real^N)) i))
         (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (fstcart w) z)))
         (sndcart w))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDM_MPULLBACK_SMOOTH_ST THEN
    EXISTS_TAC `interior((ks:num->real^N->bool) i)` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL; OPEN_INTERIOR] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                        (FST c INTER FST((cs:num->(A->bool)#(A->real^N)) i))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                       `FST((cs:num->(A->bool)#(A->real^N)) i)`;
                       `SND((cs:num->(A->bool)#(A->real^N)) i)`] CHART_TRANS_SMOOTH) THEN
        ASM_REWRITE_TAC[PAIR]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) i`; `x:A`]
                    PDM_CHART_TRANS_AT_C) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(x:A) IN Vi` THEN EXPAND_TAC "Vi" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i) /\
                SND(cs i) x IN interior((ks:num->real^N->bool) i)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN Vi` THEN EXPAND_TAC "Vi" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) i`;
                 `(v:real->A->real^N^N) t`; `SND(c:(A->bool)#(A->real^N)) x`]
                PDM_METRIC_LOCAL_TRANS_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(cs:num->(A->bool)#(A->real^N)) i`; `x:A`]
                PDM_CHART_TRANS_AT_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE]);;

(* ------------------------------------------------------------------------- *)
(* Limits of families.  Smooth limits under locally uniform Cauchy jets;    *)
(* Cauchy bounds for t > a extend to t = a by continuity.                   *)
(* ------------------------------------------------------------------------- *)

let PDM_SEQ_SMOOTH_LIMIT_LOCAL = prove
 (`!s (f:num->real^M->real^K).
     open s /\ (!n. smooth_map_on s (f n)) /\
     (!x. x IN s
          ==> ?u. open u /\ x IN u /\ u SUBSET s /\
                  !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
                      ==> !e. &0 < e
                              ==> ?N. !m n y. N <= m /\ N <= n /\ y IN u
                                              ==> norm(iterated_partial l (f m) y -
                                                       iterated_partial l (f n) y) < e)
     ==> ?g. smooth_map_on s g /\
             !l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
                   ==> ((\n. iterated_partial l (f n) x) --> iterated_partial l g x)
                       sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ?u (gu:real^M->real^K).
              open u /\ x IN u /\ u SUBSET s /\ smooth_map_on u gu /\
              !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
                  ==> !e. &0 < e
                          ==> ?N. !n y. N <= n /\ y IN u
                                        ==> norm(iterated_partial l
                                                   ((f:num->real^M->real^K) n) y -
                                                 iterated_partial l gu y) < e`
  (LABEL_TAC "lg") THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `x:real^M` th) (ASSUME `(x:real^M) IN s`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^M->bool`; `f:num->real^M->real^K`] PDM_SEQ_SMOOTH_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `gu:real^M->real^K` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`u:real^M->bool`; `gu:real^M->real^K`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u (gu:real^M->real^K) y.
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
           ==> !e. &0 < e
                   ==> ?N. !n y. N <= n /\ y IN u
                                 ==> norm(iterated_partial l ((f:num->real^M->real^K) n) y -
                                          iterated_partial l gu y) < e) /\ y IN u
      ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
              ==> ((\n. iterated_partial l (f n) y) --> iterated_partial l gu y) sequentially`
  (LABEL_TAC "pt") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u (gu:real^M->real^K).
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
           ==> !e. &0 < e
                   ==> ?N. !n y. N <= n /\ y IN u
                                 ==> norm(iterated_partial l ((f:num->real^M->real^K) n) y -
                                          iterated_partial l gu y) < e)
      ==> !y. y IN u ==> lim sequentially (\n. f n y) = gu y`
  (LABEL_TAC "eq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TENDSTO_LIM THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    USE_THEN "pt" (MP_TAC o SPECL [`u:real^M->bool`; `gu:real^M->real^K`; `y:real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial; ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^M. lim sequentially (\n. (f:num->real^M->real^K) n x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    USE_THEN "lg" (fun th -> MP_TAC(MP (SPEC `x:real^M` th) (ASSUME `(x:real^M) IN s`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` (X_CHOOSE_THEN `gu:real^M->real^K`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `gu:real^M->real^K` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN BETA_TAC THEN
    USE_THEN "eq" (MP_TAC o SPECL [`u:real^M->bool`; `gu:real^M->real^K`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^M`] THEN STRIP_TAC THEN
    USE_THEN "lg" (fun th -> MP_TAC(MP (SPEC `x:real^M` th) (ASSUME `(x:real^M) IN s`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` (X_CHOOSE_THEN `gu:real^M->real^K`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `iterated_partial l (\x. lim sequentially (\n. (f:num->real^M->real^K) n x)) x =
      iterated_partial l gu x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `u:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN BETA_TAC THEN
      USE_THEN "eq" (MP_TAC o SPECL [`u:real^M->bool`; `gu:real^M->real^K`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "pt" (MP_TAC o SPECL [`u:real^M->bool`; `gu:real^M->real^K`; `x:real^M`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let PDM_CAUCHY_CLOSURE_A = prove
 (`!(H:num->real^(1,N)finite_sum->real^K) a b t1 U.
     a < t1 /\ t1 < b /\
     (!n. (H n) continuous_on {pastecart (lift t) y | a <= t /\ t < b /\ y IN U}) /\
     (!e. &0 < e
          ==> ?N. !m n t y. N <= m /\ N <= n /\ a < t /\ t <= t1 /\ y IN U
                            ==> norm(H m (pastecart (lift t) y) -
                                     H n (pastecart (lift t) y)) < e)
     ==> !e. &0 < e
             ==> ?N. !m n t y. N <= m /\ N <= n /\ a <= t /\ t <= t1 /\ y IN U
                               ==> norm(H m (pastecart (lift t) y) -
                                        H n (pastecart (lift t) y)) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ct") (LABEL_TAC "cau")))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "cau" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `a < t` THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `e / &2` THEN CONJ_TAC THENL
     [USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t:real = a` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `t1:real`] PDM_APPROACH_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dn") (LABEL_TAC "dlim")) THEN
  ABBREV_TAC `z = \k. pastecart (lift(a + (t1 - a) * inv(&k + &2))) (y:real^N)` THEN
  SUBGOAL_THEN
   `((z:num->real^(1,N)finite_sum) --> pastecart (lift a) y) sequentially /\
    (!k. z k IN {pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}) /\
    pastecart (lift a) y IN {pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[LIM_CONST];
      X_GEN_TAC `k:num` THEN
      MAP_EVERY EXISTS_TAC [`a + (t1 - a) * inv(&k + &2)`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "dn" (MP_TAC o SPEC `k:num`) THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`a:real`; `y:real^N`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (((H:num->real^(1,N)finite_sum->real^K) j) o (z:num->real^(1,N)finite_sum) -->
         H j (pastecart (lift a) (y:real^N))) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    USE_THEN "ct" (MP_TAC o REWRITE_RULE[CONTINUOUS_ON_SEQUENTIALLY] o SPEC `j:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\k. ((H:num->real^(1,N)finite_sum->real^K) m o
                       (z:num->real^(1,N)finite_sum)) k - (H n o z) k`;
                 `(H:num->real^(1,N)finite_sum->real^K) m (pastecart (lift a) (y:real^N)) -
                  H n (pastecart (lift a) y)`;
                 `e / &2`] LIM_NORM_UBOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[o_THM] THEN
      EXPAND_TAC "z" THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "dn" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Uniformly Cauchy sequences converge uniformly to their pointwise limits. *)

let PDM_UNIFORM_CAUCHY_LIM = prove
 (`!(P:B->bool) (f:num->B->real^K) g.
     (!e. &0 < e ==> ?N. !m n x. N <= m /\ N <= n /\ P x ==> norm(f m x - f n x) < e) /\
     (!x. P x ==> ((\n. f n x) --> g x) sequentially)
     ==> !e. &0 < e ==> ?N. !n x. N <= n /\ P x ==> norm(f n x - g x) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c") (LABEL_TAC "p")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "c" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:B`] THEN STRIP_TAC THEN
  USE_THEN "p" (fun th -> MP_TAC(MP (SPEC `x:B` th) (ASSUME `(P:B->bool) x`))) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M + N:num`)) THEN REWRITE_TAC[LE_ADD] THEN
  USE_THEN "N" (fun th -> MP_TAC(MP (SPECL [`n:num`; `M + N:num`; `x:B`] th)
    (CONJ (ASSUME `N:num <= n`) (CONJ (ARITH_RULE `N:num <= M + N`)
          (ASSUME `(P:B->bool) x`))))) THEN
  CONV_TAC NORM_ARITH);;

(* The Euclidean core of the families limit: maps smooth up to time a      *)
(* whose space-time jets are uniformly Cauchy on (a,t1] x U for every      *)
(* t1 < b have a limit smooth up to time a, with uniform convergence of     *)
(* the jets on (a,t1] x U.                                                   *)

let PDM_UPTO_LIMIT = prove
 (`!a b (U:real^N->bool) (FF:num->real^(1,N)finite_sum->real^K) (e:num->real).
        open U /\ a < b /\
        (!n. &0 < e n /\
             smooth_map_on (interval(lift(a - e n),lift b) PCROSS U) (FF n)) /\
        (!l t1. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ t1 < b
                ==> !d. &0 < d
                        ==> ?N0. !m n t y. N0 <= m /\ N0 <= n /\ a < t /\ t <= t1 /\ y IN U
                                           ==> norm(iterated_partial l (FF m)
                                                      (pastecart (lift t) y) -
                                                    iterated_partial l (FF n)
                                                      (pastecart (lift t) y)) < d)
        ==> ?G. pde_upto a b U (\t y. G(pastecart (lift t) y)) /\
                (!t y. a <= t /\ t < b /\ y IN U
                       ==> ((\n. FF n (pastecart (lift t) y)) --> G(pastecart (lift t) y))
                           sequentially) /\
                (!l t1. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ t1 < b
                        ==> !d. &0 < d
                                ==> ?N0. !n t y. N0 <= n /\ a < t /\ t <= t1 /\ y IN U
                                                 ==> norm(iterated_partial l (FF n)
                                                            (pastecart (lift t) y) -
                                                          iterated_partial l G
                                                            (pastecart (lift t) y)) < d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sm") (LABEL_TAC "cau")))) THEN
  (* the open slab and the regularity of the FF n *)
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (interval(lift a,lift b) PCROSS (U:real^N->bool))
                      ((FF:num->real^(1,N)finite_sum->real^K) n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - (e:num->real) n),lift b) PCROSS (U:real^N->bool)` THEN
    USE_THEN "sm" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `n:num` th)]) THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    USE_THEN "sm" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n l. (iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n)) continuous_on
          {pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}`
  (LABEL_TAC "ct") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - (e:num->real) n),lift b) PCROSS (U:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      USE_THEN "sm" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN DISCH_TAC THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the smooth limit on the open slab *)
  MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
                 `FF:num->real^(1,N)finite_sum->real^K`] PDM_SEQ_SMOOTH_LIMIT_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `y0:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `interval(lift a,lift((s0 + b) / &2)) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
      USE_THEN "cau" (MP_TAC o SPECL [`l:num list`; `(s0 + b) / &2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1;
                  LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(1,N)finite_sum->real^K`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gj"))) THEN
  (* Cauchy up to t = a *)
  SUBGOAL_THEN
   `!l t1. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ a < t1 /\ t1 < b
           ==> !d. &0 < d
                   ==> ?N0. !m n t y. N0 <= m /\ N0 <= n /\ a <= t /\ t <= t1 /\
                                      (y:real^N) IN U
                                      ==> norm(iterated_partial l
                                                 ((FF:num->real^(1,N)finite_sum->real^K) m)
                                                 (pastecart (lift t) y) -
                                               iterated_partial l (FF n)
                                                 (pastecart (lift t) y)) < d`
  (LABEL_TAC "cauc") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\n. iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n)`;
                   `a:real`; `b:real`; `t1:real`; `U:real^N->bool`] PDM_CAUCHY_CLOSURE_A) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cau" (fun th -> ACCEPT_TAC(MP (SPECL [`l:num list`; `t1:real`] th)
      (CONJ (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l`)
            (ASSUME `t1 < b`))));
    ALL_TAC] THEN
  (* the limits of the jets on the closed slab *)
  ABBREV_TAC `hh = \l w. lim sequentially
                     (\n. iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n) w)` THEN
  SUBGOAL_THEN
   `!l t y. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
            a <= t /\ t < b /\ (y:real^N) IN U
            ==> ((\n. iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n)
                        (pastecart (lift t) y)) -->
                 (hh:(num)list->real^(1,N)finite_sum->real^K) l (pastecart (lift t) y))
                sequentially`
  (LABEL_TAC "hpt") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "hh" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[CONVERGENT_EQ_CAUCHY; TENDSTO_LIM; TRIVIAL_LIMIT_SEQUENTIALLY]
      `cauchy (s:num->real^K) ==> (s --> lim sequentially s) sequentially`) THEN
    REWRITE_TAC[cauchy; GE; dist] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "cauc" (MP_TAC o SPECL [`l:num list`; `(t + b) / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* uniform convergence of the jets on [a,t1] x U *)
  SUBGOAL_THEN
   `!l t1. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\ a < t1 /\ t1 < b
           ==> !d. &0 < d
                   ==> ?N0. !n w. N0 <= n /\
                                  w IN {pastecart (lift t) y | a <= t /\ t <= t1 /\
                                                               (y:real^N) IN U}
                                  ==> norm(iterated_partial l
                                             ((FF:num->real^(1,N)finite_sum->real^K) n) w -
                                           (hh:(num)list->real^(1,N)finite_sum->real^K) l w)
                                      < d`
  (LABEL_TAC "hun") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PDM_UNIFORM_CAUCHY_LIM THEN CONJ_TAC THENL
     [X_GEN_TAC `d:real` THEN DISCH_TAC THEN
      USE_THEN "cauc" (MP_TAC o SPECL [`l:num list`; `t1:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `w:real^(1,N)finite_sum`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "hpt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the limits of the jets are continuous on the closed slab *)
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> ((hh:(num)list->real^(1,N)finite_sum->real^K) l) continuous_on
              {pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}`
  (LABEL_TAC "hct") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC PDM_CONTINUOUS_ON_LOCAL THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `interval(lift(a - &1),lift((t0 + b) / &2)) PCROSS (:real^N)` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
    EXISTS_TAC `\n. iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{pastecart (lift t) y | a <= t /\ t < b /\ (y:real^N) IN U}` THEN
      USE_THEN "ct" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "hun" (MP_TAC o SPECL [`l:num list`; `(t0 + b) / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* on the open slab the limits of the jets are the jets of the limit *)
  SUBGOAL_THEN
   `!l t y. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
            a < t /\ t < b /\ (y:real^N) IN U
            ==> (hh:(num)list->real^(1,N)finite_sum->real^K) l (pastecart (lift t) y) =
                iterated_partial l (g:real^(1,N)finite_sum->real^K) (pastecart (lift t) y)`
  (LABEL_TAC "hg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. iterated_partial l ((FF:num->real^(1,N)finite_sum->real^K) n)
                      (pastecart (lift t) y)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [USE_THEN "hpt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "gj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]];
    ALL_TAC] THEN
  EXISTS_TAC `(hh:(num)list->real^(1,N)finite_sum->real^K) []` THEN
  SUBGOAL_THEN
   `!w. w IN interval(lift a,lift b) PCROSS (U:real^N->bool)
        ==> (hh:(num)list->real^(1,N)finite_sum->real^K) [] w =
            (g:real^(1,N)finite_sum->real^K) w`
  (LABEL_TAC "hg0") THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "hg" (MP_TAC o SPECL [`[]:num list`; `t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS (U:real^N->bool))
                  ((hh:(num)list->real^(1,N)finite_sum->real^K) [])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^(1,N)finite_sum->real^K` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "hg0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l t y. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
            a < t /\ t < b /\ (y:real^N) IN U
            ==> iterated_partial l ((hh:(num)list->real^(1,N)finite_sum->real^K) [])
                  (pastecart (lift t) y) =
                hh l (pastecart (lift t) y)`
  (LABEL_TAC "hj") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "hg" (MP_TAC o SPECL [`l:num list`; `t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    USE_THEN "hg0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[pde_upto_classical] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND; ETA_AX] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "hct" (MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      EXISTS_TAC `(hh:(num)list->real^(1,N)finite_sum->real^K) l` THEN CONJ_TAC THENL
       [USE_THEN "hct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "hj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    REPEAT STRIP_TAC THEN
    USE_THEN "hpt" (MP_TAC o SPECL [`[]:num list`; `t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial; ETA_AX]];
    MAP_EVERY X_GEN_TAC [`l:num list`; `t1:real`] THEN STRIP_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `a < t1` THENL
     [ALL_TAC; EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    USE_THEN "hun" (MP_TAC o SPECL [`l:num list`; `t1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "hj" (MP_TAC o SPECL [`l:num list`; `t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Limits of families.  A sequence of pde_tfam_from families whose           *)
(* space-time jets in the charts of a cover are uniformly Cauchy on          *)
(* (a,t1] x interior(ks i) for every t1 < b has a pde_tfam_from limit, with  *)
(* pointwise convergence on M and uniform convergence of the chart jets on   *)
(* the same sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let PDM_TFAM_LIMIT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks a b
    (vv:num->real->A->real^N^N).
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\ a < b /\
        (!n. pde_tfam_from atlas a b (vv n)) /\
        (!i l t1. i < n0 /\ ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) l /\ t1 < b
                  ==> !d. &0 < d
                          ==> ?N0. !m n t y. N0 <= m /\ N0 <= n /\ a < t /\ t <= t1 /\
                                             y IN interior(ks i)
                                             ==> norm(iterated_partial l
                                                        (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                               (metric_local atlas (cs i)
                                                                  (vv m (drop(fstcart w))) (sndcart w)))
                                                        (pastecart (lift t) y) -
                                                      iterated_partial l
                                                        (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                               (metric_local atlas (cs i)
                                                                  (vv n (drop(fstcart w))) (sndcart w)))
                                                        (pastecart (lift t) y)) < d)
        ==> ?v. pde_tfam_from atlas a b v /\
                (!t x. ~(a <= t /\ t < b /\ x IN topspace top) ==> v t x = mat 0) /\
                (!t x. a <= t /\ t < b /\ x IN topspace top
                       ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (vv n t x)) -->
                            vectorize(v t x)) sequentially) /\
                (!i l t1. i < n0 /\ ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) l /\
                          t1 < b
                          ==> !d. &0 < d
                                  ==> ?N0. !n t y. N0 <= n /\ a < t /\ t <= t1 /\
                                                   y IN interior(ks i)
                                                   ==> norm(iterated_partial l
                                                              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                                     (metric_local atlas (cs i)
                                                                        (vv n (drop(fstcart w))) (sndcart w)))
                                                              (pastecart (lift t) y) -
                                                            iterated_partial l
                                                              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                                     (metric_local atlas (cs i)
                                                                        (v (drop(fstcart w))) (sndcart w)))
                                                              (pastecart (lift t) y)) < d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cov")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fam") (LABEL_TAC "cau"))))) THEN
  (* chart facts *)
  SUBGOAL_THEN
   `!i. i < n0
        ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\
            (ks:num->real^N->bool) i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
            interior(ks i) SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
            open(IMAGE (SND(cs i)) (FST(cs i))) /\ FST(cs i) SUBSET topspace top /\
            (!x. x IN FST(cs i) ==> chart_inv (cs i) (SND(cs i) x) = x) /\
            (!z. z IN IMAGE (SND(cs i)) (FST(cs i))
                 ==> chart_inv (cs i) z IN FST(cs i) /\ SND(cs i) (chart_inv (cs i) z) = z)`
  (LABEL_TAC "cf") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\
      (ks:num->real^N->bool) i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "cov" (MP_TAC o SPEC `i:num` o CONJUNCT1 o REWRITE_RULE[pde_cover]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(ks:num->real^N->bool) i` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the chart extensions of the vv n *)
  SUBGOAL_THEN
   `?EE (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod).
      !n i. i < n0
            ==> &0 < EE n i /\
                smooth_map_on (interval(lift(a - EE n i),lift b) PCROSS
                               IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                              (FFF n i) /\
                !t y. a <= t /\ t < b /\ y IN IMAGE (SND(cs i)) (FST(cs i))
                      ==> FFF n i (pastecart (lift t) y) =
                          (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (cs i) ((vv:num->real->A->real^N^N) n t) y)`
  (X_CHOOSE_THEN `EE:num->num->real` (X_CHOOSE_THEN
     `FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod` (LABEL_TAC "ext"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "fam" (MP_TAC o REWRITE_RULE[pde_tfam_from] o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN
    USE_THEN "cf" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))]);
    ALL_TAC] THEN
  (* the jets of the extensions are those of the families for t > a *)
  SUBGOAL_THEN
   `!n i l t y. i < n0 /\ a < t /\ t < b /\
                y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))
                ==> iterated_partial l
                      ((FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i)
                      (pastecart (lift t) y) =
                    iterated_partial l
                      (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas (cs i)
                                ((vv:num->real->A->real^N^N) n (drop(fstcart w))) (sndcart w)))
                      (pastecart (lift t) y)`
  (LABEL_TAC "jeq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS
                IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "ext" (fun th -> MP_TAC(SPECL [`s:real`; `z:real^N`]
      (CONJUNCT2(CONJUNCT2(MP (SPECL [`n:num`; `i:num`] th) (ASSUME `(i:num) < n0`)))))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the limits in the charts of the cover *)
  SUBGOAL_THEN
   `?GG. !i. i < n0
             ==> pde_upto a b (interior((ks:num->real^N->bool) i))
                   (\t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                            (pastecart (lift t) y)) /\
                 (!t y. a <= t /\ t < b /\ y IN interior(ks i)
                        ==> ((\n. (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i
                                    (pastecart (lift t) y)) -->
                             GG i (pastecart (lift t) y)) sequentially) /\
                 (!l t1. ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) l /\ t1 < b
                         ==> !d. &0 < d
                                 ==> ?N0. !n t y. N0 <= n /\ a < t /\ t <= t1 /\
                                                  y IN interior(ks i)
                                                  ==> norm(iterated_partial l (FFF n i)
                                                             (pastecart (lift t) y) -
                                                           iterated_partial l (GG i)
                                                             (pastecart (lift t) y)) < d)`
  (X_CHOOSE_THEN `GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod` (LABEL_TAC "GG")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `interior((ks:num->real^N->bool) i)`;
                   `\n. (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i`;
                   `\n. (EE:num->num->real) n i`] PDM_UPTO_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      USE_THEN "ext" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`n:num`; `i:num`] th)
        (ASSUME `(i:num) < n0`))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - (EE:num->num->real) n i),lift b) PCROSS
                  IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `t1:real`] THEN STRIP_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "cau" (MP_TAC o SPECL [`i:num`; `l:num list`; `t1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MP (SPEC `d:real` th) (ASSUME `&0 < d`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)) /\
                  t < b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN interior((ks:num->real^N->bool) i)` THEN
        UNDISCH_TAC `interior((ks:num->real^N->bool) i) SUBSET
                     IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
        SET_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "jeq" (fun th ->
      REWRITE_TAC[MP (SPECL [`m:num`; `i:num`; `l:num list`; `t:real`; `y:real^N`] th)
        (CONJ (ASSUME `(i:num) < n0`) (CONJ (ASSUME `a < t`) (CONJ (ASSUME `t < b`)
          (ASSUME `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`))));
        MP (SPECL [`n:num`; `i:num`; `l:num list`; `t:real`; `y:real^N`] th)
        (CONJ (ASSUME `(i:num) < n0`) (CONJ (ASSUME `a < t`) (CONJ (ASSUME `t < b`)
          (ASSUME `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`))))]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the limit family *)
  ABBREV_TAC
   `vlim = \t x:A. if a <= t /\ t < b /\ x IN topspace top
                   then (matrify:real^(N,N)finite_prod->real^N^N)
                          (lim sequentially
                            (\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                                   ((vv:num->real->A->real^N^N) n t x)))
                   else mat 0` THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((vv:num->real->A->real^N^N) n t x)) -->
               vectorize((vlim:real->A->real^N^N) t x)) sequentially`
  (LABEL_TAC "ptv") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?i z0. i < n0 /\ z0 IN interior((ks:num->real^N->bool) i) /\
             x = chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z0`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "cov" (MP_TAC o CONJUNCT2 o REWRITE_RULE[pde_cover]) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z0:real^N` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `z0:real^N`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    SUBGOAL_THEN `(z0:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(z0:real^N) IN interior((ks:num->real^N->bool) i)` THEN
      UNDISCH_TAC `interior((ks:num->real^N->bool) i) SUBSET
                   IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN FST((cs:num->(A->bool)#(A->real^N)) i) /\ SND(cs i) x = z0`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\n. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                ((vv:num->real->A->real^N^N) n t) z0)) =
      (\n. (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i
             (pastecart (lift t) z0))`
    ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN CONV_TAC SYM_CONV THEN
      USE_THEN "ext" (fun th -> MP_TAC(SPECL [`t:real`; `z0:real^N`]
        (CONJUNCT2(CONJUNCT2(MP (SPECL [`n:num`; `i:num`] th) (ASSUME `(i:num) < n0`)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\n. (vectorize:real^N^N->real^(N,N)finite_prod) ((vv:num->real->A->real^N^N) n t x)) -->
       vectorize(pdm_chart_field atlas ((cs:num->(A->bool)#(A->real^N)) i)
                   ((matrify:real^(N,N)finite_prod->real^N^N) o
                    (\z. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                           (pastecart (lift t) z))) x)) sequentially`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`;
                     `\n. (vv:num->real->A->real^N^N) n t`;
                     `\z. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                            (pastecart (lift t) z)`;
                     `x:A`; `sequentially`] PDM_CHART_FIELD_LIM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "GG" (fun th -> MP_TAC(SPECL [`t:real`; `z0:real^N`]
        (CONJUNCT1(CONJUNCT2(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`)))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "vlim" THEN
    REWRITE_TAC[ASSUME `a <= t`; ASSUME `t < b`; ASSUME `(x:A) IN topspace top`;
                VECTORIZE_MATRIFY] THEN
    MATCH_MP_TAC(MESON[TENDSTO_LIM; TRIVIAL_LIMIT_SEQUENTIALLY]
     `!(s:num->real^(N,N)finite_prod) l.
        (s --> l) sequentially ==> (s --> lim sequentially s) sequentially`) THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(rator(concl th))) THEN ACCEPT_TAC th);
    ALL_TAC] THEN
  (* the chart representatives of the limit *)
  SUBGOAL_THEN
   `!i t y. i < n0 /\ a <= t /\ t < b /\ y IN interior((ks:num->real^N->bool) i)
            ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                     ((vlim:real->A->real^N^N) t) y) =
                (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i (pastecart (lift t) y)`
  (LABEL_TAC "vchart") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN interior((ks:num->real^N->bool) i)` THEN
      UNDISCH_TAC `interior((ks:num->real^N->bool) i) SUBSET
                   IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i
                      (pastecart (lift t) y)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\n. (FFF:num->num->real^(1,N)finite_sum->real^(N,N)finite_prod) n i
               (pastecart (lift t) y)) =
        (\n. (vectorize:real^N^N->real^(N,N)finite_prod)
               (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                  ((vv:num->real->A->real^N^N) n t) y))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
        USE_THEN "ext" (fun th -> MP_TAC(SPECL [`t:real`; `y:real^N`]
          (CONJUNCT2(CONJUNCT2(MP (SPECL [`n:num`; `i:num`] th) (ASSUME `(i:num) < n0`)))))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`;
                     `\n. (vv:num->real->A->real^N^N) n t`;
                     `(vlim:real->A->real^N^N) t`; `y:real^N`; `sequentially`]
                    PDM_METRIC_LOCAL_LIM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ptv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `FST((cs:num->(A->bool)#(A->real^N)) i) SUBSET topspace top` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      USE_THEN "GG" (fun th -> MP_TAC(SPECL [`t:real`; `y:real^N`]
        (CONJUNCT1(CONJUNCT2(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`)))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `vlim:real->A->real^N^N` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PDM_TFAM_FROM_COVER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `n0:num`; `cs:num->(A->bool)#(A->real^N)`;
                          `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC PDM_UPTO_CONG THEN
    EXISTS_TAC `\t y. (GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                        (pastecart (lift t) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "GG" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `i:num` th)
        (ASSUME `(i:num) < n0`))]);
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "vchart" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "vlim" THEN ASM_REWRITE_TAC[];
    USE_THEN "ptv" ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `l:num list`; `t1:real`] THEN STRIP_TAC THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
  USE_THEN "GG" (fun th -> MP_TAC(SPEC `d:real` (MP (SPECL [`l:num list`; `t1:real`]
    (CONJUNCT2(CONJUNCT2(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`)))))
    (CONJ (ASSUME `ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) l`)
          (ASSUME `t1 < b`))))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N0:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)) /\
                t < b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN interior((ks:num->real^N->bool) i)` THEN
      UNDISCH_TAC `interior((ks:num->real^N->bool) i) SUBSET
                   IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "jeq" (fun th ->
    REWRITE_TAC[GSYM(MP (SPECL [`n:num`; `i:num`; `l:num list`; `t:real`; `y:real^N`] th)
      (CONJ (ASSUME `(i:num) < n0`) (CONJ (ASSUME `a < t`) (CONJ (ASSUME `t < b`)
        (ASSUME `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`)))))]) THEN
  SUBGOAL_THEN
   `iterated_partial l
      (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                ((vlim:real->A->real^N^N) (drop(fstcart w))) (sndcart w)))
      (pastecart (lift t) y) =
    iterated_partial l ((GG:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i)
      (pastecart (lift t) y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS interior((ks:num->real^N->bool) i)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_INTERIOR; PASTECART_IN_PCROSS;
                 IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "vchart" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

