(* ========================================================================= *)
(* Unit pc_pde_mnorm (PDE layer, chart-wise norms): finite chart covers with *)
(* cutoffs on compact manifolds, chart bounds of metrics, chart-wise Sobolev *)
(* norms of tensor fields, the transplant of compactly supported chart       *)
(* functions to the unit cube (dilation and periodization), jet bounds for   *)
(* pullbacks under chart changes, and the Sobolev embedding for the          *)
(* chart-wise norms (PDE_MNORM_SOBOLEV).                                     *)
(*                                                                           *)
(* First the definitions pde_tensor_smooth, pde_mnorm2, pde_cutoffs and      *)
(* basic facts.  pde_cover and pde_cbound are those of pc_pde_iface.         *)
(* pde_tensor_smooth is the same notion as mfd_tensor2_smooth of             *)
(* pc_mfd_fields (PDM_TENSOR_SMOOTH_EQ).                                     *)
(* ========================================================================= *)

needs "src/pc_pde_torus.ml";;
needs "src/pc_mfd_cutoff.ml";;
needs "src/pc_pde_iface.ml";;
needs "src/pc_rf_extend.ml";;

prioritize_real();;
type_invention_error := true;;

(* Symmetric 2-tensor fields smooth in every chart (matrices in preferred    *)
(* coordinates, transforming like metrics).                                  *)

let pde_tensor_smooth = new_definition
 `pde_tensor_smooth (atlas:((A->bool)#(A->real^N))->bool) (v:A->real^N^N) <=>
    !c. c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c))
              ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c v)`;;

(* Chart-wise H^s norm squared of a tensor field v for cutoffs psi i        *)
(* supported in the chart domains: sum over charts and index lists of the   *)
(* L^2 norms of the derivatives of psi_i v in the coordinates of cs i.      *)

let pde_mnorm2 = new_definition
 `pde_mnorm2 (atlas:((A->bool)#(A->real^N))->bool) (n0:num)
             (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) (s:num)
             (v:A->real^N^N) =
    sum {i | i < n0}
     (\i. sum (pde_index_lists s (:N))
           (\l. drop(integral (IMAGE (SND(cs i)) (FST(cs i)))
                  (\y. lift(norm(iterated_partial l
                         (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (psi i (chart_inv (cs i) z) %%
                               metric_local atlas (cs i) v z)) y) pow 2)))))`;;

(* Admissible cutoffs for a cover: smooth, values in [0,1], vanishing off a  *)
(* compact subset of the chart domain, and some psi_i equal to 1 near every *)
(* point.                                                                    *)

let pde_cutoffs = new_definition
 `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (n0:num)
              (cs:num->(A->bool)#(A->real^N)) (psi:num->A->real) <=>
    (!i. i < n0 ==> cs i IN atlas /\ mfd_smooth atlas (\x. lift(psi i x)) /\
                    (!x. &0 <= psi i x /\ psi i x <= &1) /\
                    ?L. compact_in top L /\ L SUBSET FST(cs i) /\
                        !x. ~(x IN L) ==> psi i x = &0) /\
    (!x. x IN topspace top
         ==> ?i V. i < n0 /\ open_in top V /\ x IN V /\ !z. z IN V ==> psi i z = &1)`;;

(* pde_tensor_smooth is mfd_tensor2_smooth (pc_mfd_fields): same body.       *)

let PDM_TENSOR_SMOOTH_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (v:A->real^N^N).
        pde_tensor_smooth atlas v <=> mfd_tensor2_smooth atlas v`,
  REWRITE_TAC[pde_tensor_smooth; mfd_tensor2_smooth]);;

let PDM_TENSOR_SMOOTH_EQ_FUN = prove
 (`(pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool) =
   mfd_tensor2_smooth`,
  REWRITE_TAC[FUN_EQ_THM; PDM_TENSOR_SMOOTH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Finite covers with cutoffs on compact manifolds                           *)
(* (PDE_COVER_CUTOFFS_EXISTS; the cover alone is PDE_COVER_EXISTS and the    *)
(* chart bounds PDE_CBOUND_EXISTS of pc_rf_extend).  Chart bumps of          *)
(* pc_mfd_cutoff around finitely many points: the pieces are the closed      *)
(* chart balls of radius 2r, the cutoffs are 1 on the chart balls of radius  *)
(* r and vanish off the pieces.                                              *)
(* ------------------------------------------------------------------------- *)

let PDM_CHART_BUMP = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) y0 r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        (U,phi) IN atlas /\ &0 < r /\ cball(y0,&2 * r) SUBSET IMAGE phi U
        ==> mfd_smooth atlas
              (\x. lift(if x IN U then smooth_bump r (&2 * r) (phi x - y0) else &0)) /\
            (!x. &0 <= (if x IN U then smooth_bump r (&2 * r) (phi x - y0) else &0) /\
                 (if x IN U then smooth_bump r (&2 * r) (phi x - y0) else &0) <= &1) /\
            compact_in top {p | p IN U /\ phi p IN cball(y0,&2 * r)} /\
            (!x. ~(x IN U /\ phi x IN cball(y0,&2 * r))
                 ==> (if x IN U then smooth_bump r (&2 * r) (phi x - y0) else &0) = &0) /\
            open_in top {p | p IN U /\ phi p IN ball(y0,r)} /\
            (!x. x IN U /\ phi x IN ball(y0,r)
                 ==> (if x IN U then smooth_bump r (&2 * r) (phi x - y0) else &0) = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p:A. let b = (if p IN U then smooth_bump r (&2 * r) ((phi:A->real^N) p - y0)
                   else &0) in
          &0 <= b /\ b <= &1 /\
          (p IN U /\ phi p IN ball(y0,r) ==> b = &1) /\
          (~(p IN U /\ phi p IN cball(y0,&2 * r)) ==> b = &0)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFDC_BUMP_VALUES THEN ASM_REWRITE_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDC_BUMP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* Chart domains lie in the space. *)

let PDM_CHART_SUBSET_TOPSPACE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> U SUBSET topspace top`,
  MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]);;

let PDE_COVER_CUTOFFS_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top
        ==> ?n0 cs ks psi. pde_cover (top,atlas) n0 cs ks /\
                           pde_cutoffs (top,atlas) n0 cs psi /\
                           !i x. i < n0 /\ ~(psi i x = &0)
                                 ==> x IN IMAGE (chart_inv (cs i)) (ks i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`] MFDC_LOCAL_BALL) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?UU PH RR. !x:A. x IN topspace top
        ==> (UU x,PH x) IN atlas /\ x IN UU x /\ &0 < RR x /\
            cball((PH x:A->real^N) x,&2 * RR x) SUBSET
            IMAGE (PH x) (UU x INTER topspace top)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> cball((PH x:A->real^N) x,&2 * RR x) SUBSET IMAGE (PH x) (UU x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((PH:A->A->real^N) x) (UU x INTER topspace top)` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
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
  MP_TAC(ISPECL [`FF:A->bool`; `CARD(FF:A->bool)`] HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i < CARD(FF:A->bool) ==> (e:num->A) i IN topspace top`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `CARD(FF:A->bool)` THEN
  EXISTS_TAC `\i. ((UU:A->A->bool) ((e:num->A) i),(PH:A->A->real^N) (e i))` THEN
  EXISTS_TAC `\i. cball((PH:A->A->real^N) (e i) (e i),&2 * RR((e:num->A) i))` THEN
  EXISTS_TAC
   `\i (p:A). if p IN (UU:A->A->bool) (e i)
              then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                               ((PH:A->A->real^N) (e i) p - PH (e i) (e i))
              else &0` THEN
  REWRITE_TAC[pde_cover; pde_cutoffs; FST; SND; ETA_AX] THEN
  SUBGOAL_THEN
   `!i. i < CARD(FF:A->bool)
        ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
              (\x. lift(if x IN (UU:A->A->bool) (e i)
                        then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                                         ((PH:A->A->real^N) (e i) x - PH (e i) (e i))
                        else &0)) /\
            (!x. &0 <= (if x IN (UU:A->A->bool) (e i)
                        then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                                         ((PH:A->A->real^N) (e i) x - PH (e i) (e i))
                        else &0) /\
                 (if x IN (UU:A->A->bool) (e i)
                  then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                                   ((PH:A->A->real^N) (e i) x - PH (e i) (e i))
                  else &0) <= &1) /\
            compact_in top {p | p IN UU(e i) /\
                                PH (e i) p IN cball(PH (e i) (e i),&2 * RR(e i))} /\
            (!x. ~(x IN UU(e i) /\ PH (e i) x IN cball(PH (e i) (e i),&2 * RR(e i)))
                 ==> (if x IN (UU:A->A->bool) (e i)
                      then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                                       ((PH:A->A->real^N) (e i) x - PH (e i) (e i))
                      else &0) = &0) /\
            open_in top {p | p IN UU(e i) /\
                             PH (e i) p IN ball(PH (e i) (e i),RR(e i))} /\
            (!x. x IN UU(e i) /\ PH (e i) x IN ball(PH (e i) (e i),RR(e i))
                 ==> (if x IN (UU:A->A->bool) (e i)
                      then smooth_bump (RR((e:num->A) i)) (&2 * RR(e i))
                                       ((PH:A->A->real^N) (e i) x - PH (e i) (e i))
                      else &0) = &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC PDM_CHART_BUMP THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* pieces *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[COMPACT_CBALL];
    (* covering by the interiors *)
    REWRITE_TAC[INTERIOR_CBALL; EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN
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
      SUBGOAL_THEN `?i. i < CARD(FF:A->bool) /\ (e:num->A) i = f` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC
       `IMAGE (chart_inv ((UU:A->A->bool) (e i),(PH:A->A->real^N) (e i)))
              (ball(PH (e i) (e i),&2 * RR((e:num->A) i)))` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(PH:A->A->real^N) f x` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(UU:A->A->bool) f`; `(PH:A->A->real^N) f`] CHART_INV) THEN
        ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        UNDISCH_TAC `(PH f:A->real^N) x IN ball(PH f f,RR f)` THEN
        ASM_REWRITE_TAC[IN_BALL] THEN
        SUBGOAL_THEN `&0 < RR(f:A)` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `y IN IMAGE ((PH:A->A->real^N) (e i)) (UU((e:num->A) i))`
      ASSUME_TAC THENL
       [SUBGOAL_THEN
         `ball((PH:A->A->real^N) (e i) (e i),&2 * RR((e:num->A) i)) SUBSET
          IMAGE (PH (e i)) (UU (e i))`
        MP_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `cball((PH:A->A->real^N) (e i) (e i),&2 * RR((e:num->A) i))` THEN
          ASM_SIMP_TAC[BALL_SUBSET_CBALL];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(UU:A->A->bool) ((e:num->A) i)`; `(PH:A->A->real^N) ((e:num->A) i)`] CHART_INV) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(UU:A->A->bool) ((e:num->A) i) SUBSET topspace top` MP_TAC THENL
       [MATCH_MP_TAC PDM_CHART_SUBSET_TOPSPACE THEN
        MAP_EVERY EXISTS_TAC
         [`atlas:((A->bool)#(A->real^N))->bool`; `(PH:A->A->real^N) ((e:num->A) i)`] THEN
        ASM_SIMP_TAC[];
        ASM SET_TAC[]]];
    (* cutoffs: chart, smoothness, values, support *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC
     `{p | p IN (UU:A->A->bool) (e i) /\
           (PH:A->A->real^N) (e i) p IN cball(PH (e i) (e i),&2 * RR((e:num->A) i))}` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    (* some cutoff is 1 near every point *)
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
    SUBGOAL_THEN `?i. i < CARD(FF:A->bool) /\ (e:num->A) i = f` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `i:num` THEN
    EXISTS_TAC
     `{p | p IN (UU:A->A->bool) (e i) /\
           (PH:A->A->real^N) (e i) p IN ball(PH (e i) (e i),RR((e:num->A) i))}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    (* the support of each cutoff lies in the chart image of its piece *)
    MAP_EVERY X_GEN_TAC [`i:num`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `x IN (UU:A->A->bool) (e i) /\
      (PH:A->A->real^N) (e i) x IN cball(PH (e i) (e i),&2 * RR((e:num->A) i))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(PH:A->A->real^N) ((e:num->A) i) x` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(UU:A->A->bool) ((e:num->A) i)`; `(PH:A->A->real^N) ((e:num->A) i)`] CHART_INV) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Maps with compact support in an open set (zero extension,                 *)
(* vanishing of partials off the support, integrability), affine changes of *)
(* variables (partials and integrals), and the periodization of maps        *)
(* vanishing off a closed box inside the open unit cube.                     *)
(* ------------------------------------------------------------------------- *)

(* Iterated partials of maps that vanish on an open set vanish there.        *)

let PDM_PARTIAL_ZERO_OFF = prove
 (`!s k (w:real^M->real^N) l z.
        open s /\ compact k /\ (!y. y IN s /\ ~(y IN k) ==> w y = vec 0) /\
        z IN s /\ ~(z IN k)
        ==> iterated_partial l w z = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
  EXISTS_TAC `s DIFF (k:real^M->bool)` THEN
  ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]);;

(* Zero extension of a smooth map vanishing off a compact subset of an open *)
(* set: smooth everywhere, with the partials of the map on the set and 0    *)
(* outside.                                                                  *)

let PDM_ZERO_EXT_SMOOTH = prove
 (`!s k (w:real^M->real^N).
        open s /\ compact k /\ k SUBSET s /\ smooth_map_on s w /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0)
        ==> smooth_map_on (:real^M) (\y. if y IN s then w y else vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^M` THEN
  ASM_CASES_TAC `(x:real^M) IN s` THENL
   [EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `w:real^M->real^N` THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `(:real^M) DIFF k` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^M. vec 0:real^N` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let PDM_ZERO_EXT_PARTIAL = prove
 (`!s k (w:real^M->real^N) l z.
        open s /\ compact k /\ k SUBSET s /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0)
        ==> iterated_partial l (\y. if y IN s then w y else vec 0) z =
            if z IN s then iterated_partial l w z else vec 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `(:real^M) DIFF k` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* Continuous maps vanishing off a compact set are integrable on the space.  *)

let PDM_INTEGRABLE_COMPACT_SUPPORT = prove
 (`!(f:real^M->real^N) k.
        f continuous_on (:real^M) /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
        ==> f integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^M` (X_CHOOSE_TAC `b:real^M`)) THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUPERSET THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

(* The squared norms of the partials of a smooth map vanishing off a        *)
(* compact set are integrable, and their integral over any open set         *)
(* containing the set is the integral over the space.                        *)

let PDM_SQNORM_PARTIAL_INTEGRABLE = prove
 (`!(f:real^M->real^N) k l.
        smooth_map_on (:real^M) f /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
        ==> (\x. lift(norm(iterated_partial l f x) pow 2)) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_INTEGRABLE_COMPACT_SUPPORT THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `iterated_partial l (f:real^M->real^N) x = vec 0`
      (fun th -> REWRITE_TAC[th; NORM_0; LIFT_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
                 REWRITE_TAC[LIFT_NUM]) THEN
    MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
    MAP_EVERY EXISTS_TAC [`(:real^M)`; `k:real^M->bool`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* Affine changes of variables.                                              *)
(* ------------------------------------------------------------------------- *)

let PDM_PARTIAL_AFFINE = prove
 (`!(f:real^M->real^N) c b i x.
        f differentiable (at (c % x + b))
        ==> partial_derivative i (\y. f(c % y + b)) x =
            c % partial_derivative i f (c % x + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(fun th -> ASSUME_TAC(MATCH_MP LINEAR_FRECHET_DERIVATIVE th) THEN
                          ASSUME_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] th)) THEN
  SUBGOAL_THEN
   `((\y. (f:real^M->real^N)(c % y + b)) has_derivative
     (\h. frechet_derivative f (at (c % x + b)) (c % h))) (at x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (f:real^M->real^N)(c % y + b)) = f o (\y. c % y + b)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. frechet_derivative (f:real^M->real^N) (at (c % x + b)) (c % h)) =
      frechet_derivative f (at (c % x + b)) o (\h. c % h + vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[LINEAR_CMUL]]);;

let PDM_SMOOTH_AFFINE = prove
 (`!(f:real^M->real^N) c b.
        smooth_map_on (:real^M) f ==> smooth_map_on (:real^M) (\y. f(c % y + b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (f:real^M->real^N)(c % y + b)) = f o (\y. c % y + b)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^M)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let PDM_ITERATED_PARTIAL_AFFINE = prove
 (`!l (f:real^M->real^N) c b.
        smooth_map_on (:real^M) f
        ==> !x. iterated_partial l (\y. f(c % y + b)) x =
                c pow (LENGTH l) % iterated_partial l f (c % x + b)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; LENGTH; real_pow; VECTOR_MUL_LID] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `iterated_partial t (\y. (f:real^M->real^N)(c % y + b)) =
    (\y. c pow (LENGTH t) % iterated_partial t f (c % y + b))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^M. iterated_partial t (f:real^M->real^N) differentiable (at z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `c pow (LENGTH(t:num list))`;
                 `\y:real^M. iterated_partial t (f:real^M->real^N) (c % y + b)`;
                 `x:real^M`] PARTIAL_DERIVATIVE_CMUL) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\y:real^M. iterated_partial t (f:real^M->real^N) (c % y + b)) =
      iterated_partial t f o (\y. c % y + b)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_ADD THEN REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN REWRITE_TAC[DIFFERENTIABLE_ID];
    DISCH_THEN(SUBST1_TAC o BETA_RULE)] THEN
  ASM_SIMP_TAC[PDM_PARTIAL_AFFINE; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_AC]);;

(* Integrals over the space under affine changes of variables.               *)

let PDM_INTEGRAL_AFFINE_UNIV = prove
 (`!(f:real^M->real^N) c b.
        f integrable_on (:real^M) /\ ~(c = &0)
        ==> integral (:real^M) (\x. f(c % x + b)) =
            inv(abs c pow dimindex(:M)) % integral (:real^M) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `integral (:real^M) (f:real^M->real^N)`;
                 `(:real^M)`; `c:real`; `b:real^M`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN X_GEN_TAC `y:real^M` THEN
  EXISTS_TAC `c % y + b:real^M` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Periodization of maps vanishing off the closed box [a,1-a]^N.            *)
(* ------------------------------------------------------------------------- *)

let pdm_frac = new_definition
 `pdm_frac (x:real^N) = (lambda i. frac(x$i)):real^N`;;

let pdm_floorv = new_definition
 `pdm_floorv (x:real^N) = (lambda i. floor(x$i)):real^N`;;

let pdm_periodize = new_definition
 `pdm_periodize (u:real^N->B) (x:real^N) = u(pdm_frac x)`;;

let PDM_FRAC_COMPONENT = prove
 (`!(x:real^N) i. 1 <= i /\ i <= dimindex(:N) ==> pdm_frac x$i = frac(x$i)`,
  SIMP_TAC[pdm_frac; LAMBDA_BETA]);;

let PDM_FLOORV_COMPONENT = prove
 (`!(x:real^N) i. 1 <= i /\ i <= dimindex(:N) ==> pdm_floorv x$i = floor(x$i)`,
  SIMP_TAC[pdm_floorv; LAMBDA_BETA]);;

let PDM_FRAC_SHIFT = prove
 (`!(x:real^N) i. 1 <= i /\ i <= dimindex(:N) ==> pdm_frac(x + basis i) = pdm_frac x`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ; PDM_FRAC_COMPONENT] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; BASIS_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM FRAC_UNIQUE] THEN
  REWRITE_TAC[FRAC_FLOOR; REAL_ARITH `(x + &1) - (x - f) = f + &1`] THEN
  SIMP_TAC[INTEGER_ADD; INTEGER_CLOSED; FLOOR] THEN
  MP_TAC(SPEC `(x:real^N)$j` FLOOR) THEN REAL_ARITH_TAC);;

let PDM_PERIODIZE_ZPER = prove
 (`!u:real^N->B. pde_zper (pdm_periodize u)`,
  SIMP_TAC[pde_zper; pdm_periodize; PDM_FRAC_SHIFT]);;

(* Floors of nearby numbers off the box margin. *)

let PDM_FLOOR_NEAR = prove
 (`!a x x0. &0 < a /\ a <= &1 / &2 /\ abs(x - x0) < a /\ ~(floor x = floor x0)
            ==> (frac x < a \/ &1 - a < frac x) /\
                (x - floor x0 < a \/ &1 - a < x - floor x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
  MP_TAC(SPEC `x0:real` FLOOR) THEN STRIP_TAC THEN
  ASM_CASES_TAC `floor x0 + &1 <= x` THENL
   [SUBGOAL_THEN `floor x = floor x0 + &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
      ASM_SIMP_TAC[INTEGER_ADD; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `x < floor x0` THENL
   [SUBGOAL_THEN `floor x = floor x0 - &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
      ASM_SIMP_TAC[INTEGER_SUB; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `~(floor x = floor x0)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Near the unit cube, outside [0,1), the fractional part is near an edge.  *)

let PDM_FRAC_NEAR_EDGE = prove
 (`!a x. &0 < a /\ a <= &1 / &2 /\ --a < x /\ x < &1 + a /\ ~(&0 <= x /\ x < &1)
         ==> (frac x < a \/ &1 - a < frac x) /\ (x < a \/ &1 - a < x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
  ASM_CASES_TAC `x < &0` THENL
   [SUBGOAL_THEN `floor x = -- &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN SIMP_TAC[INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `floor x = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN SIMP_TAC[INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* Off the box margin a map vanishing off the box is 0: the box test.        *)

let PDM_NOT_IN_BOX = prove
 (`!a (y:real^N) j.
        1 <= j /\ j <= dimindex(:N) /\ (y$j < a \/ &1 - a < y$j)
        ==> ~(y IN interval[a % vec 1,(&1 - a) % vec 1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

let PDM_PERIODIZE_LOCAL = prove
 (`!(u:real^N->real^K) a x0 x.
        &0 < a /\ a <= &1 / &2 /\
        (!y. ~(y IN interval[a % vec 1:real^N,(&1 - a) % vec 1]) ==> u y = vec 0) /\
        (!k. 1 <= k /\ k <= dimindex(:N) ==> abs(x$k - x0$k) < a)
        ==> pdm_periodize u x = u(x - pdm_floorv x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pdm_periodize] THEN
  ASM_CASES_TAC
   `!k. 1 <= k /\ k <= dimindex(:N) ==> floor((x:real^N)$k) = floor((x0:real^N)$k)` THENL
   [AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; PDM_FRAC_COMPONENT; VECTOR_SUB_COMPONENT; PDM_FLOORV_COMPONENT] THEN
    ASM_SIMP_TAC[FRAC_FLOOR];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real`; `(x:real^N)$j`; `(x0:real^N)$j`] PDM_FLOOR_NEAR) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(u:real^N->real^K) (pdm_frac x) = vec 0 /\ u(x - pdm_floorv x0) = vec 0`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC PDM_NOT_IN_BOX THEN
  EXISTS_TAC `j:num` THEN
  ASM_SIMP_TAC[PDM_FRAC_COMPONENT; VECTOR_SUB_COMPONENT; PDM_FLOORV_COMPONENT]);;

let PDM_PERIODIZE_SMOOTH = prove
 (`!(u:real^N->real^K) a.
        smooth_map_on (:real^N) u /\ &0 < a /\ a <= &1 / &2 /\
        (!y. ~(y IN interval[a % vec 1:real^N,(&1 - a) % vec 1]) ==> u y = vec 0)
        ==> smooth_map_on (:real^N) (pdm_periodize u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x0:real^N` THEN
  EXISTS_TAC `ball(x0:real^N,a)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y:real^N. (u:real^N->real^K)(y + --(pdm_floorv x0))` THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    BETA_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM VECTOR_SUB] THEN
    MATCH_MP_TAC PDM_PERIODIZE_LOCAL THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(x0:real^N,y)` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[PDE_SMOOTH_TRANSLATE; SUBSET_UNIV]]);;

(* The periodization agrees with the map near the closed unit cube.          *)

let PDM_PERIODIZE_EQ = prove
 (`!(u:real^N->real^K) a x.
        &0 < a /\ a <= &1 / &2 /\
        (!y. ~(y IN interval[a % vec 1:real^N,(&1 - a) % vec 1]) ==> u y = vec 0) /\
        x IN interval(--a % vec 1:real^N,(&1 + a) % vec 1)
        ==> pdm_periodize u x = u x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pdm_periodize] THEN
  ASM_CASES_TAC
   `!k. 1 <= k /\ k <= dimindex(:N) ==> &0 <= (x:real^N)$k /\ x$k < &1` THENL
   [AP_TERM_TAC THEN SIMP_TAC[CART_EQ; PDM_FRAC_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_FRAC_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN interval(--a % vec 1,(&1 + a) % vec 1)` THEN
  REWRITE_TAC[IN_INTERVAL] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `(x:real^N)$j`] PDM_FRAC_NEAR_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) (pdm_frac x) = vec 0 /\ u x = vec 0`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC PDM_NOT_IN_BOX THEN
  EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[PDM_FRAC_COMPONENT]);;

(* The torus norms of the periodization are the norms on the space.          *)

let PDM_HS2_PERIODIZE = prove
 (`!(u:real^N->real^K) a s.
        smooth_map_on (:real^N) u /\ &0 < a /\ a <= &1 / &2 /\
        (!y. ~(y IN interval[a % vec 1:real^N,(&1 - a) % vec 1]) ==> u y = vec 0)
        ==> pde_hs2 s (pdm_periodize u) =
            sum (pde_index_lists s (:N))
                (\l. drop(integral (:real^N)
                       (\x. lift(norm(iterated_partial l u x) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[vec 0,vec 1])
                (\x:real^N. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(--a % vec 1:real^N,(&1 + a) % vec 1)` THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC PDM_PERIODIZE_EQ THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `iterated_partial l (u:real^N->real^K) x = vec 0`
     (fun th -> REWRITE_TAC[th; NORM_0; LIFT_NUM] THEN
                CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM]) THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `(:real^N) DIFF interval[a % vec 1,(&1 - a) % vec 1]` THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_INTERVAL; IN_DIFF; IN_UNIV] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `~((x:real^N) IN interval[vec 0,vec 1])` THEN
    REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_MUL_COMPONENT; CONTRAPOS_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The transplant of a compactly supported map to the unit                   *)
(* cube (dilation by 1/lam around the centre of the cube, then              *)
(* periodization), its smoothness, periodicity, partials and torus norms,   *)
(* and the Sobolev embedding for maps with compact support in an open set   *)
(* (PDM_SOBOLEV_COMPACT, from PDE_TORUS_SOBOLEV_PARTIAL).                     *)
(* ------------------------------------------------------------------------- *)

(* Integrals of the squared partials of a map with compact support in an    *)
(* open set: integrability, the integral of the zero extension, sign.        *)

let PDM_ZERO_EXT_INTEGRAL = prove
 (`!s k (w:real^M->real^N) l.
        open s /\ compact k /\ k SUBSET s /\ smooth_map_on s w /\
        (!y. y IN s /\ ~(y IN k) ==> w y = vec 0)
        ==> (\y. lift(norm(iterated_partial l w y) pow 2)) integrable_on s /\
            integral s (\y. lift(norm(iterated_partial l w y) pow 2)) =
            integral (:real^M)
              (\y. lift(norm(iterated_partial l (\y. if y IN s then w y else vec 0) y)
                        pow 2)) /\
            &0 <= drop(integral s (\y. lift(norm(iterated_partial l w y) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(norm(iterated_partial l (\y. if y IN s then (w:real^M->real^N) y
                                            else vec 0) y) pow 2)) =
    (\y. if y IN s then lift(norm(iterated_partial l w y) pow 2) else vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`; `w:real^M->real^N`;
                   `l:num list`; `y:real^M`] PDM_ZERO_EXT_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(norm(iterated_partial l (\y. if y IN s then (w:real^M->real^N) y
                                            else vec 0) y) pow 2)) integrable_on (:real^M)`
  MP_TAC THENL
   [MATCH_MP_TAC PDM_SQNORM_PARTIAL_INTEGRABLE THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDM_ZERO_EXT_SMOOTH THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]);;

let PDM_INTEGRABLE_AFFINE_UNIV = prove
 (`!(f:real^M->real^N) c b.
        f integrable_on (:real^M) /\ ~(c = &0)
        ==> (\x. f(c % x + b)) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`; `c:real`; `b:real^M`]
                INTEGRABLE_AFFINITY) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN X_GEN_TAC `y:real^M` THEN
  EXISTS_TAC `c % y + b:real^M` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The transplant.  For w vanishing off cball(0,lam/4), the dilated map      *)
(* x -> w(lam (x - c)), c the centre of the cube, vanishes off the box       *)
(* [1/4,3/4]^N, so its periodization is smooth and agrees with it near the  *)
(* closed cube.                                                               *)
(* ------------------------------------------------------------------------- *)

let pdm_transplant = new_definition
 `pdm_transplant (lam:real) (w:real^N->real^K) =
    pdm_periodize (\x. w(lam % (x - inv(&2) % vec 1)))`;;

let PDM_TRANSPLANT_BOX = prove
 (`!lam (w:real^N->real^K).
        &0 < lam /\ (!z. lam / &4 < norm z ==> w z = vec 0)
        ==> !y. ~(y IN interval[(&1 / &4) % vec 1:real^N,(&1 - &1 / &4) % vec 1])
                ==> w(lam % (y - inv(&2) % vec 1)) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `abs((y - inv(&2) % vec 1:real^N)$j)` THEN
  REWRITE_TAC[COMPONENT_LE_NORM] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let PDM_TRANSPLANT_DILATE_SMOOTH = prove
 (`!lam (w:real^N->real^K).
        smooth_map_on (:real^N) w
        ==> smooth_map_on (:real^N) (\x. w(lam % (x - inv(&2) % vec 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. (w:real^N->real^K)(lam % (x - inv(&2) % vec 1))) =
    (\x. w(lam % x + --(lam % inv(&2) % vec 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC PDM_SMOOTH_AFFINE THEN ASM_REWRITE_TAC[]]);;

let PDM_TRANSPLANT_SMOOTH = prove
 (`!lam (w:real^N->real^K).
        smooth_map_on (:real^N) w /\ &0 < lam /\
        (!z. lam / &4 < norm z ==> w z = vec 0)
        ==> smooth_map_on (:real^N) (pdm_transplant lam w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pdm_transplant] THEN
  MATCH_MP_TAC PDM_PERIODIZE_SMOOTH THEN EXISTS_TAC `&1 / &4` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[PDM_TRANSPLANT_DILATE_SMOOTH]; REAL_ARITH_TAC; REAL_ARITH_TAC;
    REWRITE_TAC[] THEN MATCH_MP_TAC PDM_TRANSPLANT_BOX THEN ASM_REWRITE_TAC[]]);;

let PDM_TRANSPLANT_ZPER = prove
 (`!lam (w:real^N->real^K). pde_zper (pdm_transplant lam w)`,
  REWRITE_TAC[pdm_transplant; PDM_PERIODIZE_ZPER]);;

(* Values and partials near the closed cube. *)

let PDM_TRANSPLANT_EQ = prove
 (`!lam (w:real^N->real^K) x.
        &0 < lam /\ (!z. lam / &4 < norm z ==> w z = vec 0) /\
        x IN interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)
        ==> pdm_transplant lam w x = w(lam % (x - inv(&2) % vec 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pdm_transplant] THEN
  MP_TAC(ISPECL [`\x:real^N. (w:real^N->real^K)(lam % (x - inv(&2) % vec 1))`;
                 `&1 / &4`; `x:real^N`] PDM_PERIODIZE_EQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    REWRITE_TAC[] THEN MATCH_MP_TAC PDM_TRANSPLANT_BOX THEN ASM_REWRITE_TAC[]]);;

let PDM_TRANSPLANT_PARTIAL = prove
 (`!lam (w:real^N->real^K) l x.
        smooth_map_on (:real^N) w /\ &0 < lam /\
        (!z. lam / &4 < norm z ==> w z = vec 0) /\
        x IN interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)
        ==> iterated_partial l (pdm_transplant lam w) x =
            lam pow (LENGTH l) % iterated_partial l w (lam % (x - inv(&2) % vec 1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterated_partial l
                (\x:real^N. (w:real^N->real^K)(lam % x + --(lam % inv(&2) % vec 1))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(--(&1 / &4) % vec 1:real^N,(&1 + &1 / &4) % vec 1)` THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`lam:real`; `w:real^N->real^K`; `y:real^N`] PDM_TRANSPLANT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[PDM_ITERATED_PARTIAL_AFFINE] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    VECTOR_ARITH_TAC]);;

(* The torus norms of the transplant: each order picks up lam^(2|l| - N).   *)

let PDM_TRANSPLANT_HS2 = prove
 (`!lam (w:real^N->real^K) s.
        smooth_map_on (:real^N) w /\ &0 < lam /\
        (!z. lam / &4 < norm z ==> w z = vec 0)
        ==> pde_hs2 s (pdm_transplant lam w) =
            sum (pde_index_lists s (:N))
                (\l. lam pow (2 * LENGTH l) * inv(lam pow dimindex(:N)) *
                     drop(integral (:real^N)
                            (\z. lift(norm(iterated_partial l w z) pow 2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pdm_transplant] THEN
  MP_TAC(ISPECL [`\x:real^N. (w:real^N->real^K)(lam % (x - inv(&2) % vec 1))`;
                 `&1 / &4`; `s:num`] PDM_HS2_PERIODIZE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[PDM_TRANSPLANT_DILATE_SMOOTH]; REAL_ARITH_TAC; REAL_ARITH_TAC;
      REWRITE_TAC[] THEN MATCH_MP_TAC PDM_TRANSPLANT_BOX THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x:real^N. (w:real^N->real^K)(lam % (x - inv(&2) % vec 1))) =
    (\x. w(lam % x + --(lam % inv(&2) % vec 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PDM_ITERATED_PARTIAL_AFFINE; NORM_MUL; REAL_POW_MUL; REAL_ABS_POW;
               REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; LIFT_CMUL] THEN
  SUBGOAL_THEN
   `(\z. lift(norm(iterated_partial l (w:real^N->real^K) z) pow 2)) integrable_on (:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDM_SQNORM_PARTIAL_INTEGRABLE THEN
    EXISTS_TAC `cball(vec 0:real^N,lam / &4)` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift(norm(iterated_partial l (w:real^N->real^K) z) pow 2)`;
                 `lam:real`; `--(lam % inv(&2) % vec 1:real^N)`]
                PDM_INTEGRAL_AFFINE_UNIV) THEN
  MP_TAC(ISPECL [`\z. lift(norm(iterated_partial l (w:real^N->real^K) z) pow 2)`;
                 `lam:real`; `--(lam % inv(&2) % vec 1:real^N)`]
                PDM_INTEGRABLE_AFFINE_UNIV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_POW_POW] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sobolev embedding for maps with compact support in an open set.          *)
(* ------------------------------------------------------------------------- *)

let PDM_REAL_DIV_BOUND = prove
 (`!P A CT S1 S2 L. &0 < P /\ &0 <= CT /\ P * A <= CT * S1 /\ S1 <= (P * L) * S2
                   ==> A <= (CT * L) * S2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `P * A <= P * ((CT * L) * S2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CT * S1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CT * (P * L) * S2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let PDM_SOBOLEV_COMPACT = prove
 (`!k:real^N->bool.
        compact k
        ==> ?C. &0 < C /\
                !s (w:real^N->real^K) l z.
                    open s /\ k SUBSET s /\ smooth_map_on s w /\
                    (!y. y IN s /\ ~(y IN k) ==> w y = vec 0) /\
                    ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ z IN s
                    ==> norm(iterated_partial l w z) pow 2 <=
                        C * sum (pde_index_lists (dimindex(:N) + LENGTH l) (:N))
                                (\l'. drop(integral s
                                        (\y. lift(norm(iterated_partial l' w y) pow 2))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `CT:real` STRIP_ASSUME_TAC
    (INST_TYPE [`:K`,`:K`] PDE_TORUS_SOBOLEV_PARTIAL) THEN
  ABBREV_TAC `lam = &4 * (b + &1)` THEN
  SUBGOAL_THEN `&1 <= lam /\ &0 < lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `CT * lam pow dimindex(:N)` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `w:real^N->real^K`; `l:num list`; `z:real^N`] THEN
  STRIP_TAC THEN
  (* the integrals over s are those of the zero extension, and nonnegative *)
  ABBREV_TAC `we = \y:real^N. if y IN s then (w:real^N->real^K) y else vec 0` THEN
  SUBGOAL_THEN
   `!l'. integral s (\y. lift(norm(iterated_partial l' (w:real^N->real^K) y) pow 2)) =
         integral (:real^N) (\y. lift(norm(iterated_partial l' (we:real^N->real^K) y) pow 2)) /\
         &0 <= drop(integral s (\y. lift(norm(iterated_partial l' w y) pow 2)))`
  (LABEL_TAC "ints") THENL
   [X_GEN_TAC `l':num list` THEN EXPAND_TAC "we" THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`; `w:real^N->real^K`; `l':num list`]
                  PDM_ZERO_EXT_INTEGRAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum (pde_index_lists (dimindex(:N) + LENGTH(l:num list)) (:N))
              (\l'. drop(integral s
                      (\y. lift(norm(iterated_partial l' (w:real^N->real^K) y) pow 2))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `l':num list` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "ints" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `l':num list` th)]);
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^N) IN k` THENL
   [ALL_TAC;
    SUBGOAL_THEN `iterated_partial l (w:real^N->real^K) z = vec 0` SUBST1_TAC THENL
     [MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `k:real^N->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE;
                                                 REAL_POW_LE]]] THEN
  (* the zero extension and its transplant *)
  SUBGOAL_THEN `smooth_map_on (:real^N) (we:real^N->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "we" THEN MATCH_MP_TAC PDM_ZERO_EXT_SMOOTH THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. lam / &4 < norm y ==> (we:real^N->real^K) y = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "we" THEN
    SUBGOAL_THEN `~((y:real^N) IN k)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `norm(y:real^N) <= b` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `lam / &4 < norm(y:real^N)` THEN EXPAND_TAC "lam" THEN
      REAL_ARITH_TAC;
      COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `x = inv lam % z + inv(&2) % vec 1:real^N` THEN
  SUBGOAL_THEN `lam % (x - inv(&2) % vec 1) = z:real^N` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[VECTOR_ARITH `(a % z + c) - c:real^N = a % z`; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN interval(--(&1 / &4) % vec 1,(&1 + &1 / &4) % vec 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N)$j - inv(&2) = inv lam * (z:real^N)$j` ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((z:real^N)$j) <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:real^N)` THEN
      ASM_SIMP_TAC[COMPONENT_LE_NORM];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(inv lam * (z:real^N)$j) < &1 / &4` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
      EXPAND_TAC "lam" THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^N)$j - inv(&2) = inv lam * (z:real^N)$j` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the torus Sobolev inequality for the transplant at x *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`pdm_transplant lam (we:real^N->real^K)`;
                                `l:num list`; `x:real^N`]) THEN
  ASM_SIMP_TAC[PDM_TRANSPLANT_SMOOTH; PDM_TRANSPLANT_ZPER; PDM_TRANSPLANT_PARTIAL;
               PDM_TRANSPLANT_HS2] THEN
  SUBGOAL_THEN
   `iterated_partial l (we:real^N->real^K) z = iterated_partial l w z`
  SUBST1_TAC THENL
   [EXPAND_TAC "we" THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`; `w:real^N->real^K`;
                   `l:num list`; `z:real^N`] PDM_ZERO_EXT_PARTIAL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < lam ==> abs lam = lam`] THEN
  DISCH_TAC THEN MATCH_MP_TAC PDM_REAL_DIV_BOUND THEN
  EXISTS_TAC `lam pow LENGTH(l:num list) pow 2` THEN
  EXISTS_TAC
   `sum (pde_index_lists (dimindex(:N) + LENGTH(l:num list)) (:N))
      (\l. lam pow (2 * LENGTH l) * inv (lam pow dimindex (:N)) *
           drop (integral (:real^N)
                  (\z. lift (norm (iterated_partial l (we:real^N->real^K) z) pow 2))))` THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l':num list` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `LENGTH(l':num list) <= dimindex(:N) + LENGTH(l:num list)` ASSUME_TAC THENL
     [UNDISCH_TAC `l' IN pde_index_lists (dimindex(:N) + LENGTH(l:num list)) (:N)` THEN
      SIMP_TAC[pde_index_lists; IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[REAL_POW_POW; GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    USE_THEN "ints" (MP_TAC o SPEC `l':num list`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th); CONJUNCT2 th])]);;

(* ------------------------------------------------------------------------- *)
(* Jet bounds for compositions with a smooth map tau, with                   *)
(* smooth coefficients (Faa di Bruno type, by induction on the order with   *)
(* the coefficients universally quantified), and the instances for plain    *)
(* compositions and for pullbacks of matrix fields (mpullback), as used for *)
(* chart changes.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Linearity of iterated partials over finite sums on open sets: the same   *)
(* statement and proof as PDE_HEAT_ITERATED_PARTIAL_VSUM_OPEN (pc_pde_heat,  *)
(* not in this unit's load closure).                                         *)

let PDM_ITERATED_PARTIAL_VSUM_OPEN = prove
 (`!l s (g:A->real^M->real^N) ss.
      open s /\ FINITE ss /\ (!a. a IN ss ==> smooth_map_on s (g a))
      ==> !x. x IN s
              ==> iterated_partial l (\x. vsum ss (\a. g a x)) x =
                  vsum ss (\a. iterated_partial l (g a) x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ETA_AX] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\x. vsum ss (\a. iterated_partial t ((g:A->real^M->real^N) a) x)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`h:num`; `\a:A. iterated_partial t ((g:A->real^M->real^N) a)`;
                   `ss:A->bool`; `x:real^M`] PARTIAL_DERIVATIVE_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

(* The Frechet derivative in terms of the partials. *)

let PDM_FRECHET_PARTIALS = prove
 (`!(f:real^M->real^N) x h.
        f differentiable (at x)
        ==> frechet_derivative f (at x) h =
            vsum(1..dimindex(:M)) (\k. h$k % partial_derivative k f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TEXT_HAS_DERIVATIVE_PARTIALS) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

(* The forms H(y) = sum_q g(tau y)_q c_q(y): smoothness and first partials. *)

let PDM_FORM_SMOOTH = prove
 (`!s0 t0 (tau:real^N->real^M) (c:num->real^N->real^Q) (g:real^M->real^P).
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        smooth_map_on t0 g /\ (!q. smooth_map_on s0 (c q))
        ==> smooth_map_on s0 (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN SUBGOAL_THEN
   `(\y. ((g:real^M->real^P)((tau:real^N->real^M) y))$q % (c:num->real^N->real^Q) q y) =
    (\y. drop(((\x:real^P. lift(x$q)) o g o tau) y) % c q y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t0:real^M->bool` THEN
  ASM_REWRITE_TAC[]);;

let PDM_FORM_PARTIAL = prove
 (`!s0 t0 (tau:real^N->real^M) (c:num->real^N->real^Q) (g:real^M->real^P) i y.
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        smooth_map_on t0 g /\ (!q. smooth_map_on s0 (c q)) /\ y IN s0
        ==> partial_derivative i
              (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y)) y =
            vsum(1..dimindex(:P)) (\q. (g(tau y))$q % partial_derivative i (c q) y) +
            vsum(1..dimindex(:M))
              (\k. vsum(1..dimindex(:P))
                     (\q. (partial_derivative k g (tau y))$q %
                          ((partial_derivative i tau y)$k % c q y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(tau:real^N->real^M) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^M->real^P) differentiable (at ((tau:real^N->real^M) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t0:real^M->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. (c:num->real^N->real^Q) q differentiable (at y)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. (\y. lift(((g:real^M->real^P)((tau:real^N->real^M) y))$q)) differentiable (at y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\y. lift(((g:real^M->real^P)((tau:real^N->real^M) y))$q)) =
      (\x:real^P. lift(x$q)) o g o tau`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`;
                 `\q y. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                        (c:num->real^N->real^Q) q y`;
                 `1..dimindex(:P)`; `y:real^N`] PARTIAL_DERIVATIVE_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. ((g:real^M->real^P)((tau:real^N->real^M) y))$q`;
                   `(c:num->real^N->real^Q) q`; `y:real^N`] DIFFERENTIABLE_MUL_AT) THEN
    REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN 1..dimindex(:P)
        ==> partial_derivative i
              (\y. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                   (c:num->real^N->real^Q) q y) y =
            (g(tau y))$q % partial_derivative i (c q) y +
            vsum(1..dimindex(:M))
              (\k. (partial_derivative k g (tau y))$q %
                   ((partial_derivative i tau y)$k % c q y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`i:num`; `\y. lift(((g:real^M->real^P)((tau:real^N->real^M) y))$q)`;
                   `(c:num->real^N->real^Q) q`; `y:real^N`] PARTIAL_DERIVATIVE_MUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(\y. lift(((g:real^M->real^P)((tau:real^N->real^M) y))$q)) =
      (\y. lift(((g o tau) y)$q))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`i:num`; `q:num`; `(g:real^M->real^P) o (tau:real^N->real^M)`;
                   `y:real^N`] PARTIAL_DERIVATIVE_COMPONENT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`i:num`; `tau:real^N->real^M`; `g:real^M->real^P`; `y:real^N`]
                  PARTIAL_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[PDM_FRECHET_PARTIALS] THEN
    ASM_SIMP_TAC[VSUM_COMPONENT; FINITE_NUMSEG; GSYM VSUM_RMUL] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum(1..dimindex(:P))
      (\q. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
           partial_derivative i ((c:num->real^N->real^Q) q) y +
           vsum(1..dimindex(:M))
             (\k. (partial_derivative k g (tau y))$q %
                  ((partial_derivative i tau y)$k % c q y)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`\q k. (partial_derivative k (g:real^M->real^P) ((tau:real^N->real^M) y))$q %
           ((partial_derivative i tau y)$k % (c:num->real^N->real^Q) q y)`;
    `1..dimindex(:P)`; `1..dimindex(:M)`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN ACCEPT_TAC);;

(* The coefficients of the derivative of a form. *)

let PDM_COEFF2_SMOOTH = prove
 (`!s0 (tau:real^N->real^M) (c:real^N->real^Q) i j.
        open s0 /\ smooth_map_on s0 tau /\ smooth_map_on s0 c
        ==> smooth_map_on s0 (\y. (partial_derivative i tau y)$j % c y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. (partial_derivative i (tau:real^N->real^M) y)$j % (c:real^N->real^Q) y) =
    (\y. drop(((\x:real^M. lift(x$j)) o partial_derivative i tau) y) % c y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_SIMP_TAC[LINEAR_LIFT_COMPONENT; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* Iterated partials of the first partial of a form split into forms.       *)

let PDM_FORM_PARTIAL_ITERATED = prove
 (`!s0 t0 (tau:real^N->real^M) (c:num->real^N->real^Q) (g:real^M->real^P) i l y.
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        smooth_map_on t0 g /\ (!q. smooth_map_on s0 (c q)) /\ y IN s0
        ==> iterated_partial l
              (partial_derivative i
                 (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % c q y))) y =
            iterated_partial l
              (\y. vsum(1..dimindex(:P)) (\q. (g(tau y))$q % partial_derivative i (c q) y)) y +
            vsum(1..dimindex(:M))
              (\j. iterated_partial l
                     (\y. vsum(1..dimindex(:P))
                            (\q. (partial_derivative j g (tau y))$q %
                                 ((partial_derivative i tau y)$j % c q y))) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on s0
      (\y. vsum(1..dimindex(:P))
             (\q. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                  partial_derivative i ((c:num->real^N->real^Q) q) y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                   `\q. partial_derivative i ((c:num->real^N->real^Q) q)`;
                   `g:real^M->real^P`] PDM_FORM_SMOOTH) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. smooth_map_on s0
         (\y. vsum(1..dimindex(:P))
                (\q. (partial_derivative j (g:real^M->real^P) ((tau:real^N->real^M) y))$q %
                     ((partial_derivative i tau y)$j % (c:num->real^N->real^Q) q y)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                   `\q y. (partial_derivative i (tau:real^N->real^M) y)$j %
                          (c:num->real^N->real^Q) q y`;
                   `partial_derivative j (g:real^M->real^P)`] PDM_FORM_SMOOTH) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; PDM_COEFF2_SMOOTH; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `iterated_partial l
      (\y. vsum(1..dimindex(:P))
             (\q. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                  partial_derivative i ((c:num->real^N->real^Q) q) y) +
           vsum(1..dimindex(:M))
             (\j. vsum(1..dimindex(:P))
                    (\q. (partial_derivative j g (tau y))$q %
                         ((partial_derivative i tau y)$j % c q y)))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC PDM_FORM_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`s0:real^N->bool`; `t0:real^M->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`l:num list`; `s0:real^N->bool`;
    `\y. vsum(1..dimindex(:P))
           (\q. ((g:real^M->real^P)((tau:real^N->real^M) y))$q %
                partial_derivative i ((c:num->real^N->real^Q) q) y)`;
    `\y. vsum(1..dimindex(:M))
           (\j. vsum(1..dimindex(:P))
                  (\q. (partial_derivative j (g:real^M->real^P) ((tau:real^N->real^M) y))$q %
                       ((partial_derivative i tau y)$j % (c:num->real^N->real^Q) q y)))`]
   PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`l:num list`; `s0:real^N->bool`;
    `\j y. vsum(1..dimindex(:P))
             (\q. (partial_derivative j (g:real^M->real^P) ((tau:real^N->real^M) y))$q %
                  ((partial_derivative i tau y)$j % (c:num->real^N->real^Q) q y))`;
    `1..dimindex(:M)`] PDM_ITERATED_PARTIAL_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[]);;

(* The jet bound for forms, by induction on the order, the coefficients     *)
(* being universally quantified (the innermost derivative is split off).    *)

let PDM_COMPOSE_JET_BOUND = prove
 (`!s0 t0 (tau:real^N->real^M) k.
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        compact k /\ k SUBSET s0
        ==> !n (c:num->real^N->real^Q).
              (!q. smooth_map_on s0 (c q))
              ==> ?C. &0 <= C /\
                      !(g:real^M->real^P) l y.
                          smooth_map_on t0 g /\ LENGTH l = n /\
                          ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ y IN k
                          ==> norm(iterated_partial l
                                     (\y. vsum(1..dimindex(:P))
                                            (\q. (g(tau y))$q % c q y)) y)
                              <= C * pde_jetn n g (tau y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [X_GEN_TAC `c:num->real^N->real^Q` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!q. ?B. !y. y IN k ==> norm((c:num->real^N->real^Q) q y) <= B`
    MP_TAC THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`s0:real^N->bool`; `(c:num->real^N->real^Q) q`; `k:real^N->bool`;
                     `[]:num list`] PDE_SMOOTH_PARTIAL_BOUNDED) THEN
      ASM_REWRITE_TAC[iterated_partial];
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `B:num->real`) THEN
    EXISTS_TAC `sum(1..dimindex(:P)) (\q. abs((B:num->real) q))` THEN
    SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_ABS_POS] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN
    MAP_EVERY X_GEN_TAC [`g:real^M->real^P`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[iterated_partial; pde_jetn; PDE_INDEX_LISTS_0; SUM_SING] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:P))
                  (\q. norm((g:real^M->real^P)((tau:real^N->real^M) y)) *
                       abs((B:num->real) q))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; COMPONENT_LE_NORM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B:num->real) q` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `c:num->real^N->real^Q` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?C1. &0 <= C1 /\
             !(g:real^M->real^P) l y.
                smooth_map_on t0 g /\ LENGTH l = n /\
                ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ y IN k
                ==> norm(iterated_partial l
                           (\y. vsum(1..dimindex(:P))
                                  (\q. (g((tau:real^N->real^M) y))$q %
                                       partial_derivative i ((c:num->real^N->real^Q) q) y)) y)
                    <= C1 * pde_jetn n g (tau y)`
  MP_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `\q. partial_derivative i ((c:num->real^N->real^Q) q)`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `C1:num->real`)] THEN
  SUBGOAL_THEN
   `!i j. ?C2. &0 <= C2 /\
               !(g:real^M->real^P) l y.
                  smooth_map_on t0 g /\ LENGTH l = n /\
                  ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ y IN k
                  ==> norm(iterated_partial l
                             (\y. vsum(1..dimindex(:P))
                                    (\q. (g((tau:real^N->real^M) y))$q %
                                         ((partial_derivative i tau y)$j %
                                          (c:num->real^N->real^Q) q y))) y)
                      <= C2 * pde_jetn n g (tau y)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `\q y. (partial_derivative i (tau:real^N->real^M) y)$j %
                                     (c:num->real^N->real^Q) q y`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PDM_COEFF2_SMOOTH; ETA_AX];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `C2:num->num->real`)] THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. (C1:num->real) i + sum(1..dimindex(:M)) (\j. (C2:num->num->real) i j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real^M->real^P`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l0 i. l = APPEND l0 [i:num]` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `BUTLAST(l:num list)` THEN EXISTS_TAC `LAST(l:num list)` THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC APPEND_BUTLAST_LAST THEN
    DISCH_TAC THEN UNDISCH_TAC `LENGTH(l:num list) = SUC n` THEN
    ASM_REWRITE_TAC[LENGTH; NOT_SUC];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL]) THEN
  SUBGOAL_THEN `LENGTH(l0:num list) = n` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(l0:num list) + SUC 0 = SUC n` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC o
    check (fun th -> can (term_match [] `ALL P (l0:num list) /\ Q`) (concl th))) THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `t0:real^M->bool`; `tau:real^N->real^M`;
                 `c:num->real^N->real^Q`; `g:real^M->real^P`; `i:num`; `l0:num list`;
                 `y:real^N`] PDM_FORM_PARTIAL_ITERATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `((C1:num->real) i + sum(1..dimindex(:M)) (\j. (C2:num->num->real) i j)) *
    pde_jetn (SUC n) (g:real^M->real^P) ((tau:real^N->real^M) y)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PDE_JETN_POS] THEN
    MP_TAC(ISPECL
     [`{i:num}`; `1..dimindex(:N)`;
      `\i. (C1:num->real) i + sum(1..dimindex(:M)) (\j. (C2:num->num->real) i j)`]
     SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[FINITE_NUMSEG; SUM_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG; IN_DIFF] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i':num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:real^Q) <= x /\ norm(b:real^Q) <= y ==> norm(a + b) <= x + y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C1:num->real) i * pde_jetn n (g:real^M->real^P) ((tau:real^N->real^M) y)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_JETN_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C2:num->num->real) i j *
              pde_jetn n (partial_derivative j (g:real^M->real^P)) ((tau:real^N->real^M) y)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o
      check (fun th -> can (term_match [] `!i j. &0 <= (C2:num->num->real) i j /\ P`)
                           (concl th))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PDE_JETN_PARTIAL THEN ASM_REWRITE_TAC[]]);;

(* Plain compositions. *)

let PDM_COMPOSE_JET_BOUND_PLAIN = prove
 (`!s0 t0 (tau:real^N->real^M) k.
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        compact k /\ k SUBSET s0
        ==> !n. ?C. &0 <= C /\
                    !(g:real^M->real^P) l y.
                        smooth_map_on t0 g /\ LENGTH l = n /\
                        ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ y IN k
                        ==> norm(iterated_partial l (\y. g(tau y)) y)
                            <= C * pde_jetn n g (tau y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`n:num`; `\q:num y:real^N. basis q:real^P`] o
    MATCH_MP PDM_COMPOSE_JET_BOUND) THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; BASIS_EXPANSION; ETA_AX]);;

(* Pullbacks of matrix fields: vectorize(J^T G(tau y) J) as a form.         *)

let PDM_LINEAR_CONGRUENCE = prove
 (`!(A:real^N^N) (B:real^N^N).
        linear (\v:real^(N,N)finite_prod.
                  (vectorize:real^N^N->real^(N,N)finite_prod)
                    (A ** (matrify v:real^N^N) ** B))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_LDISTRIB;
              MATRIX_ADD_RDISTRIB; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              VECTORIZE_ADD; VECTORIZE_CMUL]);;

let PDM_MPULLBACK_FORM = prove
 (`!(tau:real^N->real^N) (G:real^N->real^N^N) y.
        (vectorize:real^N^N->real^(N,N)finite_prod) (mpullback tau G y) =
        vsum(1..dimindex(:(N,N)finite_prod))
          (\q. (((vectorize:real^N^N->real^(N,N)finite_prod) o G) (tau y))$q %
               (vectorize:real^N^N->real^(N,N)finite_prod)
                 (transp(matrix(frechet_derivative tau (at y))) **
                  (matrify(basis q):real^N^N) **
                  matrix(frechet_derivative tau (at y))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  MP_TAC(ISPECL
   [`\v:real^(N,N)finite_prod.
       (vectorize:real^N^N->real^(N,N)finite_prod)
         (transp(matrix(frechet_derivative (tau:real^N->real^N) (at y))) **
          (matrify v:real^N^N) ** matrix(frechet_derivative tau (at y)))`;
    `1..dimindex(:(N,N)finite_prod)`;
    `\q. ((vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N)
            ((tau:real^N->real^N) y)))$q`;
    `basis:num->real^(N,N)finite_prod`] LINEAR_VSUM_MUL) THEN
  REWRITE_TAC[PDM_LINEAR_CONGRUENCE; FINITE_NUMSEG; BASIS_EXPANSION; MATRIFY_VECTORIZE] THEN
  DISCH_THEN(fun th -> ACCEPT_TAC th));;

let PDM_PULLBACK_COEFF_SMOOTH = prove
 (`!s0 (tau:real^N->real^N) (E:real^N^N).
        open s0 /\ smooth_map_on s0 tau
        ==> smooth_map_on s0
              (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (transp(matrix(frechet_derivative tau (at y))) ** E **
                      matrix(frechet_derivative tau (at y))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s0:real^N->bool`;
                 `\y. transp(matrix(frechet_derivative (tau:real^N->real^N) (at y)))`;
                 `\y. (E:real^N^N) ** matrix(frechet_derivative (tau:real^N->real^N) (at y))`]
                LRG_SMOOTH_MATMUL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s0:real^N->bool`;
                   `\y. matrix(frechet_derivative (tau:real^N->real^N) (at y))`]
                  LRG_SMOOTH_TRANSP) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`] LRG_SMOOTH_JACOBIAN) THEN
    ASM_REWRITE_TAC[o_DEF];
    MP_TAC(ISPECL [`s0:real^N->bool`; `\y:real^N. E:real^N^N`;
                   `\y. matrix(frechet_derivative (tau:real^N->real^N) (at y))`]
                  LRG_SMOOTH_MATMUL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`s0:real^N->bool`; `tau:real^N->real^N`] LRG_SMOOTH_JACOBIAN) THEN
    ASM_REWRITE_TAC[o_DEF]]);;

let PDM_PULLBACK_JET_BOUND = prove
 (`!s0 t0 (tau:real^N->real^N) k.
        open s0 /\ open t0 /\ smooth_map_on s0 tau /\ IMAGE tau s0 SUBSET t0 /\
        compact k /\ k SUBSET s0
        ==> !n. ?C. &0 <= C /\
                    !(G:real^N->real^N^N) l y.
                        smooth_map_on t0 ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
                        LENGTH l = n /\
                        ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ y IN k
                        ==> norm(iterated_partial l
                                   ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                    mpullback tau G) y)
                            <= C * pde_jetn n ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                              (tau y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o ISPECL
   [`n:num`;
    `\q y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (transp(matrix(frechet_derivative (tau:real^N->real^N) (at y))) **
              (matrify(basis q):real^N^N) **
              matrix(frechet_derivative tau (at y)))`] o
    MATCH_MP (INST_TYPE [`:(N,N)finite_prod`,`:P`] PDM_COMPOSE_JET_BOUND)) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PDM_PULLBACK_COEFF_SMOOTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o REWRITE_RULE[]) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`G:real^N->real^N^N`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
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
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chart pieces psi_i v of a tensor field, the chart-wise                *)
(* norm pde_mnorm2 (sign, domination of its terms), the Sobolev bound in a  *)
(* chart of the cover, the change from chart i to a chart j whose cutoff is *)
(* 1 near a point, and the Sobolev embedding PDE_MNORM_SOBOLEV.              *)
(* ------------------------------------------------------------------------- *)

(* Chart facts in the pair-free form used by pde_cover and pde_mnorm2.       *)

let PDM_CHART_INV_C = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> (!x. x IN FST c ==> chart_inv c (SND c x) = x) /\
            (!y. y IN IMAGE (SND c) (FST c)
                 ==> chart_inv c y IN FST c /\ SND c (chart_inv c y) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR]);;

let PDM_CHART_OPEN_C = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> open_in top (FST c) /\ open (IMAGE (SND c) (FST c)) /\
            FST c SUBSET topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[OPEN_IN_SUBSET]);;

(* The chart piece of psi v in the chart c: smooth on the chart image and   *)
(* zero off the piece k when psi vanishes off the image of k.               *)

let PDM_CHART_PIECE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (psi:A->real) (v:A->real^N^N) k.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        mfd_smooth atlas (\x. lift(psi x)) /\ pde_tensor_smooth atlas v /\
        k SUBSET IMAGE (SND c) (FST c) /\
        (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) k)
        ==> smooth_map_on (IMAGE (SND c) (FST c))
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (psi (chart_inv c z) %% metric_local atlas c v z)) /\
            (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN k)
                 ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                       (psi (chart_inv c z) %% metric_local atlas c v z) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[VECTORIZE_CMUL] THEN
    SUBGOAL_THEN
     `(\z. psi (chart_inv (c:(A->bool)#(A->real^N)) z) %
           (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas c (v:A->real^N^N) z)) =
      (\z. drop(((\x:A. lift(psi x)) o chart_inv c) z) %
           ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c v) z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(psi x))` THEN
      REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `pde_tensor_smooth atlas (v:A->real^N^N)` THEN
      REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `psi(chart_inv (c:(A->bool)#(A->real^N)) z) = &0`
      (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LZERO; VECTORIZE_0]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv (c:(A->bool)#(A->real^N)) z`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) = y` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) (chart_inv c z)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

(* Terms of the chart-wise norm: sign, and domination by the norm.           *)

let PDM_MNORM2_TERMS = prove
 (`!top atlas n0 cs ks psi (v:A->real^N^N) s.
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
        pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        pde_tensor_smooth atlas v
        ==> (!j l. j < n0
                   ==> &0 <= drop(integral (IMAGE (SND(cs j)) (FST(cs j)))
                               (\y. lift(norm(iterated_partial l
                                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                           (psi j (chart_inv (cs j) z) %%
                                            metric_local atlas (cs j) v z)) y) pow 2)))) /\
            &0 <= pde_mnorm2 atlas n0 cs psi s v /\
            (!j s'. j < n0 /\ s' <= s
                    ==> sum (pde_index_lists s' (:N))
                          (\l. drop(integral (IMAGE (SND(cs j)) (FST(cs j)))
                                 (\y. lift(norm(iterated_partial l
                                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                             (psi j (chart_inv (cs j) z) %%
                                              metric_local atlas (cs j) v z)) y) pow 2))))
                        <= pde_mnorm2 atlas n0 cs psi s v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j l. j < n0
          ==> &0 <= drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
                      (\y. lift(norm(iterated_partial l
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (psi j (chart_inv (cs j) z) %%
                                   metric_local atlas (cs j) (v:A->real^N^N) z)) y) pow 2)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                           (ks:num->real^N->bool)` THEN
    UNDISCH_TAC `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                             (psi:num->A->real)` THEN
    REWRITE_TAC[pde_cover; pde_cutoffs] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) j`; `(psi:num->A->real) j`;
                   `v:A->real^N^N`; `(ks:num->real^N->bool) j`] PDM_CHART_PIECE) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                   `(ks:num->real^N->bool) j`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                          metric_local atlas (cs j) (v:A->real^N^N) z)`;
                   `l:num list`] PDM_ZERO_EXT_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j s. j < n0
          ==> &0 <= sum (pde_index_lists s (:N))
                     (\l. drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
                            (\y. lift(norm(iterated_partial l
                                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                        (psi j (chart_inv (cs j) z) %%
                                         metric_local atlas (cs j) (v:A->real^N^N) z)) y)
                                   pow 2))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `s':num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (pde_index_lists s (:N))
      (\l. drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j)))
             (\y. lift(norm(iterated_partial l
                    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         (psi j (chart_inv (cs j) z) %%
                          metric_local atlas (cs j) (v:A->real^N^N) z)) y) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO];
    ALL_TAC] THEN
  REWRITE_TAC[pde_mnorm2] THEN
  MP_TAC(ISPECL
   [`{j:num}`; `{i:num | i < n0}`;
    `\i. sum (pde_index_lists s (:N))
          (\l. drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                 (\y. lift(norm(iterated_partial l
                        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (psi i (chart_inv (cs i) z) %%
                              metric_local atlas (cs i) (v:A->real^N^N) z)) y) pow 2))))`]
   SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SUBSET; IN_SING; IN_ELIM_THM; IN_DIFF]);;

(* Sobolev in a chart of the cover, for the chart pieces psi_j v. *)

let PDM_MNORM_CHART_SOBOLEV = prove
 (`!top atlas n0 cs ks psi m.
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
        pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
        ==> !j. j < n0
                ==> ?C. &0 < C /\
                        !(v:A->real^N^N) l z.
                           pde_tensor_smooth atlas v /\
                           ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\ LENGTH l <= m /\
                           z IN IMAGE (SND(cs j)) (FST(cs j))
                           ==> norm(iterated_partial l
                                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                           (psi j (chart_inv (cs j) z) %%
                                            metric_local atlas (cs j) v z)) z) pow 2
                               <= C * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\ compact((ks:num->real^N->bool) j) /\
    ks j SUBSET IMAGE (SND(cs j)) (FST(cs j)) /\
    mfd_smooth atlas (\x. lift((psi:num->A->real) j x))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pde_cover; pde_cutoffs]; ALL_TAC] THEN
  MP_TAC(ISPEC `(ks:num->real^N->bool) j`
               (INST_TYPE [`:(N,N)finite_prod`,`:K`] PDM_SOBOLEV_COMPACT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:A->real^N^N`; `l:num list`; `z:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`; `(psi:num->A->real) j`;
                 `v:A->real^N^N`; `(ks:num->real^N->bool) j`] PDM_CHART_PIECE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
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
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `v:A->real^N^N`; `m + dimindex(:N)`]
                PDM_MNORM2_TERMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Change of chart where the cutoff of the target chart is 1.               *)

let PDM_CHART_CHANGE_PIECE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' (psi:A->real) (v:A->real^N^N) V z.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        (!x. x IN V ==> psi x = &1) /\
        z IN IMAGE (SND c) (FST c INTER FST c' INTER V)
        ==> metric_local atlas c v z =
            mpullback (chart_trans c c')
              (\y. (matrify:real^(N,N)finite_prod->real^N^N)
                     ((vectorize:real^N^N->real^(N,N)finite_prod)
                        (psi (chart_inv c' y) %% metric_local atlas c' v y))) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `v:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback; MATRIFY_VECTORIZE] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `x:A`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_SIMP_TAC[MATRIX_CMUL_LID]);;

(* Local bounds on a compact set give a global bound (for bounds monotone   *)
(* in the constant).                                                         *)

let PDM_COMPACT_LOCAL_BOUND = prove
 (`!(k:real^N->bool) (P:real->real^N->bool).
        compact k /\ (!C C' y. P C y /\ C <= C' ==> P C' y) /\
        (!y0. y0 IN k ==> ?r C. &0 < r /\ !y. y IN k /\ y IN ball(y0,r) ==> P C y)
        ==> ?C. !y. y IN k ==> P C y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real` (X_CHOOSE_TAC `CC:real^N->real`)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\y0:real^N. ball(y0,r y0)) k`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `y:real^N` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?FF. FINITE FF /\ FF SUBSET k /\ f = IMAGE (\y0:real^N. ball(y0,r y0)) FF`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FINITE_SUBSET_IMAGE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CC:real^N->real`; `FF:real^N->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `a:real` THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?y0:real^N. y0 IN FF /\ y IN ball(y0,r y0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k SUBSET UNIONS (f:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "mono" MATCH_MP_TAC THEN
  EXISTS_TAC `(CC:real^N->real) y0` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `(y0:real^N) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Squares of jets bounded termwise. *)

let PDM_JETN_SQ_BOUND = prove
 (`!m (w:real^N->real^Q) x B.
        &0 <= B /\
        (!l. l IN pde_index_lists m (:N) ==> norm(iterated_partial l w x) pow 2 <= B)
        ==> pde_jetn m w x <= &(CARD(pde_index_lists m (:N))) * sqrt B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_SIMP_TAC[]);;

(* The bound near a point of a piece, through a chart whose cutoff is 1     *)
(* near the point.                                                           *)

let PDM_MNORM_LOCAL = prove
 (`!top atlas n0 cs ks psi m i y0.
        smooth_manifold_atlas top atlas /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        i < n0 /\ y0 IN ks i
        ==> ?r C. &0 < r /\
                  !y. y IN ks i /\ y IN ball(y0,r)
                      ==> !(v:A->real^N^N) l.
                             pde_tensor_smooth atlas v /\ l IN pde_index_lists m (:N)
                             ==> norm(iterated_partial l
                                        ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                         metric_local atlas (cs i) v) y) pow 2
                                 <= C * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
    ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                           (ks:num->real^N->bool)` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `x0 = chart_inv ((cs:num->(A->bool)#(A->real^N)) i) y0` THEN
  SUBGOAL_THEN `(x0:A) IN FST((cs:num->(A->bool)#(A->real^N)) i) /\
                SND(cs i) x0 = y0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "x0" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?j V. j < n0 /\ open_in top V /\ (x0:A) IN V /\
          !z. z IN V ==> (psi:num->A->real) j z = &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                             (psi:num->A->real)` THEN
    REWRITE_TAC[pde_cutoffs] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) j IN atlas /\
    (ks:num->real^N->bool) j SUBSET IMAGE (SND(cs j)) (FST(cs j))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                           (ks:num->real^N->bool)` THEN
    REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x0:A) IN FST((cs:num->(A->bool)#(A->real^N)) j)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x0:A) IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) j))
                                  ((ks:num->real^N->bool) j)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> can (term_match [] `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                                                  ==> P i x`) (concl th))) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i))
              (FST(cs i) INTER FST(cs j) INTER (V:A->bool))` THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ (y0:real^N) IN W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((cs:num->(A->bool)#(A->real^N)) i)`; `SND((cs:num->(A->bool)#(A->real^N)) i)`;
                     `FST((cs:num->(A->bool)#(A->real^N)) i) INTER FST(cs j) INTER (V:A->bool)`]
                    CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tau = chart_trans ((cs:num->(A->bool)#(A->real^N)) i) (cs j)` THEN
  SUBGOAL_THEN `smooth_map_on (W:real^N->bool) (tau:real^N->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i) INTER FST(cs j))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      EXPAND_TAC "tau" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((cs:num->(A->bool)#(A->real^N)) i)`; `SND((cs:num->(A->bool)#(A->real^N)) i)`;
                     `FST((cs:num->(A->bool)#(A->real^N)) j)`; `SND((cs:num->(A->bool)#(A->real^N)) j)`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (tau:real^N->real^N) W SUBSET IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN EXPAND_TAC "tau" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST((cs:num->(A->bool)#(A->real^N)) i)`; `SND((cs:num->(A->bool)#(A->real^N)) i)`;
                   `FST((cs:num->(A->bool)#(A->real^N)) j)`; `SND((cs:num->(A->bool)#(A->real^N)) j)`;
                   `x:A`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the jet bound for the pullback by tau on cball(y0,r) *)
  MP_TAC(ISPECL [`W:real^N->bool`;
                 `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) j)) (FST(cs j))`;
                 `tau:real^N->real^N`; `cball(y0:real^N,r)`] PDM_PULLBACK_JET_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_TAC `CP:num->real` o REWRITE_RULE[SKOLEM_THM]) THEN
  (* the Sobolev bound in chart j *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `psi:num->A->real`; `m:num`] PDM_MNORM_CHART_SOBOLEV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cj:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  EXISTS_TAC `r:real` THEN
  EXISTS_TAC `(sum(0..m) (CP:num->real) * &(CARD(pde_index_lists m (:N)))) pow 2 * Cj` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`v:A->real^N^N`; `l:num list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(l:num list) <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:num list) IN pde_index_lists m (:N)` THEN
    SIMP_TAC[pde_index_lists; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN W` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= pde_mnorm2 atlas n0 cs (psi:num->A->real) (m + dimindex(:N)) (v:A->real^N^N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `v:A->real^N^N`; `m + dimindex(:N)`]
                  PDM_MNORM2_TERMS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) j`; `(psi:num->A->real) j`;
                 `v:A->real^N^N`; `(ks:num->real^N->bool) j`] PDM_CHART_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pde_cutoffs (top:A topology,atlas:((A->bool)#(A->real^N))->bool) n0 cs
                               (psi:num->A->real)` THEN
      REWRITE_TAC[pde_cutoffs] THEN DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[]];
    STRIP_TAC] THEN
  (* the chart change on W *)
  SUBGOAL_THEN
   `iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                     (v:A->real^N^N)) y =
    iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
       mpullback (tau:real^N->real^N)
         (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                ((vectorize:real^N^N->real^(N,N)finite_prod)
                   ((psi:num->A->real) j (chart_inv (cs j) z) %%
                    metric_local atlas (cs j) v z)))) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN EXPAND_TAC "tau" THEN
    MATCH_MP_TAC PDM_CHART_CHANGE_PIECE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `V:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = sum(0..m) (CP:num->real)` THEN
  ABBREV_TAC `KK = &(CARD(pde_index_lists m (:N)))` THEN
  SUBGOAL_THEN `&0 <= S /\ &0 <= KK /\ (CP:num->real) (LENGTH(l:num list)) <= S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "KK" THEN REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`{LENGTH(l:num list)}`; `0..m`; `CP:num->real`] SUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; IN_SING; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `MM = pde_mnorm2 atlas n0 cs (psi:num->A->real) (m + dimindex(:N)) (v:A->real^N^N)` THEN
  SUBGOAL_THEN
   `norm(iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
       mpullback (tau:real^N->real^N)
         (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                ((vectorize:real^N^N->real^(N,N)finite_prod)
                   ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                    metric_local atlas (cs j) (v:A->real^N^N) z)))) y)
    <= S * (KK * sqrt(Cj * MM))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `(CP:num->real) (LENGTH(l:num list)) *
      pde_jetn (LENGTH l)
        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                metric_local atlas (cs j) (v:A->real^N^N) z))
        ((tau:real^N->real^N) y)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH(l:num list)` o
        check (fun th -> can (term_match [] `!n. &0 <= (CP:num->real) n /\ Q n`) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`\z. (matrify:real^(N,N)finite_prod->real^N^N)
               ((vectorize:real^N^N->real^(N,N)finite_prod)
                  ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                   metric_local atlas (cs j) (v:A->real^N^N) z))`;
        `l:num list`; `y:real^N`] o CONJUNCT2) THEN
      REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PDE_JETN_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `pde_jetn m
        (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               ((psi:num->A->real) j (chart_inv ((cs:num->(A->bool)#(A->real^N)) j) z) %%
                metric_local atlas (cs j) (v:A->real^N^N) z))
        ((tau:real^N->real^N) y)` THEN
    ASM_SIMP_TAC[PDE_JETN_MONO] THEN EXPAND_TAC "KK" THEN
    MATCH_MP_TAC PDM_JETN_SQ_BOUND THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `l':num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
    STRIP_TAC THEN EXPAND_TAC "MM" THEN
    USE_THEN "sob" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(S * (KK * sqrt(Cj * MM))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]);;

(* Sobolev embedding on M for the chart-wise norms.                          *)

let PDE_MNORM_SOBOLEV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi m.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
        ==> ?C. !(v:A->real^N^N) i l y.
                  pde_tensor_smooth atlas v /\ i < n0 /\ l IN pde_index_lists m (:N) /\
                  y IN ks i
                  ==> norm(iterated_partial l
                             ((vectorize:real^N^N->real^(N,N)finite_prod) o
                              metric_local atlas (cs i) v) y) pow 2 <=
                      C * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!C C' (v:A->real^N^N) X.
        pde_tensor_smooth atlas v /\ X <= C * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v /\
        C <= C'
        ==> X <= C' * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * pde_mnorm2 atlas n0 cs (psi:num->A->real) (m + dimindex(:N))
                                (v:A->real^N^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                   `psi:num->A->real`; `v:A->real^N^N`; `m + dimindex(:N)`]
                  PDM_MNORM2_TERMS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?C. i < n0
            ==> !y. y IN ks i
                    ==> !(v:A->real^N^N) l.
                           pde_tensor_smooth atlas v /\ l IN pde_index_lists m (:N)
                           ==> norm(iterated_partial l
                                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                       metric_local atlas (cs i) v) y) pow 2 <=
                               C * pde_mnorm2 atlas n0 cs psi (m + dimindex(:N)) v`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`(ks:num->real^N->bool) i`;
      `\C y. !(v:A->real^N^N) l.
                pde_tensor_smooth atlas v /\ l IN pde_index_lists m (:N)
                ==> norm(iterated_partial l
                           ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) v) y) pow 2 <=
                    C * pde_mnorm2 atlas n0 cs (psi:num->A->real) (m + dimindex(:N)) v`]
     PDM_COMPACT_LOCAL_BOUND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[pde_cover];
      REPEAT STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
      EXISTS_TAC `C:real` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC PDM_MNORM_LOCAL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `CC:num->real`) THEN
  MP_TAC(ISPECL [`CC:num->real`; `{i:num | i < n0}`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`v:A->real^N^N`; `i:num`; `l:num list`; `y:real^N`] THEN
  STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
  EXISTS_TAC `(CC:num->real) i` THEN ASM_SIMP_TAC[]);;

