(* ========================================================================= *)
(* pc_p2b_x0r (Part 2B, a step of SPLIT_ROUND): bounded slices for an        *)
(* ancient flow with a global unit split field.  Main theorem:               *)
(*   P2B_GSPLIT_SLICE_BOUND_ROUTE |- !w. P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT w *)
(* i.e. ANCIENT_COMPACT /\ POINT /\ ORBIT (pc_p2b_parlimreq) ==> every slice *)
(* g(s1), s1 < b, of a p2b_ancflow0 flow with a p2b_gsplit field X has       *)
(* bounded scalar curvature.  The LIM theorems are used as proved theorems   *)
(* (pc_p2b_x0lim).  Route: unbounded R gives picked points moved along the   *)
(* X-orbits to almost minimise the distance to p, almost-line pairs whose    *)
(* near point lies on a segment to p, the X0 limit and its slice at time 0,  *)
(* a unit vector v with Ric(v,v) = 0 and the limit geodesic of v (POINT,     *)
(* ORBIT), a line whose ray stays far from geo(xl,v,d) and geo(xl,v,-d), so  *)
(* v is orthogonal to the splitting field of the line (Busemann function),   *)
(* hence R(xl) = 0 at time 0, against R(xl) = 1.                             *)
(* Sections: curvature algebra (R = 0 from two killed directions;            *)
(* Ric(X,.) = 0); Busemann orthogonality; shifted points; far pair and       *)
(* almost pairs with the segment property (copies of the pc_p2b_x0 proofs    *)
(* with one more conclusion); pairs and the line with the far points; exact  *)
(* limit pairs; assembly lemmas (including P2BX0R_FLOW_TO_SLICE_AT, a copy   *)
(* of P2BU_FLOW_TO_SLICE_AT of pc_p2c_blowup2, which is outside the load     *)
(* closure of this unit); the statements, the assembly and the route.        *)
(* ========================================================================= *)

needs "src/pc_p2b_x0lim.ml";;
needs "src/pc_p2b_kfl.ml";;
needs "src/pc_p2b_parlimreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* X0R.C1 The final algebra (dimension 3): if e lies in planes of zero      *)
(* sectional curvature only and the unit w orthogonal to e has Ric(w,w) = 0, *)
(* then R = 0 (sec(f,e) = P(w,w) = R/2 - Ric(w,w) for the orthonormal       *)
(* triple f, e, w; RFA_LSECTIONAL_PCURV_3D, RFA_LPCURV_DIAG).               *)

let P2BX0R_LSCALAR_ZERO = prove
 (`!U (G:real^3->real^3^3) y e w.
     metric_field U G /\ y IN U /\
     e dot (G y ** e) = &1 /\ w dot (G y ** w) = &1 /\ e dot (G y ** w) = &0 /\
     (!u. ~collinear {vec 0,u,e} ==> lsectional G y u e = &0) /\
     lricci G y w w = &0
     ==> lscalar G y = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`; `w:real^3`]
                RFA_NORMAL3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `f:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^3) dot ((G:real^3->real^3^3) y ** e) = &0 /\
                (f:real^3) dot ((G:real^3->real^3^3) y ** w) = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(fun (asl,w) -> let l,r = dest_eq w in
      let a,_ = dest_binary "dot" l in
      let _,b = dest_binary "matrix_vector_mul" (rand l) in
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; a; b] LRG_METRIC_SYM)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `f:real^3`; `e:real^3`; `w:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
  ASM_REWRITE_TAC[RFA_LPCURV_DIAG; REAL_MUL_RID; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `lsectional (G:real^3->real^3^3) y f e = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
    EXISTS_TAC `(G:real^3->real^3^3) y` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* X0R.C2 The manifold form: a unit parallel field X and a unit vector v    *)
(* g-orthogonal to X(x) with Ric(v,v) = 0 force R(x) = 0 (P2BX0_PAR_SEC_ZERO *)
(* and P2BX0R_LSCALAR_ZERO in the chart at x).                              *)

let P2BX0R_SCALAR_ZERO = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) X x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
     x IN topspace top /\ v dot (g x ** v) = &1 /\ v dot (g x ** X x) = &0 /\
     mfd_ricci atlas g x v v = &0
     ==> mfd_scalar atlas g x = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) x))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:B->real^3^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN MATCH_MP_TAC P2BX0R_LSCALAR_ZERO THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) x)) (FST(chart_at atlas x))`;
    `(X:B->real^3) x`; `v:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) x))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas x) (g:B->real^3^3)`;
                   `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) x) x`;
                   `(X:B->real^3) x`; `v:real^3`] LRG_METRIC_SYM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `X:B->real^3`; `x:B`; `u:real^3`] P2BX0_PAR_SEC_ZERO) THEN
    ASM_REWRITE_TAC[mfd_sectional];
    UNDISCH_TAC `mfd_ricci (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) x v v = &0` THEN
    REWRITE_TAC[mfd_ricci]]);;

(* X0R.C6 The Ricci form kills a parallel field at every point:            *)
(* Ric(X x, w) = 0 (P2BX0_LRICCI_PAR in the preferred chart at x).          *)

let P2BX0R_PAR_RICCI_ZERO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) X p w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ p IN topspace top
     ==> mfd_ricci atlas g p (X p) w = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (SND c) (FST c INTER topspace top) =
                IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^N^N) (topspace top) X` THEN
  REWRITE_TAC[p2b_parallel_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`)
    (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                             (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `mfd_vrep atlas (X:A->real^N) (c:(A->bool)#(A->real^N))`;
                 `SND (c:(A->bool)#(A->real^N)) p`] P2BX0_LRICCI_PAR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `X:A->real^N`; `p:A`]
                P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN
  ASM_REWRITE_TAC[mfd_ricci] THEN SIMP_TAC[]);;

(* X0R.C3 The Busemann step: for a line lam through xl, if the geodesic    *)
(* through xl with velocity v is at distance >= t from lam t (all t >= 0)   *)
(* at the two parameters s = d and s = -d, then v is g-orthogonal to the    *)
(* splitting field X' of lam: the Busemann function B of lam is <= 0 at     *)
(* those two points, 0 at xl, and affine along the geodesic with slope      *)
(* <v, X'> (CMP_AFFINE_PARALLEL).                                           *)

let P2BX0R_BUSEMANN_ORTHO = prove
 (`!top atlas (g:B->real^3^3) (lam:real->B) v d.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u w. x IN topspace top /\ ~collinear {vec 0,u,w}
              ==> &0 <= mfd_sectional atlas g x u w) /\
     (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)) /\
     &0 < d /\
     (!s t. (s = d \/ s = --d) /\ &0 <= t
            ==> t <= mfd_dist (top,atlas) g (mfd_geo (top,atlas) g (lam(&0)) v s) (lam t))
     ==> ?X. p2b_parallel_on atlas g (topspace top) X /\
             (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
             v dot (g (lam(&0)) ** X(lam(&0))) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `lam:real->B`] CMPSP_LINE_E_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `lam:real->B`] CMPSP_LINE_BUSEMANN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B1 = cmp_busemann (top,atlas) (g:B->real^3^3) lam` THEN
  DISCH_THEN(LABEL_TAC "fl" o CONJUNCT2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lip")
    (CONJUNCTS_THEN2 (LABEL_TAC "eaff") (LABEL_TAC "asym"))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `B1:B->real`] CMP_AFFINE_PARALLEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "form") (K ALL_TAC))))) THEN
  EXISTS_TAC `X:B->real^3` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `xl = (lam:real->B)(&0)` THEN
  SUBGOAL_THEN `(xl:B) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "xl" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(B1:B->real) xl = &0` ASSUME_TAC THENL
   [EXPAND_TAC "xl" THEN USE_THEN "fl" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!s. mfd_geo (top,atlas) (g:B->real^3^3) xl v s =
                    mfd_exp (top,atlas) g xl (s % v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `xl:B`; `v:real^3`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`] MFD_COMPLETE_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`xl:B`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (s = d \/ s = --d) ==> (B1:B->real) (mfd_geo (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                                                   (g:B->real^3^3) (xl:B) (v:real^3) s) <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "B1" THEN REWRITE_TAC[cmp_busemann] THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `&0 - mfd_dist (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                                (g:B->real^3^3) (mfd_geo (top,atlas) g (xl:B) (v:real^3) s)
                                ((lam:real->B)(&0))` THEN
      EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `t <= x ==> t - x <= &0`) THEN
      USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (s = d \/ s = --d) ==> s * ((v:real^3) dot ((g:B->real^3^3) xl ** (X:B->real^3) xl)) <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      can (find_term (fun t -> t = `B1:B->real`)) (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "real_le" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "form" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(xl:B) IN topspace top`)]) THEN
    ASM_REWRITE_TAC[DOT_LMUL; REAL_ADD_LID];
    ALL_TAC] THEN
  ABBREV_TAC `c = (v:real^3) dot ((g:B->real^3^3) xl ** (X:B->real^3) xl)` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `d:real` th) THEN MP_TAC(SPEC `--d:real` th)) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LNEG] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `d * c = &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC);;

(* X0R.C4 Moving points along the X-orbits to almost closest points to p:   *)
(* the flow Phi_r of a unit parallel field is an isometry (P2BKF_PHI_ISOMETRY), *)
(* so R and the balls move with the points, and the new point q2 k is        *)
(* eta k-closest to p on its orbit.                                          *)

let P2BX0R_SHIFTED_POINTS = prove
 (`!top atlas (g:B->real^3^3) X p (q:num->B) (eta:num->real).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     p IN topspace top /\ (!k. q k IN topspace top) /\ (!k. &0 < eta k)
     ==> ?q2. !k. q2 k IN topspace top /\
                  mfd_scalar atlas g (q2 k) = mfd_scalar atlas g (q k) /\
                  (!R y. y IN mfd_ball (top,atlas) g (q2 k) R
                         ==> ?y'. y' IN mfd_ball (top,atlas) g (q k) R /\
                                  mfd_scalar atlas g y = mfd_scalar atlas g y') /\
                  (!r. mfd_dist (top,atlas) g p (q2 k) <=
                       mfd_dist (top,atlas) g p (p2bkf_phi (top,atlas) g X r (q2 k)) + eta k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
  ABBREV_TAC `S = {mfd_dist (top,atlas) (g:B->real^3^3) p
                     (p2bkf_phi (top,atlas) g X r ((q:num->B) k)) | r | T}` THEN
  SUBGOAL_THEN `!r. p2bkf_phi (top,atlas) (g:B->real^3^3) X r ((q:num->B) k) IN topspace top /\
                    &0 <= mfd_dist (top,atlas) g p (p2bkf_phi (top,atlas) g X r (q k))`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `r:real` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `X:B->real^3`; `r:real`; `(q:num->B) k`] P2BKF_PHI_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. mfd_dist (top,atlas) (g:B->real^3^3) p
                      (p2bkf_phi (top,atlas) g X r ((q:num->B) k)) < inf S + eta k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE; GSYM NOT_FORALL_THM] THEN
    MATCH_MP_TAC(TAUT `(p ==> F) ==> ~p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `S:real->bool` INF) THEN ANTS_TAC THENL
     [EXPAND_TAC "S" THEN CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
        EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p
                      (p2bkf_phi (top,atlas) g X (&0) ((q:num->B) k))` THEN
        EXISTS_TAC `&0` THEN REWRITE_TAC[];
        EXISTS_TAC `&0` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `inf S + (eta:num->real) k` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        can (term_match [] `!k:num. &0 < (eta:num->real) k`) (concl th))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r'. inf S <= mfd_dist (top,atlas) (g:B->real^3^3) p
                                 (p2bkf_phi (top,atlas) g X r' ((q:num->B) k))`
  (LABEL_TAC "inf") THENL
   [X_GEN_TAC `r':real` THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`&0`; `mfd_dist (top,atlas) (g:B->real^3^3) p
                                   (p2bkf_phi (top,atlas) g X r' ((q:num->B) k))`] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [EXISTS_TAC `r':real` THEN REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `p2bkf_phi (top,atlas) (g:B->real^3^3) X r ((q:num->B) k)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `g:B->real^3^3`; `X:B->real^3`; `r:real`] P2BKF_PHI_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `g:B->real^3^3`; `X:B->real^3`; `--r`] P2BKF_PHI_ISOMETRY) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `X:B->real^3`; `r:real`; `(q:num->B) k`] P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_ISOMETRY_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `top:B topology`;
                          `p2bkf_phi (top,atlas) (g:B->real^3^3) X (--r)`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`R:real`; `y:B`] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    EXISTS_TAC `p2bkf_phi (top,atlas) (g:B->real^3^3) X (--r) y` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p2bkf_phi (top,atlas) (g:B->real^3^3) X (--r)`;
                   `p2bkf_phi (top,atlas) (g:B->real^3^3) X r`] MFD_DIST_ISOMETRY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`p2bkf_phi (top,atlas) (g:B->real^3^3) X r ((q:num->B) k)`;
                               `y:B`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_ISOMETRY_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `top:B topology`;
                          `p2bkf_phi (top,atlas) (g:B->real^3^3) X r`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `r':real` THEN
    SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:B->real^3^3) X r'
                    (p2bkf_phi (top,atlas) g X r ((q:num->B) k)) =
                  p2bkf_phi (top,atlas) g X (r + r') (q k)`
    SUBST1_TAC THENL
     [REWRITE_TAC[p2bkf_phi] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `X:B->real^3`; `(q:num->B) k`] P2BKF_ORBIT_SHIFT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "inf" (MP_TAC o SPEC `r + r':real`) THEN ASM_REAL_ARITH_TAC]);;

(* X0R.C5a P2BX0_FAR_PAIR with the extra conclusion d(a,p) + r = dx (the  *)
(* point a lies on the segment from x to p); proof copied from pc_p2b_x0.  *)

let P2BX0R_FAR_PAIR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p u v dx dy eta K r.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     p IN topspace top /\ mfd_tnorm g p u = &1 /\ mfd_tnorm g p v = &1 /\
     &1 <= dx /\ &2 <= K /\ K * dx <= dy /\ &0 <= eta /\ eta pow 2 * K <= &1 /\
     (!s. &0 <= s /\ s <= dx
          ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u s) = s) /\
     (!s. &0 <= s /\ s <= dy
          ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p v s) = s) /\
     mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u (&1))
                            (mfd_geo (top,atlas) g p v (&1)) <= eta /\
     &0 < r /\ r <= dx
     ==> ?a b. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u dx) a /\
               mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u dx) b /\
               mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u dx) a = r /\
               mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u dx) b = r /\
               r pow 2 * K * (&4 - eta pow 2) <=
               (&1 + K) * mfd_dist (top,atlas) g a b pow 2 /\
               mfd_dist (top,atlas) g a p + r = dx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) p w = &1
                      ==> mfd_geo (top,atlas) g p w s IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `x = mfd_geo (top,atlas) (g:A->real^N^N) p u dx` THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) p v dy` THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (y:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN CONJ_TAC THEN
    USE_THEN "geoin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= dy` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p x = dx /\
                mfd_dist (top,atlas) g p y = dy`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s. &0 <= s /\ s <= dx
           ==> mfd_dist (top,atlas) (g:A->real^N^N) (p:A)
                 (mfd_geo (top,atlas) g p (u:real^N) s) = s`) (concl th)));
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s. &0 <= s /\ s <= dy
           ==> mfd_dist (top,atlas) (g:A->real^N^N) (p:A)
                 (mfd_geo (top,atlas) g p (v:real^N) s) = s`) (concl th)))] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* comparison at p *)
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^N^N) x y` THEN
  SUBGOAL_THEN `D pow 2 <= dx pow 2 + dy pow 2 - (&2 - eta pow 2) * dx * dy` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `u:real^N`; `v:real^N`; `dx:real`; `dy:real`; `&1`; `&1`]
                  P2BX0_TOPO_GEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `d1 = mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p u (&1))
                                             (mfd_geo (top,atlas) g p v (&1))` THEN
    SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
     [EXPAND_TAC "d1" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "join" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `d1 pow 2 <= eta pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 - eta pow 2) * (dx * dy) <= (&1 pow 2 + &1 pow 2 - d1 pow 2) * (dx * dy)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* triangle bounds for D *)
  SUBGOAL_THEN `dy - dx <= D /\ D <= dx + dy` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `x:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* segments from x *)
  SUBGOAL_THEN `~(p:A = x) /\ ~(y:A = x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x p = dx` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `p:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w1:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw1"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w2:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw2"))))) THEN
  MAP_EVERY EXISTS_TAC [`mfd_geo (top,atlas) (g:A->real^N^N) x w1 r`;
                        `mfd_geo (top,atlas) (g:A->real^N^N) x w2 r`] THEN
  SUBGOAL_THEN `r <= D` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x (mfd_geo (top,atlas) g x w1 r) = r /\
                mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x w2 r) = r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "dw1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "dw2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) x w = &1
                      ==> mfd_geo (top,atlas) g x w s IN topspace top`
  (LABEL_TAC "geoinx") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "geoinx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "geoinx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `w1:real^N`] CMPB_GEO_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real`; `dx:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) x w1 dx = p` SUBST1_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `mfd_geo (top,atlas) (g:A->real^N^N) x w1 r`; `p:A`]
                  MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "geoinx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x w1 r) p <=
                 abs(dx - r)` THEN
    ASM_REAL_ARITH_TAC] THEN
  (* comparison at x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `w1:real^N`; `w2:real^N`; `dx:real`; `D:real`; `r:real`; `r:real`]
                P2BX0_TOPO_GEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BX0_FAR_ALGEBRA THEN
  MAP_EVERY EXISTS_TAC [`D:real`; `dx:real`; `dy:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT];
    REWRITE_TAC[REAL_LE_POW_2];
    UNDISCH_TAC
     `(r pow 2 + r pow 2 -
       mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x w1 r)
                (mfd_geo (top,atlas) g x w2 r) pow 2) * (dx * D) <=
      (dx pow 2 + D pow 2 - dy pow 2) * (r * r)` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* X0R.C5b P2BX0_ALMOST_PAIRS with the extra conclusion that a lies on a  *)
(* segment from x(sub n) to p (from P2BX0R_FAR_PAIR); proof copied.        *)

let P2BX0R_ALMOST_PAIRS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p (x:num->A) (lam:num->real).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g y u v) /\
     p IN topspace top /\ (!n. x n IN topspace top) /\ (!n. &0 < lam n) /\
     (!M. ?N. !n. N <= n ==> M < mfd_dist (top,atlas) g p (x n)) /\
     (!M. ?N. !n. N <= n ==> M < lam n * mfd_dist (top,atlas) g p (x n) pow 2)
     ==> ?sub. p3_subseq sub /\
               !A e. &0 < A /\ &0 < e
                     ==> ?N. !n. N <= n
                             ==> ?a b. mfd_joinable (top,atlas) (x(sub n)) a /\
                                       mfd_joinable (top,atlas) (x(sub n)) b /\
                                       sqrt(lam(sub n)) *
                                       mfd_dist (top,atlas) g (x(sub n)) a = A /\
                                       sqrt(lam(sub n)) *
                                       mfd_dist (top,atlas) g (x(sub n)) b = A /\
                                       &2 * A - e <=
                                       sqrt(lam(sub n)) * mfd_dist (top,atlas) g a b /\
                                       mfd_dist (top,atlas) g a p +
                                       mfd_dist (top,atlas) g (x(sub n)) a =
                                       mfd_dist (top,atlas) g p (x(sub n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sec")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xin")
    (CONJUNCTS_THEN2 (LABEL_TAC "lpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "far") (LABEL_TAC "scale"))))))))))) THEN
  SUBGOAL_THEN `!y z. y IN topspace top /\ z IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y z`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a subsequence with d(p, x(sigma n)) >= n + 1 *)
  MP_TAC(ISPEC `\n. mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) n)`
                P2BX0_SUBSEQ_DIVERGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [USE_THEN "far" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sig"))) THEN
  (* segments from p *)
  SUBGOAL_THEN
   `?un:num->real^N.
      !n. mfd_tnorm (g:A->real^N^N) p (un n) = &1 /\
          mfd_geo (top,atlas) g p (un n) (mfd_dist (top,atlas) g p (x((sigma:num->num) n))) =
          x(sigma n) /\
          !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p (x(sigma n))
              ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p (un n) s) = s`
  (X_CHOOSE_THEN `un:num->real^N` (LABEL_TAC "un")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `(x:num->A) ((sigma:num->num) n)`] CMPSO_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN USE_THEN "sig" (MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `p:A`)) THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `p:A`] MFD_DIST_REFL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* convergence of the segments at fixed times *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `un:num->real^N`;
                 `\n. mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) n))`]
                CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "sig" (MP_TAC o SPEC `n:num`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `sub1:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))))) THEN
  MP_TAC(ISPEC `sub1:num->num` P2BX0_SUBSEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rho"))) THEN
  EXISTS_TAC `(sigma:num->num) o (sub1:num->num) o (rho:num->num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:real`; `e:real`] P2BX0_PAIR_PARAMS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `eta = inv(sqrt K)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta pow 2 * K = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt K` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`&1`; `eta / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "scale" (MP_TAC o SPEC `A pow 2`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k:num. k <= (sigma:num->num) k` (LABEL_TAC "sigge") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (sub1:num->num) ((rho:num->num) k)` (LABEL_TAC "srge") THENL
   [GEN_TAC THEN USE_THEN "rho" (MP_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `(rho:num->num) k` o check (fun th ->
      aconv (concl th) `!n:num. n <= (sub1:num->num) n`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (sub1:num->num) ((rho:num->num) n)` THEN
  ABBREV_TAC `dx = mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m))` THEN
  MP_TAC(SPEC `K * dx` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `M0:num`) THEN
  ABBREV_TAC `n2 = M0 + N1 + n:num` THEN
  ABBREV_TAC `m2 = (sub1:num->num) ((rho:num->num) n2)` THEN
  ABBREV_TAC `dy = mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2))` THEN
  SUBGOAL_THEN `n <= m:num /\ n2 <= m2:num /\ N1 <= n:num /\ N2 <= n:num /\ N1 <= n2:num /\ M0 <= n2:num`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` (ASSUME `!k:num. k <= (sub1:num->num) ((rho:num->num) k)`)) THEN
    MP_TAC(SPEC `n2:num` (ASSUME `!k:num. k <= (sub1:num->num) ((rho:num->num) k)`)) THEN
    REWRITE_TAC[ASSUME `(sub1:num->num) ((rho:num->num) n) = m`;
                ASSUME `(sub1:num->num) ((rho:num->num) n2) = m2`] THEN
    UNDISCH_TAC `N1 + N2 <= n:num` THEN UNDISCH_TAC `M0 + N1 + n = n2:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= dx /\ K * dx <= dy` STRIP_ASSUME_TAC THENL
   [USE_THEN "sig" (MP_TAC o SPEC `m:num`) THEN USE_THEN "sig" (MP_TAC o SPEC `m2:num`) THEN
    REWRITE_TAC[ASSUME `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`;
                ASSUME `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2)) = dy`] THEN
    UNDISCH_TAC `M0 <= n2:num` THEN UNDISCH_TAC `n2 <= m2:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `K * dx <= &M0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) p w = &1
                      ==> mfd_geo (top,atlas) g p w s IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p ((un:num->real^N) m) = &1 /\
                mfd_tnorm g p (un m2) = &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "un" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  (* closeness at time 1 *)
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N)
                  (mfd_geo (top,atlas) g p ((un:num->real^N) m) (&1))
                  (mfd_geo (top,atlas) g p (un m2) (&1)) <= eta` ASSUME_TAC THENL
   [USE_THEN "N1" (MP_TAC o SPEC `(rho:num->num) n`) THEN
    USE_THEN "N1" (MP_TAC o SPEC `(rho:num->num) n2`) THEN
    REWRITE_TAC[ASSUME `(sub1:num->num) ((rho:num->num) n) = m`;
                ASSUME `(sub1:num->num) ((rho:num->num) n2) = m2`] THEN
    ANTS_TAC THENL
     [USE_THEN "rho" (MP_TAC o SPEC `n2:num`) THEN UNDISCH_TAC `N1 <= n2:num` THEN ARITH_TAC;
      DISCH_TAC] THEN
    ANTS_TAC THENL
     [USE_THEN "rho" (MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `N1 <= n:num` THEN ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m2) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] P2BX0_DIST_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_REFL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "geoin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m2) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scale r = A / sqrt(lam) <= dx *)
  SUBGOAL_THEN `&0 < sqrt((lam:num->real) ((sigma:num->num) m))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN USE_THEN "lpos" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `A / sqrt((lam:num->real) ((sigma:num->num) m)) < dx` ASSUME_TAC THENL
   [USE_THEN "N2" (MP_TAC o SPEC `(sigma:num->num) m`) THEN
    ANTS_TAC THENL
     [USE_THEN "sigge" (MP_TAC o SPEC `m:num`) THEN UNDISCH_TAC `N2 <= n:num` THEN
      UNDISCH_TAC `n <= m:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME
      `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `A pow 2 < lam ((sigma:num->num) m) * dx pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the far pair *)
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) dx =
                (x:num->A) ((sigma:num->num) m)` ASSUME_TAC THENL
   [USE_THEN "un" (MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[ASSUME
      `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `(un:num->real^N) m`; `(un:num->real^N) m2`; `dx:real`; `dy:real`;
                 `eta:real`; `K:real`; `A / sqrt((lam:num->real) ((sigma:num->num) m))`]
                P2BX0R_FAR_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "un" (MP_TAC o SPEC `m:num`) THEN
      REWRITE_TAC[ASSUME
        `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
      SIMP_TAC[];
      USE_THEN "un" (MP_TAC o SPEC `m2:num`) THEN
      REWRITE_TAC[ASSUME
        `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2)) = dy`] THEN
      SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt((lam:num->real) ((sigma:num->num) m)) *
                (A / sqrt(lam(sigma m))) = A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX0_PAIR_ARITH THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eta:real`; `ep:real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
  EXISTS_TAC `(x:num->A) ((sigma:num->num) m)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(x:num->A) ((sigma:num->num) m)`; `a:A`] MFD_JOINABLE_SYM) THEN
  ASM_SIMP_TAC[]);;

(* X0R.C7 P2BX0_PAIRS_FROM_SUP with the two points in two compact sets   *)
(* K1 and K2 (the proof is the same: maximise F on K1 x K2).              *)

let P2BX0R_PAIRS_FROM_SUP2 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl K1 K2 A.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     xl IN topspace top /\ compact_in top K1 /\ compact_in top K2 /\ &0 < A /\
     (!e. &0 < e
          ==> ?y z. y IN K1 /\ z IN K2 /\
                    abs(mfd_dist (top,atlas) g xl y - A) < e /\
                    abs(mfd_dist (top,atlas) g xl z - A) < e /\
                    &2 * A - e < mfd_dist (top,atlas) g y z)
     ==> ?a b. a IN K1 /\ b IN K2 /\
               mfd_dist (top,atlas) g xl a = A /\ mfd_dist (top,atlas) g xl b = A /\
               mfd_dist (top,atlas) g a b = &2 * A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
                       LABEL_TAC "appr" (last (CONJUNCTS th))) THEN
  SUBGOAL_THEN `(K1:A->bool) SUBSET topspace top /\ (K2:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  ABBREV_TAC
   `Fp = \p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) (FST p) (SND p) -
                 &2 * abs(mfd_dist (top,atlas) g xl (FST p) - A) -
                 &2 * abs(mfd_dist (top,atlas) g xl (SND p) - A)` THEN
  SUBGOAL_THEN `continuous_map (prod_topology top top,euclideanreal) (\p:A#A. --((Fp:A#A->real) p))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN EXPAND_TAC "Fp" THEN
    REWRITE_TAC[] THEN REPEAT
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC) THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`] MFD_DIST_CONTINUOUS) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      SUBGOAL_THEN `(\p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) xl (FST p)) =
                    (\y. mfd_dist (top,atlas) g xl y) o FST` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_FST] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      SUBGOAL_THEN `(\p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) xl (SND p)) =
                    (\y. mfd_dist (top,atlas) g xl y) o SND` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((K1:A->bool) CROSS (K2:A->bool) = {})` ASSUME_TAC THENL
   [USE_THEN "appr" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM; IN_CROSS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prod_topology (top:A topology) top`; `\p:A#A. --((Fp:A#A->real) p)`;
                 `(K1:A->bool) CROSS (K2:A->bool)`] RFA_CMAP_COMPACT_MIN) THEN
  ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "max")))) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * A <= (Fp:A#A->real) (a,b)` ASSUME_TAC THENL
   [ABBREV_TAC `m = (Fp:A#A->real) (a,b)` THEN
    MATCH_MP_TAC(REAL_ARITH `~(x < y) ==> y <= x`) THEN DISCH_TAC THEN
    USE_THEN "appr" (MP_TAC o SPEC `(&2 * A - m) / &5`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `&2 * A - &5 * ((&2 * A - m) / &5) < (Fp:A#A->real) (y,z)` ASSUME_TAC THENL
     [EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "max" (MP_TAC o SPECL [`y:A`; `z:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) a b <=
                mfd_dist (top,atlas) g xl a + mfd_dist (top,atlas) g xl b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `xl:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `xl:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&2 * A <= (Fp:A#A->real) (a,b)` THEN EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* X0R.C8 P2BX0_PAIR_SEGMENTS with the endpoint bounds: the point at       *)
(* parameter s of the segment from xl to b (to a) is within L - s of b (a).  *)

let P2BX0R_PAIR_SEGMENTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl a b L.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ xl IN topspace top /\
     a IN topspace top /\ b IN topspace top /\ &0 < L /\
     mfd_dist (top,atlas) g xl a = L /\ mfd_dist (top,atlas) g xl b = L /\
     mfd_dist (top,atlas) g a b = &2 * L
     ==> ?u w. mfd_tnorm g xl u = &1 /\ mfd_tnorm g xl w = &1 /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl u s) = s) /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl w s) = s) /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u s) b <= L - s) /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl w s) a <= L - s) /\
               (!s t. &0 <= s /\ s <= L /\ &0 <= t /\ t <= L
                      ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u s)
                                                 (mfd_geo (top,atlas) g xl w t) = s + t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:A = xl) /\ ~(b:A = xl)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `xl:A`] MFD_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `b:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "du")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `a:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw")))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inu")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lipu")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inw")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lipw")))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl u L = b`)) THEN
    USE_THEN "lipu" (MP_TAC o SPECL [`s:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl w L = a`)) THEN
    USE_THEN "lipw" (MP_TAC o SPECL [`s:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) xl u s` THEN
  ABBREV_TAC `z = mfd_geo (top,atlas) (g:A->real^N^N) xl w t` THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (z:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN EXPAND_TAC "z" THEN
    USE_THEN "inu" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "inw" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) xl y = s` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN USE_THEN "du" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) xl z = t` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN USE_THEN "dw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) z a <= L - t` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl w L = a`)) THEN
    USE_THEN "lipw" (MP_TAC o SPECL [`t:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y b <= L - s` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl u L = b`)) THEN
    USE_THEN "lipu" (MP_TAC o SPECL [`s:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y z <= s + t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `xl:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `xl:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s + t <= mfd_dist (top,atlas) (g:A->real^N^N) y z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `z:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `y:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `z:A`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `y:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* X0R.C9 P2BX0_LINE_FROM_PAIRS with two points c1, c2 kept far from the  *)
(* ray: if the pairs (a, b) can be chosen with d(a, ci) >= A - e for every  *)
(* e > 0, then the line lam through xl (lam 0 = xl) satisfies               *)
(* d(ci, lam t) >= t for t >= 0 (the ray towards the a-points, by the      *)
(* triangle inequality along the segments and in the limit).               *)

let P2BX0R_LINE_FROM_PAIRS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl (c1:A) (c2:A).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ xl IN topspace top /\
     c1 IN topspace top /\ c2 IN topspace top /\
     (!A e. &0 < A /\ &0 < e
            ==> ?a b. a IN topspace top /\ b IN topspace top /\
                      mfd_dist (top,atlas) g xl a = A /\ mfd_dist (top,atlas) g xl b = A /\
                      mfd_dist (top,atlas) g a b = &2 * A /\
                      A - e <= mfd_dist (top,atlas) g a c1 /\
                      A - e <= mfd_dist (top,atlas) g a c2)
     ==> ?lam. (!s t. lam s IN topspace top /\
                      mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)) /\
               lam(&0) = xl /\
               (!t. &0 <= t ==> t <= mfd_dist (top,atlas) g c1 (lam t) /\
                                t <= mfd_dist (top,atlas) g c2 (lam t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
                       LABEL_TAC "pairs" (last (CONJUNCTS th))) THEN
  SUBGOAL_THEN
   `?(u:num->real^N) (w:num->real^N).
      !n. mfd_tnorm (g:A->real^N^N) xl (u n) = &1 /\ mfd_tnorm g xl (w n) = &1 /\
          (!s. &0 <= s /\ s <= &n + &1
               ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl (u n) s) = s) /\
          (!s. &0 <= s /\ s <= &n + &1
               ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl (w n) s) = s) /\
          (!s t. &0 <= s /\ s <= &n + &1 /\ &0 <= t /\ t <= &n + &1
                 ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl (u n) s)
                                            (mfd_geo (top,atlas) g xl (w n) t) = s + t) /\
          (!s. &0 <= s /\ s <= &n + &1
               ==> s - inv(&n + &1) <=
                   mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl (u n) s) c1 /\
                   s - inv(&n + &1) <=
                   mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl (u n) s) c2)`
  (X_CHOOSE_THEN `u:num->real^N` (X_CHOOSE_THEN `w:num->real^N` (LABEL_TAC "seg"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`&n + &1`; `inv(&n + &1)`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `xl:A`; `b:A`; `a:A`; `&n + &1`] P2BX0R_PAIR_SEGMENTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `b:A`; `a:A`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "toa") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "toa" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `xl:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!c:A. c IN topspace top /\ (&n + &1) - inv(&n + &1) <= mfd_dist (top,atlas) g a c
            ==> s - inv(&n + &1) <=
                mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g xl u s) c`
    (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
    X_GEN_TAC `c:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `mfd_geo (top,atlas) (g:A->real^N^N) xl u s`; `c:A`]
                  MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `mfd_geo (top,atlas) (g:A->real^N^N) xl u s`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v r. mfd_tnorm (g:A->real^N^N) xl v = &1
                      ==> mfd_geo (top,atlas) g xl v r IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `xl:A`; `v:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `u:num->real^N`; `\n:num. &n + &1`] CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `sub1:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rayu") (LABEL_TAC "convu")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `\n:num. (w:num->real^N) (sub1 n)`; `\n:num. &(sub1 n) + &1`]
                CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (term_match [] `!n:num. n <= (sub1:num->num) n`) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N` (X_CHOOSE_THEN `sub2:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rayw") (LABEL_TAC "convw")))))) THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ &0 <= t
          ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u0 s)
                                     (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t) = s + t`
  (LABEL_TAC "opp") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    ABBREV_TAC `D = mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u0 s)
                                           (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t)` THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ABBREV_TAC `e = abs(D - (s + t)) / &4` THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "convu" (MP_TAC o SPECL [`s:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    USE_THEN "convw" (MP_TAC o SPECL [`t:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
    MP_TAC(SPEC `s + t:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
    ABBREV_TAC `n = N1 + N2 + N3:num` THEN
    SUBGOAL_THEN `N2 <= n /\ N1 <= (sub2:num->num) n /\ s + t <= &((sub1:num->num) (sub2 n))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `n <= (sub2:num->num) n /\ (sub2 n) <= (sub1:num->num) (sub2 n)`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "n" THEN ARITH_TAC;
        UNDISCH_TAC `n <= (sub2:num->num) n` THEN EXPAND_TAC "n" THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N3` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `n <= (sub2:num->num) n` THEN
        UNDISCH_TAC `(sub2:num->num) n <= (sub1:num->num) (sub2 n)` THEN
        EXPAND_TAC "n" THEN ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "n1" (MP_TAC o SPEC `(sub2:num->num) n`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "n2" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
    USE_THEN "seg" (MP_TAC o SPEC `(sub1:num->num) ((sub2:num->num) n)`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`] o check (fun th ->
      can (term_match [] `!s t. &0 <= s /\ s <= x /\ &0 <= t /\ t <= x ==> P s t`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 s`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (u((sub1:num->num) ((sub2:num->num) n))) s`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (w((sub1:num->num) ((sub2:num->num) n))) t`]
                  P2BX0_DIST_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the u0 side keeps the distance bounds to c1 and c2 *)
  SUBGOAL_THEN
   `!n s. &0 <= s /\ s <= &n + &1
          ==> s - inv(&n + &1) <=
              mfd_dist (top,atlas) (g:A->real^N^N)
                       (mfd_geo (top,atlas) g xl ((u:num->real^N) n) s) c1 /\
              s - inv(&n + &1) <=
              mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl (u n) s) c2`
  (LABEL_TAC "segorb") THENL
   [REPEAT GEN_TAC THEN USE_THEN "seg" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `s:real` (last(CONJUNCTS th))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:A t. c IN topspace top /\ &0 <= t /\
            (!n s. &0 <= s /\ s <= &n + &1
                   ==> s - inv(&n + &1) <=
                       mfd_dist (top,atlas) (g:A->real^N^N)
                                (mfd_geo (top,atlas) g xl ((u:num->real^N) n) s) c)
            ==> t <= mfd_dist (top,atlas) g c (mfd_geo (top,atlas) g xl u0 t)`
  (LABEL_TAC "orb") THENL
   [MAP_EVERY X_GEN_TAC [`c:A`; `t:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "segc"))) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    ABBREV_TAC `e = (t - mfd_dist (top,atlas) (g:A->real^N^N) c
                              (mfd_geo (top,atlas) g xl u0 t)) / &3` THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "convu" (MP_TAC o SPECL [`t:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N4:num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `n = N1 + N3 + N4:num` THEN
    SUBGOAL_THEN `n <= (sub1:num->num) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `N1 <= n /\ t <= &((sub1:num->num) n) + &1 /\
                  inv(&((sub1:num->num) n) + &1) < e`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "n" THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N3` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `n <= (sub1:num->num) n` THEN
        EXPAND_TAC "n" THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N4)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `n <= (sub1:num->num) n` THEN
          EXPAND_TAC "n" THEN ARITH_TAC]];
      ALL_TAC] THEN
    USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "segc" (MP_TAC o SPECL [`(sub1:num->num) n`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (u((sub1:num->num) n)) t`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t`; `c:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (u((sub1:num->num) n)) t`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `c:A`; `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t`] MFD_DIST_SYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `&0 < e` THEN EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\t. if &0 <= t then mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t
                  else mfd_geo (top,atlas) g xl w0 (--t)` THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `xl:A`; `u0:real^N`] CMPB_GEO_FACTS) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[ASSUME `&0 <= t`] THEN
      CONJ_TAC THEN
      (USE_THEN "orb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       USE_THEN "segorb" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]])]] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN REWRITE_TAC[] THEN
  USE_THEN "rayu" (STRIP_ASSUME_TAC o REWRITE_RULE[cmp_ray]) THEN
  USE_THEN "rayw" (STRIP_ASSUME_TAC o REWRITE_RULE[cmp_ray]) THEN
  ASM_CASES_TAC `&0 <= s` THEN ASM_CASES_TAC `&0 <= t` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[];
    ASM_SIMP_TAC[] THEN
    USE_THEN "opp" (MP_TAC o SPECL [`s:real`; `--t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. &0 <= t ==> mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t IN topspace top`)
            (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl w0 (--s)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "opp" (MP_TAC o SPECL [`t:real`; `--s`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. &0 <= t ==> mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t IN topspace top`)
            (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--s`; `--t`] o check (fun th ->
      can (term_match [] `!s t. &0 <= s /\ &0 <= t
             ==> mfd_joinable (top,atlas) (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 s)
                   (mfd_geo (top,atlas) g xl w0 t) /\
                 mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl w0 s)
                   (mfd_geo (top,atlas) g xl w0 t) = abs(t - s)`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC]);;

(* X0R.C10 Exact pairs in the limit with the ray side far from c1 and c2:  *)
(* P2BX0_LIMIT_PAIRS for the first point restricted to the closed set of   *)
(* points at distance >= A - e0 from c1 and c2 (P2BX0R_PAIRS_FROM_SUP2).   *)
(* The view pairs come with points y1, y2 of the limit near c1, c2 whose   *)
(* images stay at rescaled distance >= A - e from the first view point.    *)

let P2BX0R_CLOSED_DIST_GE = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) c a.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> closed_in top {y | y IN topspace top /\ a <= mfd_dist (top,atlas) g c y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. mfd_dist (top,atlas) (g:B->real^N^N) c y`; `top:B topology`;
                 `euclideanreal`; `{r:real | r >= a}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[MFD_DIST_CONTINUOUS_RIGHT; GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_GE] THEN
  REWRITE_TAC[IN_ELIM_THM; real_ge] THEN SIMP_TAC[]);;

let P2BX0R_LIMIT_PAIRS = prove
 (`!(u:A->bool) (w:B->bool)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s A e0 (c1:B) (c2:B).
     LIM_DIST_STATEMENT u w /\ LIM_BALL_STATEMENT u w /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ connected_space top /\ riemannian_metric atlas (g s) /\
     mfd_complete (top,atlas) (g s) /\ &0 < A /\ &0 < e0 /\
     c1 IN topspace top /\ c2 IN topspace top /\
     (!e N. &0 < e
            ==> ?k a b y1 y2.
                  N <= k /\
                  mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                rfs_vatlas (V k) (t k + s / Q k)) (x k) a /\
                  mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                rfs_vatlas (V k) (t k + s / Q k)) (x k) b /\
                  sqrt(Q k) *
                  mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                            rfs_vatlas (V k) (t k + s / Q k))
                           (rfs_vmetric (V k) (t k + s / Q k)) (x k) a = A /\
                  sqrt(Q k) *
                  mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                            rfs_vatlas (V k) (t k + s / Q k))
                           (rfs_vmetric (V k) (t k + s / Q k)) (x k) b = A /\
                  &2 * A - e <=
                  sqrt(Q k) *
                  mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                            rfs_vatlas (V k) (t k + s / Q k))
                           (rfs_vmetric (V k) (t k + s / Q k)) a b /\
                  y1 IN W k /\ y2 IN W k /\
                  A - e <=
                  sqrt(Q k) *
                  mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                            rfs_vatlas (V k) (t k + s / Q k))
                           (rfs_vmetric (V k) (t k + s / Q k)) a (phi k y1) /\
                  A - e <=
                  sqrt(Q k) *
                  mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                            rfs_vatlas (V k) (t k + s / Q k))
                           (rfs_vmetric (V k) (t k + s / Q k)) a (phi k y2) /\
                  mfd_dist (top,atlas) (g s) c1 y1 < e /\
                  mfd_dist (top,atlas) (g s) c2 y2 < e)
     ==> ?a b. a IN topspace top /\ b IN topspace top /\
               mfd_dist (top,atlas) (g s) xl a = A /\ mfd_dist (top,atlas) (g s) xl b = A /\
               mfd_dist (top,atlas) (g s) a b = &2 * A /\
               A - e0 <= mfd_dist (top,atlas) (g s) a c1 /\
               A - e0 <= mfd_dist (top,atlas) (g s) a c2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    LABEL_TAC "L1" (el 0 ths) THEN LABEL_TAC "L2" (el 1 ths) THEN
    MAP_EVERY ASSUME_TAC (butlast (tl (tl ths))) THEN LABEL_TAC "views" (last ths)) THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                xl IN topspace top /\ (!k. &0 < (Q:num->real) k) /\
                (!k. (phi:num->B->A) k xl = x k) /\
                (!k. open_in top ((W:num->B->bool) k))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  SUBGOAL_THEN `!k (y:B). y IN (W:num->B->bool) k ==> y IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. compact_in (top:B topology)
                      (mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "L2" (MP_TAC o REWRITE_RULE[LIM_BALL_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `A + &1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:B->bool` (X_CHOOSE_THEN `k0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball")))) THEN
  ABBREV_TAC `D1 = mfd_dist (top,atlas) ((g:real->B->real^3^3) s) xl c1` THEN
  ABBREV_TAC `D2 = mfd_dist (top,atlas) ((g:real->B->real^3^3) s) xl c2` THEN
  ABBREV_TAC `K = ({xl:B} UNION K0) UNION
                  (mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (D1 + &1) UNION
                   mfd_cball (top,atlas) (g s) xl (D2 + &1))` THEN
  SUBGOAL_THEN `compact_in (top:B topology) K /\ (xl:B) IN K /\ K0 SUBSET K /\
                mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (D1 + &1) SUBSET K /\
                mfd_cball (top,atlas) (g s) xl (D2 + &1) SUBSET K /\
                K SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[COMPACT_IN_SING];
      SET_TAC[];
      SET_TAC[];
      SET_TAC[];
      SET_TAC[];
      REWRITE_TAC[UNION_SUBSET; SING_SUBSET] THEN ASM_MESON_TAC[compact_in]];
    ALL_TAC] THEN
  ABBREV_TAC `S = {y:B | y IN topspace top /\
                         A - e0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) s) c1 y} INTER
                  {y:B | y IN topspace top /\
                         A - e0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) s) c2 y}` THEN
  SUBGOAL_THEN `compact_in (top:B topology) (K INTER S)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC CLOSED_IN_INTER THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BX0R_CLOSED_DIST_GE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `xl:B`; `(K:B->bool) INTER S`; `K:B->bool`;
                 `A:real`] P2BX0R_PAIRS_FROM_SUP2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `e1 = min e (min e0 (&1)) / &4` THEN
    SUBGOAL_THEN `&0 < e1 /\ &2 * e1 < e /\ &3 * e1 < e0 /\ e1 < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "L1" (MP_TAC o REWRITE_RULE[LIM_DIST_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W:num->B->bool`; `phi:num->B->A`; `s:real`; `K:B->bool`; `e1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "dist")) THEN
    USE_THEN "views" (MP_TAC o SPECL [`e1:real`; `k0 + k1:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A`
      (X_CHOOSE_THEN `y1:B` (X_CHOOSE_THEN `y2:B` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `(k0:num) <= k /\ (k1:num) <= k` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) IN IMAGE ((phi:num->B->A) k) (K0 INTER W k) /\
                  (b:A) IN IMAGE (phi k) (K0 INTER W k)`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `ya:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `zb:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(ya:B) IN K /\ (zb:B) IN K /\ (ya:B) IN topspace top /\
                  (y1:B) IN topspace top /\ (y2:B) IN topspace top`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    (* y1 and y2 lie in the compact set K *)
    SUBGOAL_THEN `!c y:B D. c IN topspace top /\ y IN topspace top /\
                            mfd_dist (top,atlas) ((g:real->B->real^3^3) s) xl c = D /\
                            mfd_dist (top,atlas) (g s) c y < e1
                            ==> y IN mfd_cball (top,atlas) (g s) xl (D + &1)`
    (LABEL_TAC "incb") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `xl:B`; `c:B`; `y:B`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1:B) IN K /\ (y2:B) IN K` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(y1:B) IN mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (D1 + &1)`
        MP_TAC THENL
         [USE_THEN "incb" MATCH_MP_TAC THEN EXISTS_TAC `c1:B` THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        SUBGOAL_THEN `(y2:B) IN mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (D2 + &1)`
        MP_TAC THENL
         [USE_THEN "incb" MATCH_MP_TAC THEN EXISTS_TAC `c2:B` THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]]];
      ALL_TAC] THEN
    (* the limit distances *)
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `ya:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `zb:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `ya:B`; `zb:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `ya:B`; `y1:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `ya:B`; `y2:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    (* the far conditions for c1 and c2 *)
    SUBGOAL_THEN `!c y:B. c IN topspace top /\ y IN topspace top /\
                          A - &2 * e1 < mfd_dist (top,atlas) ((g:real->B->real^3^3) s) ya y /\
                          mfd_dist (top,atlas) (g s) c y < e1
                          ==> A - e0 <= mfd_dist (top,atlas) (g s) c ya`
    (LABEL_TAC "cfar") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `ya:B`; `c:B`; `y:B`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `ya:B`; `c:B`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ya:B`; `zb:B`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN USE_THEN "cfar" MATCH_MP_TAC THENL
       [EXISTS_TAC `y1:B`; EXISTS_TAC `y2:B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(a:B) IN K INTER S` THEN EXPAND_TAC "S" THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `a:B`; `c1:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `a:B`; `c2:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* X0R.C11 Lemmas for the assembly: the flow-to-slice bridge (a copy of     *)
(* P2BU_FLOW_TO_SLICE_AT of pc_p2c_blowup2, which is outside the load       *)
(* closure of this unit), the divergence of the distance from the           *)
(* divergence of R, the points of the argument and the orbit inequality for *)
(* the pairs.                                                               *)

let P2BX0R_FLOW_TO_SLICE_AT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\ s IN J /\
     riemannian_metric atlas (g s)
     ==> ?N. p2c_slice_limit_with (\n. V (n + N)) (\n. x (n + N))
               (\n. t (n + N) + s / Q (n + N)) (\n. Q (n + N)) (top,atlas) (g s) xl
               (\n. W (n + N)) (\n. phi (n + N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `real_interval[s,s] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r:real = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `{xl:B}`; `0`; `&1`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  EXISTS_TAC `N:num` THEN REWRITE_TAC[p2c_slice_limit_with] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "UNIONS" with _ -> false))
            (lhs(concl th)))) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `y:B` THEN
      DISCH_THEN(X_CHOOSE_THEN `u:B->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `m:num`) ASSUME_TAC)) THEN
      EXISTS_TAC `(W:num->B->bool) (m + N)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + N)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
        UNDISCH_TAC `(y:B) IN u` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    X_GEN_TAC `n:num` THEN
    USE_THEN "N" (MP_TAC o SPEC `n + N:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[REAL_LE_REFL];
    MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`; `K:B->bool`; `m:num`; `eta:real`] o
      check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun u -> try fst(dest_const u) = "lck_dist2" with _ -> false))
            (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
    EXISTS_TAC `k1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "k1" (MP_TAC o SPEC `n + N:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `k1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

let P2BX0R_RDIV_DIST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p (q:num->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ p IN topspace top /\
     (!k. q k IN topspace top) /\
     (!M. ?N. !k. N <= k ==> M < mfd_scalar atlas g (q k))
     ==> !M. ?N. !k. N <= k ==> M < mfd_dist (top,atlas) g p (q k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "qin") (LABEL_TAC "div"))))))) THEN
  X_GEN_TAC `M:real` THEN
  ABBREV_TAC `M' = max M (&0)` THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) (g:A->real^N^N) p M'` THEN
  SUBGOAL_THEN `compact_in top (Kb:A->bool) /\ (p:A) IN Kb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_complete];
      REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_DIST_REFL; MFD_JOINABLE_REFL] THEN EXPAND_TAC "M'" THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `\y:A. --(mfd_scalar atlas (g:A->real^N^N) y)`;
                 `Kb:A->bool`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_NEG2] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))) THEN
  ABBREV_TAC `C = max (mfd_scalar atlas (g:A->real^N^N) y0) (&0)` THEN
  USE_THEN "div" (MP_TAC o SPEC `C:real`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(LABEL_TAC "N") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `M <= M' /\ ~(d <= M') ==> M < d`) THEN CONJ_TAC THENL
   [EXPAND_TAC "M'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  USE_THEN "N" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p ((q:num->A) k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "qin" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^N^N) ((q:num->A) k) <= C` ASSUME_TAC THENL
   [USE_THEN "max" (MP_TAC o SPEC `(q:num->A) k`) THEN ANTS_TAC THENL
     [EXPAND_TAC "Kb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "C" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* R d^2 diverges when R and d diverge. *)

let P2BX0R_RD2_DIV = prove
 (`!(R:num->real) (d:num->real).
     (!M. ?N. !k. N <= k ==> M < R k) /\ (!M. ?N. !k. N <= k ==> M < d k)
     ==> !M. ?N. !k. N <= k ==> M < R k * d k pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "d")) THEN X_GEN_TAC `M:real` THEN
  USE_THEN "d" (X_CHOOSE_TAC `N2:num` o SPEC `&1`) THEN
  USE_THEN "R" (X_CHOOSE_TAC `N1:num` o SPEC `max M (&0)`) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `max M (&0) < (R:num->real) k /\ &1 < (d:num->real) k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (d:num->real) k pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(R:num->real) k * &1` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* The points of the argument at one time: unbounded scalar curvature       *)
(* gives picked points (P2BX0_PICKED_POINTS) moved along the orbits of the  *)
(* unit parallel field X to almost minimise the distance to p              *)
(* (P2BX0R_SHIFTED_POINTS, error inv(k+1) / sqrt R).                       *)

let P2BX0R_POINTS = prove
 (`!top atlas (G:B->real^3^3) (X:B->real^3) p.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas G /\ mfd_complete (top,atlas) G /\
     (!y. y IN topspace top ==> &0 <= mfd_scalar atlas G y) /\
     p2b_parallel_on atlas G (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (G y ** X y) = &1) /\
     p IN topspace top /\
     (!K. ?y. y IN topspace top /\ K < mfd_scalar atlas G y)
     ==> ?q:num->B.
           (!k. q k IN topspace top /\ &0 < mfd_scalar atlas G (q k)) /\
           (!M. ?N. !k. N <= k ==> M < mfd_dist (top,atlas) G p (q k)) /\
           (!M. ?N. !k. N <= k
                        ==> M < mfd_scalar atlas G (q k) * mfd_dist (top,atlas) G p (q k) pow 2) /\
           (!A. ?N. !k y. N <= k /\
                          y IN mfd_ball (top,atlas) G (q k)
                                        (A * inv(sqrt(mfd_scalar atlas G (q k))))
                          ==> mfd_scalar atlas G y <= &4 * mfd_scalar atlas G (q k)) /\
           (!k r. mfd_dist (top,atlas) G p (q k) <=
                  mfd_dist (top,atlas) G p (p2bkf_phi (top,atlas) G X r (q k)) +
                  inv(&k + &1) * inv(sqrt(mfd_scalar atlas G (q k))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
                       LABEL_TAC "unb" (last (CONJUNCTS th))) THEN
  SUBGOAL_THEN `?pp:num->B. !k. pp k IN topspace top /\ &k < mfd_scalar atlas (G:B->real^3^3) (pp k)`
  (X_CHOOSE_THEN `pp:num->B` (LABEL_TAC "pp")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "unb" (MP_TAC o SPEC `&k`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!M. ?N. !k. N <= k ==> M < mfd_scalar atlas (G:B->real^3^3) ((pp:num->B) k)`
  (LABEL_TAC "ppR") THENL
   [X_GEN_TAC `M:real` THEN MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "pp" (MP_TAC o CONJUNCT2 o SPEC `k:num`) THEN
    SUBGOAL_THEN `&N <= &k` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `p:B`; `pp:num->B`] P2BX0R_RDIV_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "pp" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ppd") THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `p:B`; `pp:num->B`] P2BX0_PICKED_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MP_TAC(ISPECL [`\k. mfd_scalar atlas (G:B->real^3^3) ((pp:num->B) k)`;
                   `\k. mfd_dist (top,atlas) (G:B->real^3^3) p ((pp:num->B) k)`]
                  P2BX0R_RD2_DIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:num->B` (CONJUNCTS_THEN2 (LABEL_TAC "q0")
    (CONJUNCTS_THEN2 (LABEL_TAC "q0div") (LABEL_TAC "q0balls")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `X:B->real^3`; `p:B`; `q0:num->B`;
                 `\k. inv(&k + &1) * inv(sqrt(mfd_scalar atlas (G:B->real^3^3) ((q0:num->B) k)))`]
                P2BX0R_SHIFTED_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(USE_THEN "q0" (fun th -> REWRITE_TAC[th]) THEN NO_TAC) THEN
    X_GEN_TAC `k:num` THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_INV THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:num->B` (LABEL_TAC "q2")) THEN
  SUBGOAL_THEN `!k. mfd_scalar atlas (G:B->real^3^3) ((q2:num->B) k) =
                    mfd_scalar atlas G ((q0:num->B) k)` (LABEL_TAC "Req") THENL
   [GEN_TAC THEN USE_THEN "q2" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!M. ?N. !k. N <= k ==> M < mfd_scalar atlas (G:B->real^3^3) ((q2:num->B) k)`
  (LABEL_TAC "q2R") THENL
   [X_GEN_TAC `M:real` THEN USE_THEN "ppR" (MP_TAC o SPEC `M:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "Req" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas (G:B->real^3^3) ((pp:num->B) k)` THEN
    ASM_SIMP_TAC[] THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `p:B`; `q2:num->B`] P2BX0R_RDIV_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "q2" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "q2d") THEN
  EXISTS_TAC `q2:num->B` THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "q2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    USE_THEN "q2d" ACCEPT_TAC;
    MP_TAC(ISPECL [`\k. mfd_scalar atlas (G:B->real^3^3) ((q2:num->B) k)`;
                   `\k. mfd_dist (top,atlas) (G:B->real^3^3) p ((q2:num->B) k)`]
                  P2BX0R_RD2_DIV) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    X_GEN_TAC `A:real` THEN USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "q2" (MP_TAC o SPECL
      [`A * inv(sqrt(mfd_scalar atlas (G:B->real^3^3) ((q2:num->B) k)))`; `y:B`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':B` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "Req" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y':B) IN mfd_ball (top,atlas) (G:B->real^3^3) ((q0:num->B) k)
                   (A * inv(sqrt(mfd_scalar atlas G ((q2:num->B) k))))` THEN
    USE_THEN "Req" (fun th -> REWRITE_TAC[th]);
    MAP_EVERY X_GEN_TAC [`k:num`; `r:real`] THEN
    USE_THEN "q2" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    USE_THEN "Req" (fun th -> REWRITE_TAC[th])]);;

(* The orbit inequality for the pairs: if x k almost minimises the         *)
(* distance to p on its X-orbit (error eta k) and a lies on a segment from  *)
(* x k to p, then a stays at distance >= d(x k, a) - eta k from the orbit.  *)

let P2BX0R_ORBIT_PAIRS = prove
 (`!top atlas (G:B->real^3^3) (X:B->real^3) p (x:num->B) (Q:num->real) (eta:num->real).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ connected_space top /\
     p IN topspace top /\ (!k. x k IN topspace top) /\ (!k. &0 < Q k) /\
     (!k r. p2bkf_phi (top,atlas) G X r (x k) IN topspace top) /\
     (!k. sqrt(Q k) * eta k <= inv(&k + &1)) /\
     (!k r. mfd_dist (top,atlas) G p (x k) <=
            mfd_dist (top,atlas) G p (p2bkf_phi (top,atlas) G X r (x k)) + eta k) /\
     (!A e. &0 < A /\ &0 < e
            ==> ?N. !k. N <= k
                    ==> ?a b. mfd_joinable (top,atlas) (x k) a /\
                              mfd_joinable (top,atlas) (x k) b /\
                              sqrt(Q k) * mfd_dist (top,atlas) G (x k) a = A /\
                              sqrt(Q k) * mfd_dist (top,atlas) G (x k) b = A /\
                              &2 * A - e <= sqrt(Q k) * mfd_dist (top,atlas) G a b /\
                              mfd_dist (top,atlas) G a p + mfd_dist (top,atlas) G (x k) a =
                              mfd_dist (top,atlas) G p (x k))
     ==> !A e. &0 < A /\ &0 < e
               ==> ?N. !k. N <= k
                       ==> ?a b. mfd_joinable (top,atlas) (x k) a /\
                                 mfd_joinable (top,atlas) (x k) b /\
                                 sqrt(Q k) * mfd_dist (top,atlas) G (x k) a = A /\
                                 sqrt(Q k) * mfd_dist (top,atlas) G (x k) b = A /\
                                 &2 * A - e <= sqrt(Q k) * mfd_dist (top,atlas) G a b /\
                                 !r. A - e <= sqrt(Q k) *
                                              mfd_dist (top,atlas) G a
                                                       (p2bkf_phi (top,atlas) G X r (x k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (butlast (CONJUNCTS th)) THEN
                       LABEL_TAC "pairs" (last (CONJUNCTS th))) THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `e:real`] THEN STRIP_TAC THEN
  USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "N1" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN
  ABBREV_TAC `z = p2bkf_phi (top,atlas) (G:B->real^3^3) X r ((x:num->B) k)` THEN
  SUBGOAL_THEN `(z:B) IN topspace top /\ (a:B) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "z" THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&k + &1) < e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `p:B`; `a:B`; `z:B`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                 `p:B`; `a:B`] MFD_DIST_SYM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (G:B->real^3^3) ((x:num->B) k) a - eta k <=
                mfd_dist (top,atlas) G a z` ASSUME_TAC THENL
   [MP_TAC(SPECL [`k:num`; `r:real`] (ASSUME
     `!k r. mfd_dist (top,atlas) (G:B->real^3^3) p ((x:num->B) k) <=
            mfd_dist (top,atlas) G p (p2bkf_phi (top,atlas) G X r (x k)) + (eta:num->real) k`)) THEN
    REWRITE_TAC[ASSUME `p2bkf_phi (top,atlas) (G:B->real^3^3) X r ((x:num->B) k) = z`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (ASSUME
    `!k. sqrt((Q:num->real) k) * (eta:num->real) k <= inv(&k + &1)`)) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((Q:num->real) k) *
              (mfd_dist (top,atlas) (G:B->real^3^3) ((x:num->B) k) a - eta k)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LDISTRIB] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The statement: bounded slices for an ancient flow with a global unit      *)
(* split field (a step of MT Cor 9.50 in SPLIT_ROUND).                       *)

let P2B_GSPLIT_SLICE_BOUND_STATEMENT = new_definition
 `P2B_GSPLIT_SLICE_BOUND_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b (X:B->real^3) s1.
      p2b_ancflow0 kappa (top,atlas) g b /\ p2b_gsplit (top,atlas) g {s | s < b} X /\
      s1 < b
      ==> ?K. !x. x IN topspace top ==> mfd_scalar atlas (g s1) x <= K`;;

let P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT = new_definition
 `P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
    P2BPL_POINT_LIMIT_STATEMENT w w /\ P2BPL_ORBIT_LIMIT_STATEMENT w w
    ==> P2B_GSPLIT_SLICE_BOUND_STATEMENT w`;;

(* X0R.C12 The assembly: unbounded scalar curvature at a time s1 < b      *)
(* gives (P2BX0R_POINTS) points q k almost minimising the distance to p on *)
(* their X-orbits, almost-line pairs along them with the segment property  *)
(* (P2BX0R_ALMOST_PAIRS), the X0 limit along a subsequence                 *)
(* (P2BX0_LIMIT_EXISTS, ANCIENT_COMPACT), its slice at time 0              *)
(* (P2BX0R_FLOW_TO_SLICE_AT), a unit vector v with Ric(v,v) = 0 at xl      *)
(* (POINT, Ric(X,X) = 0) and the convergence of the X-orbits to the       *)
(* geodesic of v (ORBIT); the pairs stay far from the orbit points         *)
(* (P2BX0R_ORBIT_PAIRS), so the limit line keeps the points geo(xl,v,d)   *)
(* and geo(xl,v,-d) at distance >= t from lam t (P2BX0R_LIMIT_PAIRS,       *)
(* P2BX0R_LINE_FROM_PAIRS); the splitting field of the line is orthogonal *)
(* to v (P2BX0R_BUSEMANN_ORTHO), hence R(xl) = 0 at time 0               *)
(* (P2BX0R_SCALAR_ZERO), against R(xl) = 1 (P2BX0_XLIM_R1).               *)

let P2BX0R_SLICE_BOUND_BODY = prove
 (`!w:B->bool.
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     P2BPL_POINT_LIMIT_STATEMENT w w /\ P2BPL_ORBIT_LIMIT_STATEMENT w w
     ==> P2B_GSPLIT_SLICE_BOUND_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AC") (CONJUNCTS_THEN2 (LABEL_TAC "POINT")
    (LABEL_TAC "ORBIT"))) THEN
  REWRITE_TAC[P2B_GSPLIT_SLICE_BOUND_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `X:B->real^3`; `s1:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gs") ASSUME_TAC)) THEN
  (* by contradiction; the goal &0 = &1 (instead of F) keeps REWRITE_TAC   *)
  (* from turning the implications below into negations                    *)
  MATCH_MP_TAC(MESON[REAL_ARITH `~(&0 = &1)`] `(~p ==> &0 = &1) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "unb" o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP;
                                             REAL_NOT_LE]) THEN
  (* facts at time s1 *)
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s1) /\
                mfd_complete (top,atlas) (g s1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s1) y u v`
  (LABEL_TAC "sec1") THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> &0 <= mfd_scalar atlas ((g:real->B->real^3^3) s1) y`
  (LABEL_TAC "Rnn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s1`; `y:B`;
                   `mfd_rm_norm atlas ((g:real->B->real^3^3) s1) y`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN USE_THEN "sec1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "gs" (MP_TAC o SPEC `s1:real` o REWRITE_RULE[p2b_gsplit]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unit1")) THEN
  SUBGOAL_THEN `?p:B. p IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
    REWRITE_TAC[p2b_ancflow0; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the points and the pairs *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s1`; `X:B->real^3`; `p:B`] P2BX0R_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->B` (CONJUNCTS_THEN2 (LABEL_TAC "qin")
    (CONJUNCTS_THEN2 (LABEL_TAC "qd") (CONJUNCTS_THEN2 (LABEL_TAC "qdiv")
    (CONJUNCTS_THEN2 (LABEL_TAC "qballs") (LABEL_TAC "qmin")))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s1`; `p:B`; `q:num->B`;
                 `\k. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((q:num->B) k)`]
                P2BX0R_ALMOST_PAIRS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `suba:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))) THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) k` (LABEL_TAC "subage") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the X0 limit along q o suba *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s1:real`; `(q:num->B) o (suba:num->num)`] P2BX0_LIMIT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "qballs" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subage" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subb:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xlim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "comp0")))))))))))) THEN
  ABBREV_TAC `x = ((q:num->B) o (suba:num->num)) o (subb:num->num)` THEN
  SUBGOAL_THEN `!k. q((suba:num->num)((subb:num->num) k)) = (x:num->B) k` (LABEL_TAC "qx") THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) ((subb:num->num) k)` (LABEL_TAC "subge") THENL
   [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    USE_THEN "subage" (MP_TAC o SPEC `(subb:num->num) k`) THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "xlim" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
                             STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th)) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s1:real`; `x:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0_XLIM_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LIM_CURV]; DISCH_THEN(LABEL_TAC "secl")] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s1:real`; `x:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0_XLIM_R1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LIM_CURV]; DISCH_THEN(LABEL_TAC "r1")] THEN
  (* the slice at time 0 *)
  MP_TAC(ISPECL [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
                 `x:num->B`; `\k:num. (s1:real)`;
                 `\k. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)`;
                 `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`]
                P2BX0R_FLOW_TO_SLICE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "slice")) THEN
  (* POINT: a unit vector v at xl with Ric(v,v) = 0 *)
  USE_THEN "POINT" (MP_TAC o SPECL
   [`\n:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
    `\n. (x:num->B) (n + N0)`; `\n:num. (s1:real)`;
    `\n. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) (n + N0))`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3) (&0)`;
    `xl:B`; `\n. (W:num->B->bool) (n + N0)`; `\n. (phi:num->B->B) (n + N0)`;
    `\n. (X:B->real^3) ((x:num->B) (n + N0))`] o REWRITE_RULE[P2BPL_POINT_LIMIT_STATEMENT]) THEN
  REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM; ASSUME `s1 < b`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `(x:num->B) (n + N0) IN topspace top` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC P2BX0R_PAR_RICCI_ZERO THEN
    EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `v:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))))) THEN
  (* ORBIT: the X-orbits converge to the geodesic of v *)
  USE_THEN "ORBIT" (MP_TAC o SPECL
   [`\n:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
    `\n. (x:num->B) (n + N0)`; `\n:num. (s1:real)`;
    `\n. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) (n + N0))`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3) (&0)`;
    `xl:B`; `\n. (W:num->B->bool) (n + N0)`; `\n. (phi:num->B->B) (n + N0)`;
    `\n. (X:B->real^3) ((x:num->B) (n + N0))`; `sub:num->num`; `v:real^3`] o
    REWRITE_RULE[P2BPL_ORBIT_LIMIT_STATEMENT]) THEN
  REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM; ASSUME `s1 < b`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "orb"))) THEN
  (* the facts along x for the orbit inequality *)
  SUBGOAL_THEN `!k. (x:num->B) k IN topspace top` (LABEL_TAC "xin") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)`
  (LABEL_TAC "xR") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k r. p2bkf_phi (top,atlas) ((g:real->B->real^3^3) s1) X r ((x:num->B) k) IN
                      topspace top`
  (LABEL_TAC "phiin") THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `r:real`] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s1`; `X:B->real^3`; `r:real`; `(x:num->B) k`]
                  P2BKF_PHI_INVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)) *
                    (inv(&((suba:num->num) ((subb:num->num) k)) + &1) *
                     inv(sqrt(mfd_scalar atlas (g s1) (x k)))) <= inv(&k + &1)`
  (LABEL_TAC "seta") THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k))`
    ASSUME_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!a i. &0 < a ==> a * (i * inv a) = i` MP_TAC THENL
     [CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k))`;
      `inv(&((suba:num->num) ((subb:num->num) k)) + &1)`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN USE_THEN "subge" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k r. mfd_dist (top,atlas) ((g:real->B->real^3^3) s1) p ((x:num->B) k) <=
                      mfd_dist (top,atlas) (g s1) p (p2bkf_phi (top,atlas) (g s1) X r (x k)) +
                      inv(&((suba:num->num) ((subb:num->num) k)) + &1) *
                      inv(sqrt(mfd_scalar atlas (g s1) (x k)))`
  (LABEL_TAC "xmin") THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `r:real`] THEN
    USE_THEN "qmin" (MP_TAC o SPECL [`(suba:num->num) ((subb:num->num) k)`; `r:real`]) THEN
    USE_THEN "qx" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A e. &0 < A /\ &0 < e
          ==> ?N. !k. N <= k
                  ==> ?a b. mfd_joinable (top,atlas) ((x:num->B) k) a /\
                            mfd_joinable (top,atlas) (x k) b /\
                            sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s1) (x k)) *
                            mfd_dist (top,atlas) (g s1) (x k) a = A /\
                            sqrt(mfd_scalar atlas (g s1) (x k)) *
                            mfd_dist (top,atlas) (g s1) (x k) b = A /\
                            &2 * A - e <= sqrt(mfd_scalar atlas (g s1) (x k)) *
                                          mfd_dist (top,atlas) (g s1) a b /\
                            mfd_dist (top,atlas) (g s1) a p +
                            mfd_dist (top,atlas) (g s1) (x k) a =
                            mfd_dist (top,atlas) (g s1) p (x k)`
  (LABEL_TAC "xpairs") THENL
   [MAP_EVERY X_GEN_TAC [`A:real`; `e:real`] THEN STRIP_TAC THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Np:num` (LABEL_TAC "Np")) THEN EXISTS_TAC `Np:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "Np" (MP_TAC o SPEC `(subb:num->num) k`) THEN
    USE_THEN "qx" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `Np <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s1`; `X:B->real^3`; `p:B`; `x:num->B`;
                 `\k. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)`;
                 `\k. inv(&((suba:num->num) ((subb:num->num) k)) + &1) *
                      inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)))`]
                P2BX0R_ORBIT_PAIRS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "opairs")] THEN
  (* the geodesic of v and the limit pairs far from geo(xl,v,d), geo(xl,v,-d) *)
  SUBGOAL_THEN `mfd_tnorm ((g':real->B->real^3^3) (&0)) xl v = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_tnorm; SQRT_1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`; `v:real^3`] CMPB_GEO_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "geoin" o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!A e0. &0 < A /\ &0 < e0
           ==> ?a b. a IN topspace top' /\ b IN topspace top' /\
                     mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl a = A /\
                     mfd_dist (top',atlas') (g' (&0)) xl b = A /\
                     mfd_dist (top',atlas') (g' (&0)) a b = &2 * A /\
                     A - e0 <= mfd_dist (top',atlas') (g' (&0)) a
                                        (mfd_geo (top',atlas') (g' (&0)) xl v d) /\
                     A - e0 <= mfd_dist (top',atlas') (g' (&0)) a
                                        (mfd_geo (top',atlas') (g' (&0)) xl v (--d))`
  (LABEL_TAC "lpairs") THENL
   [MAP_EVERY X_GEN_TAC [`A:real`; `e0:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`w:B->bool`; `w:B->bool`;
      `\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
      `x:num->B`; `\k:num. (s1:real)`;
      `\k. mfd_scalar atlas ((g:real->B->real^3^3) s1) ((x:num->B) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `A:real`;
      `e0:real`; `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v d`;
      `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v (--d)`]
     P2BX0R_LIMIT_PAIRS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LIM_DIST; LIM_BALL; IN_ELIM_THM; REAL_LE_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM;
                ASSUME `s1 < b`] THEN
    MAP_EVERY X_GEN_TAC [`e:real`; `N:num`] THEN DISCH_TAC THEN
    USE_THEN "opairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
    USE_THEN "orb" (MP_TAC o SPECL [`d:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (LABEL_TAC "n1")) THEN
    USE_THEN "orb" (MP_TAC o SPECL [`--d:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:num` (LABEL_TAC "n2")) THEN
    ABBREV_TAC `n = n1 + n2 + N + N3:num` THEN
    SUBGOAL_THEN `n <= (sub:num->num) n` ASSUME_TAC THENL
     [MP_TAC(SPEC `sub:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:B` STRIP_ASSUME_TAC) THEN
    USE_THEN "n2" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:B` STRIP_ASSUME_TAC) THEN
    USE_THEN "N3" (MP_TAC o SPEC `(sub:num->num) n + N0`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `n <= (sub:num->num) n` THEN EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "orbin" o REWRITE_RULE[p2bkf_phi])))))))) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `y1:B`;
                   `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v d`]
                  MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `y2:B`;
                   `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v (--d)`]
                  MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`(sub:num->num) n + N0`; `a:B`; `b:B`; `y1:B`; `y2:B`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `n <= (sub:num->num) n` THEN EXPAND_TAC "n" THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the line, its splitting field, and the contradiction *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`;
                 `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v d`;
                 `mfd_geo (top',atlas') ((g':real->B->real^3^3) (&0)) xl v (--d)`]
                P2BX0R_LINE_FROM_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real->B` (CONJUNCTS_THEN2 (LABEL_TAC "line")
    (CONJUNCTS_THEN2 (LABEL_TAC "lam0") (LABEL_TAC "far")))) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `lam:real->B`; `v:real^3`; `d:real`]
                P2BX0R_BUSEMANN_ORTHO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "secl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      (ASM_REWRITE_TAC[] THEN USE_THEN "far" (MP_TAC o SPEC `t:real`) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]])];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME `(lam:real->B)(&0) = xl`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `X':B->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `X':B->real^3`; `xl:B`; `v:real^3`]
                P2BX0R_SCALAR_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The route theorem. *)

let P2B_GSPLIT_SLICE_BOUND_ROUTE = prove
 (`!w:B->bool. P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT] THEN
  MATCH_ACCEPT_TAC P2BX0R_SLICE_BOUND_BODY);;

