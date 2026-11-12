(* ========================================================================= *)
(* pc_p3e_surgmetric: step S4b of the proof of MT Lemma 15.11.  The metric   *)
(* of the new stage Y at the surgery time T: on old points the limit metric  *)
(* gl, on the minus caps the transport of Theorem 13.2's metric gS (for the  *)
(* neck metric gN i, the pullback of the preview metric by the neck chart)   *)
(* through the model parametrization Phi i (e i o p3_std_nc on s1 < 0,       *)
(* cm i o p3e_theta on s1 > -sqrt 2 log 2).  Results: the glued metric       *)
(* (pc_p3e_mglue with the cap fields mpullback p3e_thinv (gS i)) is          *)
(* Riemannian, equals gl on the old points, is pinched at T, and every       *)
(* surgery neck has the cap parametrization of p3_cap_param (raw form        *)
(* p3e_capraw, bridge P3E_CAP_PARAM_RAW).                                    *)
(* ========================================================================= *)

needs "src/pc_p3e_mglue.ml";;
needs "src/pc_p3e_theta.ml";;
needs "src/pc_p3_route.ml";;
needs "src/pc_p3_inv.ml";;
needs "src/pc_p3_s13cap.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The raw cap-parametrization predicate p3e_capraw (the text                *)
(* of p3_cap_param with the history's fields as parameters) and its bridge;  *)
(* Theorem 13.2 at fixed (g0,A0) with its constants (p3e_t132); the         *)
(* hypothesis bundle p3e_smdata of S4b.                                     *)
(* ------------------------------------------------------------------------- *)

let p3e_capraw = new_definition
 `p3e_capraw (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real,h:real)
             (topY:B topology,atlasY:((B->bool)#(B->real^3))->bool,gY:B->real^3^3)
             (en:real^3->B) (cm:real^3->B) (gN:real^3->real^3^3)
             (Phi:real^3->B) (xi:real^3->real^3) <=>
    (A0 + &4) * dl < &1 /\
    mfd_param topY atlasY {x | --(inv dl) < A0 + &4 - p3_std_dist g0 x} Phi /\
    (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < &0
         ==> Phi x = en (p3_std_nc g0 A0 x)) /\
    IMAGE Phi {x | &0 <= A0 + &4 - p3_std_dist g0 x} = IMAGE cm (cball(vec 0,&1)) /\
    (!dd. &0 < dd /\ dl <= md dd
          ==> rfs_close_on (rfs_kreg dd) dd
                {x | p3_std_dist g0 x < inv dd /\
                     --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                g0 (\x. inv(h pow 2) %% rfs_pullback atlasY Phi gY x)) /\
    (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
             ==> &0 < mfd_sectional atlasY gY (Phi x) u v) /\
    smooth_map_on (rfs_neck_dom dl) xi /\
    (!y. y IN rfs_neck_dom dl
         ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (xi y) /\
             (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (xi y) = y) /\
             (&0 <= sqrt(&2) * log(norm y) ==> &0 <= A0 + &4 - p3_std_dist g0 (xi y)) /\
             (A0 + &4 <= sqrt(&2) * log(norm y) ==> xi y = vec 0)) /\
    (!y v. y IN rfs_neck_dom dl
           ==> (jacobian xi (at y) ** v) dot
               (rfs_pullback atlasY Phi gY (xi y) ** (jacobian xi (at y) ** v)) <=
               v dot (gN y ** v))`;;

let P3E_CAP_PARAM_RAW = prove
 (`!md g0 A0 dl h (hs:(B)rfs_history) k i Phi xi.
     p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi <=>
     p3e_capraw (md,g0,A0) (dl(hs_time hs k),h(hs_time hs k))
                (hs_top hs k,hs_atlas hs k,hs_metric hs k (hs_time hs k))
                (ev_neck(hs_event hs k) i) (ev_capm(hs_event hs k) i)
                (rfs_pullback (rfs_vatlas (rfs_preview hs k) (hs_time hs k))
                              (ev_neck (hs_event hs k) i)
                              (rfs_vmetric (rfs_preview hs k) (hs_time hs k)))
                Phi xi`,
  REWRITE_TAC[p3_cap_param; p3e_capraw]);;

let p3e_t132 = new_definition
 `p3e_t132 (g0:real^3->real^3^3) (A0:real) (d0:real) (h0:real) (md:real->real) <=>
    &0 < d0 /\ (A0 + &4) * d0 < &1 /\ &0 < h0 /\ p3_modulus md /\
    !dl h t gN.
       &0 < dl /\ dl <= d0 /\ &0 < h /\ h <= h0 /\ &0 <= t /\
       riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
       rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                    (\y. inv(h pow 2) %% gN y) /\
       (!y. y IN rfs_neck_dom dl
            ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl)) gN t y)
       ==> ?gS xi.
             riemannian_metric
               (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z}) gS /\
             (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                  A0 + &4 - p3_std_dist g0 x < &0
                  ==> gS x = mpullback (p3_std_nc g0 A0) gN x) /\
             (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x
                  ==> rfs_pinched_at
                        (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                        gS t x) /\
             (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
                      ==> &0 < mfd_sectional
                                 (open_set_atlas
                                    {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                                 gS x u v) /\
             (!dd. &0 < dd /\ dl <= md dd
                   ==> rfs_close_on (rfs_kreg dd) dd
                         {x | p3_std_dist g0 x < inv dd /\
                              --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                         g0 (\x. inv(h pow 2) %% gS x)) /\
             smooth_map_on (rfs_neck_dom dl) (xi:real^3->real^3) /\
             (!y. y IN rfs_neck_dom dl
                  ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (xi y) /\
                      (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (xi y) = y) /\
                      (&0 <= sqrt(&2) * log(norm y)
                       ==> &0 <= A0 + &4 - p3_std_dist g0 (xi y)) /\
                      (A0 + &4 <= sqrt(&2) * log(norm y) ==> xi y = vec 0)) /\
             (!y v. y IN rfs_neck_dom dl
                    ==> (jacobian xi (at y) ** v) dot
                        (gS (xi y) ** (jacobian xi (at y) ** v)) <=
                        v dot (gN y ** v))`;;

let P3E_T132 = prove
 (`P3_THM_13_2_STATEMENT
   ==> !g0 A0. p3_std_initial g0 A0 ==> ?d0 h0 md. p3e_t132 g0 A0 d0 h0 md`,
  REWRITE_TAC[P3_THM_13_2_STATEMENT; p3e_t132]);;

let p3e_smdata = new_definition
 `p3e_smdata (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
             (e:num->real^3->B) (nw:num->bool->real^3->B) (D:B->bool) (Om:B->bool)
             (gl:B->real^3^3) (g0:real^3->real^3^3) (A0:real) (d0:real) (h0:real)
             (md:real->real) (dl:real) (h:real) (ts:real) (yc:num->B) <=>
    p3e_cutdata topX atlasX J e nw /\
    open_in (p3e_ctop topX J e nw) D /\ closed_in (p3e_ctop topX J e nw) D /\
    (!i. i IN J
         ==> IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET D /\
             DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0,&1))) D) /\
    open_in topX Om /\
    p3e_ysp topX J e nw D INTER topspace topX SUBSET Om /\
    (!c. c IN atlasX
         ==> metric_field (IMAGE (SND c) (FST c INTER Om)) (metric_local atlasX c gl)) /\
    riemannian_metric (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) /\
    (!q. q IN Om
         ==> rfs_pinched_at (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) ts q) /\
    p3_std_initial g0 A0 /\ p3e_t132 g0 A0 d0 h0 md /\
    &0 < dl /\ dl <= d0 /\ &0 < h /\ h <= h0 /\ &0 <= ts /\
    (!i. i IN J
         ==> rfs_neck (subtopology topX Om,restrict_atlas atlasX Om)
                      (restrict_metric atlasX Om gl) dl (yc i) (e i) /\
             mfd_scalar (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) (yc i) =
             inv(h pow 2) /\
             IMAGE (e i) {y | y IN rfs_neck_dom dl /\ norm y < &1}
             SUBSET p3e_ysp topX J e nw D) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (rfs_neck_dom dl)) (IMAGE (e j) (rfs_neck_dom dl)))`;;

(* ------------------------------------------------------------------------- *)
(* Generic transfer lemmas.  Sets of sectional curvatures of                 *)
(* planes agree under a linear isomorphism of the plane vectors; the scalar *)
(* curvature, the minimal sectional curvature and the pinching condition of  *)
(* a metric at e y agree with those of its pullback by a parametrization e  *)
(* (in the identity chart of s) at y; the pullback of the restricted metric  *)
(* to an open submanifold by a parametrization of it is the pullback of the  *)
(* metric.                                                                   *)
(* ------------------------------------------------------------------------- *)

let P3E_SECSET_LINEAR = prove
 (`!(f:real^3->real^3->real) f' (L:real^3->real^3) L'.
     linear L /\ (!w. L'(L w) = w) /\ (!w. L(L' w) = w) /\
     (!u v. f u v = f' (L u) (L v))
     ==> {f u v | u,v | ~collinear {vec 0,u,v}} =
         {f' u v | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u v. collinear {vec 0:real^3,(L:real^3->real^3) u,L v} <=> collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`L:real^3->real^3`; `{vec 0:real^3,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]);
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(L:real^3->real^3) u`; `(L:real^3->real^3) v`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(L':real^3->real^3) u`; `(L':real^3->real^3) v`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let P3E_SECSET_PARAM = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s
     ==> {mfd_sectional (open_set_atlas s) (rfs_pullback atlas e g) y u v |
          u,v | ~collinear {vec 0,u,v}} =
         {mfd_sectional atlas g (e y) u v | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> can (find_term ((=) `IMAGE (e:real^3->A) s`)) (concl th) &&
                       is_comb(concl th) &&
                       can (find_term ((=) `open_in:(A)topology->(A->bool)->bool`))
                           (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y))`]
    APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^3` (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] LRG_DIFFEO_DERIV)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_SECSET_LINEAR THEN
  MAP_EVERY EXISTS_TAC
   [`frechet_derivative
       (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e)
       (at y)`;
    `frechet_derivative
       ((e2:A->real^3) o
        chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)))
       (at ((SND(chart_at atlas (e y)) o e) y))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[P3S_OPEN_MFD_SECTIONAL] THEN
  MATCH_MP_TAC APX_PULLBACK_SECTIONAL_GEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[]);;

let P3E_PINCHED_PARAM = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) t y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s
     ==> mfd_scalar (open_set_atlas s) (rfs_pullback atlas e g) y = mfd_scalar atlas g (e y) /\
         mfd_sec_min (open_set_atlas s) (rfs_pullback atlas e g) y =
         mfd_sec_min atlas g (e y) /\
         (rfs_pinched_at (open_set_atlas s) (rfs_pullback atlas e g) t y <=>
          rfs_pinched_at atlas g t (e y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN
   `mfd_scalar (open_set_atlas s) (rfs_pullback atlas e g) y =
    mfd_scalar atlas (g:A->real^3^3) (e y)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC APX_PULLBACK_SCALAR_GEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_sec_min (open_set_atlas s) (rfs_pullback atlas e g) y =
    mfd_sec_min atlas (g:A->real^3^3) (e y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_sec_min] THEN AP_TERM_TAC THEN MATCH_MP_TAC P3E_SECSET_PARAM THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_pinched_at]);;

let P3E_PULLBACK_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^3^3) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     mfd_param (subtopology top W) (restrict_atlas atlas W) s e /\ y IN s
     ==> rfs_pullback (restrict_atlas atlas W) e (restrict_metric atlas W g) y =
         rfs_pullback atlas e g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `s:real^3->bool`; `e:real^3->A`] APX_PARAM_FROM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `(e:real^3->A) y`] MFDR_CHART_AT_RESTRICT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `s:real^3->bool`; `e:real^3->A`; `U:A->bool`; `phi:A->real^3`; `y:real^3`]
    APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN ASM_REWRITE_TAC[SND] THEN
  REWRITE_TAC[mpullback; o_THM] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The surgery necks and Theorem 13.2.  For i IN J the neck                  *)
(* chart e i parametrizes the preview (X restricted to Om) and X over the   *)
(* neck domain; the neck metric gN i (pullback of the preview metric) has   *)
(* the hypotheses of 13.2 at time ts (riemannian, h-close to the cylinder,  *)
(* pinched); hence the cap metrics gS i and maps xi i (p3e_gsok, the        *)
(* conclusion of 13.2), chosen as functions of i.                           *)
(* ------------------------------------------------------------------------- *)

let p3e_gsok = new_definition
 `p3e_gsok (g0:real^3->real^3^3) (A0:real) (md:real->real) (dl:real) (h:real) (t:real)
           (gN:real^3->real^3^3) (gS:real^3->real^3^3) (xi:real^3->real^3) <=>
    riemannian_metric
      (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z}) gS /\
    (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
         A0 + &4 - p3_std_dist g0 x < &0
         ==> gS x = mpullback (p3_std_nc g0 A0) gN x) /\
    (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x
         ==> rfs_pinched_at
               (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z}) gS t x) /\
    (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
             ==> &0 < mfd_sectional
                        (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                        gS x u v) /\
    (!dd. &0 < dd /\ dl <= md dd
          ==> rfs_close_on (rfs_kreg dd) dd
                {x | p3_std_dist g0 x < inv dd /\
                     --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                g0 (\x. inv(h pow 2) %% gS x)) /\
    smooth_map_on (rfs_neck_dom dl) xi /\
    (!y. y IN rfs_neck_dom dl
         ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (xi y) /\
             (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (xi y) = y) /\
             (&0 <= sqrt(&2) * log(norm y) ==> &0 <= A0 + &4 - p3_std_dist g0 (xi y)) /\
             (A0 + &4 <= sqrt(&2) * log(norm y) ==> xi y = vec 0)) /\
    (!y v. y IN rfs_neck_dom dl
           ==> (jacobian xi (at y) ** v) dot (gS (xi y) ** (jacobian xi (at y) ** v)) <=
               v dot (gN y ** v))`;;

let P3E_T132_GSOK = prove
 (`!g0 A0 d0 h0 md dl h t gN.
     p3e_t132 g0 A0 d0 h0 md /\
     &0 < dl /\ dl <= d0 /\ &0 < h /\ h <= h0 /\ &0 <= t /\
     riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
     rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                  (\y. inv(h pow 2) %% gN y) /\
     (!y. y IN rfs_neck_dom dl
          ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl)) gN t y)
     ==> ?gS xi. p3e_gsok g0 A0 md dl h t gN gS xi`,
  REWRITE_TAC[p3e_t132; p3e_gsok] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`dl:real`; `h:real`; `t:real`; `gN:real^3->real^3^3`]) THEN
  ASM_REWRITE_TAC[]);;

let P3E_SM_NECK = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc i.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\ i IN J
     ==> mfd_param (subtopology topX Om) (restrict_atlas atlasX Om) (rfs_neck_dom dl)
                   (e i) /\
         mfd_param topX atlasX (rfs_neck_dom dl) (e i) /\
         IMAGE (e i) (rfs_neck_dom dl) SUBSET Om /\
         riemannian_metric (open_set_atlas (rfs_neck_dom dl))
           (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl)) /\
         rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
           (\y. inv(h pow 2) %%
                rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl) y) /\
         (!y. y IN rfs_neck_dom dl
              ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl))
                    (rfs_pullback (restrict_atlas atlasX Om) (e i)
                                  (restrict_metric atlasX Om gl)) ts y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  SUBGOAL_THEN
   `rfs_neck (subtopology topX Om,restrict_atlas atlasX Om)
             (restrict_metric atlasX Om gl) dl ((yc:num->B) i) (e i) /\
    mfd_scalar (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl) (yc i) =
    inv(h pow 2)`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `Om:B->bool`;
                 `rfs_neck_dom dl`; `(e:num->real^3->B) i`] APX_PARAM_FROM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(rfs_neck_dom dl:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `subtopology topX (Om:B->bool)` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
        (\y. mfd_scalar (restrict_atlas atlasX Om) (restrict_metric atlasX Om gl)
                        ((yc:num->B) i) %%
             rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl) y)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology topX (Om:B->bool)`;
                   `restrict_atlas (atlasX:((B->bool)#(B->real^3))->bool) Om`;
                   `restrict_metric (atlasX:((B->bool)#(B->real^3))->bool) Om gl`;
                   `rfs_neck_dom dl`;
                   `(e:num->real^3->B) i`; `ts:real`; `y:real^3`] P3E_PINCHED_PARAM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constants (c = sqrt 2 log 2 < 2 < 4 < inv dl), the neck                   *)
(* domain contains annulus(1/2,2) and the minus collar; the cap metrics gS i *)
(* and xi i as functions of i; the cap fields p3e_gcap = mpullback          *)
(* p3e_thinv (gS i) satisfy p3e_mgdata.                                      *)
(* ------------------------------------------------------------------------- *)

let P3E_SM_CONSTS = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc
     ==> &0 < sqrt(&2) * log(&2) /\ sqrt(&2) * log(&2) < &2 /\ sqrt(&2) < &2 /\
         &0 < A0 /\ (A0 + &4) * dl < &1 /\ A0 + &4 < inv dl /\ &4 < inv dl /\
         &0 < dl /\ dl < &1 / &4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_smdata; p3e_t132] THEN STRIP_TAC THEN
  MP_TAC P3E_SQRT2_LOG2 THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) < &2 /\ log(&2) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A0 + &4) * dl < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A0 + &4) * d0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &4 < inv dl` ASSUME_TAC THENL
   [SUBGOAL_THEN `A0 + &4 < &1 / dl` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; REWRITE_TAC[real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A0 * dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log(&2) <= sqrt(&2) * &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_SM_NECKDOM = prove
 (`!dl x:real^3.
     &0 < dl /\ dl < &1 / &4 /\
     (&1 / &2 < norm x /\ norm x < &2 \/
      exp(--(inv(sqrt(&2) * dl))) < norm x /\ norm x < &1)
     ==> x IN rfs_neck_dom dl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&1 <= inv(sqrt(&2) * dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[P3E_SQRT2_LOG2] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&1 / &4)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `t = inv(sqrt(&2) * dl)` THEN
  SUBGOAL_THEN `&2 <= exp t /\ exp(--t) <= &1 / &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= exp t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
    MP_TAC(SPECL [`&2`; `exp t`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_MPULLBACK_EQ_OPEN = prove
 (`!(f:real^3->real^3) g G s z.
     open s /\ z IN s /\ (!w. w IN s ==> f w = g w)
     ==> mpullback f G z = mpullback g G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (f:real^3->real^3) (at z) = frechet_derivative g (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let P3E_MPULLBACK_POINT = prove
 (`!(h:real^3->real^3) G1 G2 y.
     G1 (h y) = G2 (h y) ==> mpullback h G1 y = mpullback h G2 y`,
  SIMP_TAC[mpullback]);;

let P3E_THINV_COLLAR = prove
 (`!g0 A0 w:real^3.
     p3_std_initial g0 A0 /\ &1 < norm w /\ norm w < &2
     ==> --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 (p3e_thinv g0 A0 w) /\
         A0 + &4 - p3_std_dist g0 (p3e_thinv g0 A0 w) < &0 /\
         p3e_theta g0 A0 (p3e_thinv g0 A0 w) = w /\
         p3_std_nc g0 A0 (p3e_thinv g0 A0 w) = inv(norm w pow 2) % w /\
         ~(p3e_thinv g0 A0 w = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = p3e_thinv g0 A0 (w:real^3)` THEN
  SUBGOAL_THEN
   `--(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x /\ p3e_theta g0 A0 x = w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &4 - p3_std_dist g0 x < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN cball(vec 0,&1)` MP_TAC THENL
     [UNDISCH_TAC
       `IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
        cball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o
    check (fun th -> can (find_term ((=) `p3_std_nc g0 A0`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `p3e_theta g0 A0 x = (w:real^3)` THEN
  ASM_REWRITE_TAC[p3e_theta; VECTOR_MUL_RZERO] THEN DISCH_TAC THEN
  UNDISCH_TAC `&1 < norm(w:real^3)` THEN
  ASM_MESON_TAC[NORM_0; REAL_LT_ANTISYM; REAL_LT_01]);;

let P3E_SM_GSFUN = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc
     ==> ?gS xi. !i. i IN J
                     ==> p3e_gsok g0 A0 md dl h ts
                           (rfs_pullback (restrict_atlas atlasX Om) (e i)
                                         (restrict_metric atlasX Om gl))
                           (gS i) (xi i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. ?G X. i IN J
              ==> p3e_gsok g0 A0 md dl h ts
                    (rfs_pullback (restrict_atlas atlasX Om) ((e:num->real^3->B) i)
                                  (restrict_metric atlasX Om gl)) G X`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) IN J` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3E_T132_GSOK THEN MAP_EVERY EXISTS_TAC [`d0:real`; `h0:real`] THEN
    MP_TAC(SPEC_ALL P3E_SM_NECK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p3e_smdata (topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc` THEN
    SIMP_TAC[p3e_smdata];
    REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[]]);;

let p3e_gcap = new_definition
 `p3e_gcap (g0:real^3->real^3^3) (A0:real) (gS:num->real^3->real^3^3) =
    \i. mpullback (p3e_thinv g0 A0) (gS i)`;;

let P3E_SM_MGDATA = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i))
     ==> p3e_mgdata topX atlasX J e nw D Om gl (p3e_gcap g0 A0 gS)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  UNDISCH_THEN `!i b x j c y. (nw:num->bool->real^3->B) i b x = nw j c y
                              ==> i = j /\ (b <=> c) /\ x = y` (K ALL_TAC) THEN
  ASM_REWRITE_TAC[p3e_mgdata; p3e_gcap] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  ABBREV_TAC `M2 = {x | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN
   `!i. i IN J ==> metric_field M2 ((gS:num->real^3->real^3^3) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `{z | --(inv dl) < A0 + &4 - p3_std_dist g0 z}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
          can (find_term ((=) `p3e_gsok`)) (concl th))) THEN
        ASM_REWRITE_TAC[p3e_gsok] THEN SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
      SIMP_TAC[];
      EXPAND_TAC "M2" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`M2:real^3->bool`; `p3e_theta g0 A0`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `z:real^3`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3E_THINV_COLLAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_SM_NECK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `gN = rfs_pullback (restrict_atlas atlasX Om) ((e:num->real^3->B) i)
                                (restrict_metric atlasX Om gl)` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `p3e_gsok`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[p3e_gsok] THEN STRIP_TAC THEN
  ABBREV_TAC `x = p3e_thinv g0 A0 (z:real^3)` THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3e_thinv g0 A0)
                        (mpullback (p3_std_nc g0 A0) (gN:real^3->real^3^3)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3E_MPULLBACK_POINT THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3_std_nc g0 A0 o p3e_thinv g0 A0) (gN:real^3->real^3^3) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_MPULLBACK_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:real^3,&2)` THEN ASM_SIMP_TAC[OPEN_BALL; P3E_THINV_SMOOTH];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[P3S_OPEN_PUNCT; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (\w:real^3. inv(norm w pow 2) % w) (gN:real^3->real^3^3) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3E_MPULLBACK_EQ_OPEN THEN EXISTS_TAC `annulus (&1) (&2):real^3->bool` THEN
    REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `w:real^3`] P3E_THINV_COLLAR) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_MPULLBACK_POINT THEN
  EXPAND_TAC "gN" THEN MATCH_MP_TAC P3E_PULLBACK_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`topX:B topology`; `rfs_neck_dom dl`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_SM_NECKDOM THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(z:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
  SUBGOAL_THEN `inv(&2) < inv(norm(z:real^3)) /\ inv(norm z) < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The model parametrization Phi i of the new cap: e i o                     *)
(* p3_std_nc on s1 < 0, cm i o p3e_theta on s1 >= 0 (the two agree on the   *)
(* collar -c < s1 < 0); it parametrizes Y on the model region s1 > -1/dl    *)
(* (union of the two parametrizations, MFD_PARAM_UNION) and maps the cap     *)
(* s1 >= 0 onto the minus core.                                             *)
(* ------------------------------------------------------------------------- *)

let p3e_phi = new_definition
 `p3e_phi (g0:real^3->real^3^3) (A0:real) (en:real^3->B) (cm:real^3->B) =
    \x. if A0 + &4 - p3_std_dist g0 x < &0 then en (p3_std_nc g0 A0 x)
        else cm (p3e_theta g0 A0 x)`;;

let P3E_SM_NC1 = prove
 (`!g0 A0 dl.
     p3_std_initial g0 A0 /\ &0 < dl
     ==> diffeomorphism_on
           {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                       A0 + &4 - p3_std_dist g0 x < &0}
           {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1}
           (p3_std_nc g0 A0) (p3s_ncinv g0 A0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `--(inv dl)`; `&0`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < A0 /\ &0 < inv dl` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_MESON_TAC[p3_std_initial]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_MUL_LNEG] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let P3E_NECKDOM_SPHERE = prove
 (`!dl w:real^3. &0 < dl /\ norm w = &1 ==> w IN rfs_neck_dom dl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2) * dl)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3E_SQRT2_LOG2];
    ALL_TAC] THEN
  SPEC_TAC(`inv(sqrt(&2) * dl)`,`t:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < exp t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
  MP_TAC(SPECL [`&1`; `exp t`] REAL_LT_INV2) THEN REWRITE_TAC[REAL_INV_1] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_SM_EPARAM = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc i.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\ i IN J
     ==> IMAGE (e i) {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1}
         SUBSET p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J e) /\
         mfd_param topX atlasX
           {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1} (e i) /\
         mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D)
           {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1} (e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_NECK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N1 = {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1}` THEN
  SUBGOAL_THEN
   `open (N1:real^3->bool) /\ N1 SUBSET rfs_neck_dom dl /\
    N1 SUBSET {y | y IN rfs_neck_dom dl /\ norm y < &1}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N1" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM annulus; OPEN_ANNULUS];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P3E_SM_NECKDOM THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3E_SM_NECKDOM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param topX atlasX N1 ((e:num->real^3->B) i)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ei':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param topX atlasX (rfs_neck_dom dl) ((e:num->real^3->B) i)`)) THEN
  SUBGOAL_THEN
   `IMAGE ((e:num->real^3->B) i) N1 SUBSET
    p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_DIFF] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom dl /\ norm y < &1` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `IMAGE ((e:num->real^3->B) i) {y | y IN rfs_neck_dom dl /\ norm y < &1}
        SUBSET p3e_ysp topX J e nw D`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
        check (fun th -> concl th =
          `open_in topX (IMAGE ((e:num->real^3->B) i) (rfs_neck_dom dl))`)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_MFD_CUT_SPHERES; NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `w:real^3`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `j:num = i` THENL
       [UNDISCH_TAC `j:num = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
        SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
         [MATCH_MP_TAC P3E_NECKDOM_SPHERE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `norm(y:real^3) < &1` THEN UNDISCH_TAC `norm(w:real^3) = &1` THEN
        SUBGOAL_THEN `(y:real^3) = w` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_MESON_TAC[]; REAL_ARITH_TAC];
        SUBGOAL_THEN
         `DISJOINT (IMAGE ((e:num->real^3->B) i) (rfs_neck_dom dl))
                   (IMAGE (e j) (rfs_neck_dom dl))`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->B) i y`) THEN
        REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM] THEN
        SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
         [MATCH_MP_TAC P3E_NECKDOM_SPHERE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p3e_ytop; p3e_yatlas] THEN
  MP_TAC(ISPECL [`p3e_ctop (topX:B topology) J e nw`; `p3e_catlas (topX:B topology) atlasX J e nw`;
                 `p3e_ysp (topX:B topology) J e nw D`; `N1:real^3->bool`;
                 `(e:num->real^3->B) i`] APX_PARAM_RESTRICT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[p3e_ysp] THEN
      UNDISCH_TAC `closed_in (p3e_ctop topX J e nw) (D:B->bool)` THEN SIMP_TAC[closed_in];
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC APX_CUT_PARAM THEN
  MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                        `J:num->bool`; `e:num->real^3->B`; `p3e_ccp (e:num->real^3->B) nw`;
                        `p3e_ccm (e:num->real^3->B) nw`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P3E_SM_PHI_COLLAR = prove
 (`!(topX:B topology) atlasX J e nw g0 A0 i x.
     p3e_cutdata topX atlasX J e nw /\ p3_std_initial g0 A0 /\
     --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x
     ==> p3e_phi g0 A0 (e i) (p3e_ccm e nw i) x = p3e_ccm e nw i (p3e_theta g0 A0 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_phi] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    can (find_term ((=) `p3_std_nc g0 A0`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`;
                 `p3e_theta g0 A0 x`] P3E_CAP_VALUES) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_BALL_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let P3E_SM_PHI = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi i.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i)) /\
     i IN J
     ==> mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D)
                   {x | --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                   (p3e_phi g0 A0 (e i) (p3e_ccm e nw i)) /\
         (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < &0
              ==> p3e_phi g0 A0 (e i) (p3e_ccm e nw i) x = e i (p3_std_nc g0 A0 x)) /\
         (!x. --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x
              ==> p3e_phi g0 A0 (e i) (p3e_ccm e nw i) x =
                  p3e_ccm e nw i (p3e_theta g0 A0 x)) /\
         IMAGE (p3e_phi g0 A0 (e i) (p3e_ccm e nw i))
               {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
         IMAGE (p3e_ccm e nw i) (cball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_EPARAM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Phi = p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i)` THEN
  SUBGOAL_THEN
   `!x. --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x
        ==> (Phi:real^3->B) x = p3e_ccm e nw i (p3e_theta g0 A0 x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Phi" THEN MATCH_MP_TAC P3E_SM_PHI_COLLAR THEN
    MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                          `J:num->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\ A0 + &4 - p3_std_dist g0 x < &0
        ==> (Phi:real^3->B) x = (e:num->real^3->B) i (p3_std_nc g0 A0 x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Phi" THEN REWRITE_TAC[p3e_phi] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:B` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `p3e_theta g0 A0 x` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC
         `IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
          cball(vec 0,&1)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(z:real^3) IN cball(vec 0,&1)` THEN
      UNDISCH_TAC
       `IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
        cball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `dl:real`] P3E_SM_NC1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `M1 = {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                               A0 + &4 - p3_std_dist g0 x < &0}` THEN
  ABBREV_TAC `M2 = {x:real^3 | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x}` THEN
  ABBREV_TAC `N1 = {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1}` THEN
  SUBGOAL_THEN `{x | --(inv dl) < A0 + &4 - p3_std_dist g0 x} = M1 UNION (M2:real^3->bool)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M1"; "M2"] THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_UNION THEN
  MAP_EVERY EXISTS_TAC [`(e:num->real^3->B) i o p3_std_nc g0 A0`;
                        `p3e_ccm (e:num->real^3->B) nw i o p3e_theta g0 A0`] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`N1:real^3->bool`; `N1:real^3->bool`; `p3s_ncinv g0 A0`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `ball(vec 0:real^3,&2)`;
                          `p3e_thinv g0 A0`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC P3E_MG_CM_PARAM THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `p3e_gcap g0 A0 gS`] THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "M1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    EXPAND_TAC "M2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; o_THM] THEN X_GEN_TAC `p:B` THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `(x:real^3) IN M1` THEN EXPAND_TAC "M1" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `(x:real^3) IN M2` THEN EXPAND_TAC "M2" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `x2:real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `x2:real^3` THEN
  SUBGOAL_THEN `--(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x2` ASSUME_TAC THENL
   [UNDISCH_TAC `(x2:real^3) IN M2` THEN EXPAND_TAC "M2" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:B) IN topspace topX` ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_std_nc g0 A0 x1 IN (N1:real^3->bool)` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        GEN_REWRITE_RULE I [diffeomorphism_on] o
        check (fun th -> can (find_term ((=) `N1:real^3->bool`)) (concl th) &&
                         can (find_term ((=) `p3s_ncinv g0 A0`)) (concl th))) THEN
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &4 - p3_std_dist g0 x2 < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p3e_theta g0 A0 x2 IN cball(vec 0,&1)` MP_TAC THENL
     [UNDISCH_TAC
       `IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
        cball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `x2:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
    UNDISCH_TAC `(p:B) IN topspace topX` THEN
    UNDISCH_TAC `p = p3e_ccm (e:num->real^3->B) nw i (p3e_theta g0 A0 x2)` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[p3e_ccm];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `p3e_ccm (e:num->real^3->B) nw i (p3e_theta g0 A0 x2)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    EXPAND_TAC "M1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The key identity: the pullback of the glued metric by the                 *)
(* model parametrization Phi i is Theorem 13.2's metric gS i on the model    *)
(* region (on s1 < 0 through the neck: the pullback of gl by e i o nc is     *)
(* mpullback nc gN; on s1 > -c through the cap chart: mpullback theta of the *)
(* cap field mpullback thinv (gS i)).                                        *)
(* ------------------------------------------------------------------------- *)

let P3E_PARAM_CHART_DIFF = prove
 (`!top atlas s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\ y IN s
     ==> (SND(chart_at atlas (e y)) o e) differentiable at y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> can (find_term ((=) `IMAGE (e:real^3->A) s`)) (concl th) &&
                       is_comb(concl th) &&
                       can (find_term ((=) `open_in:(A)topology->(A->bool)->bool`))
                           (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y))`]
    APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR; diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^3->A) z IN
                   FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (e y))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let P3E_SM_KEY = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi i x.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i)) /\
     i IN J /\ --(inv dl) < A0 + &4 - p3_std_dist g0 x
     ==> rfs_pullback (p3e_yatlas topX atlasX J e nw D)
                      (p3e_phi g0 A0 (e i) (p3e_ccm e nw i))
                      (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS)) x =
         gS i x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MGLUE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_PHI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_SM_EPARAM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_SM_NECK) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `p3e_gsok`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[p3e_gsok] THEN STRIP_TAC THEN
  ABBREV_TAC `gT = p3e_gmet (topX:B topology) atlasX J e nw D gl (p3e_gcap g0 A0 gS)` THEN
  ABBREV_TAC `Phi = p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i)` THEN
  ASM_CASES_TAC `A0 + &4 - p3_std_dist g0 x < &0` THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `dl:real`] P3E_SM_NC1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `M1 = {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                                 A0 + &4 - p3_std_dist g0 x < &0}` THEN
    ABBREV_TAC `N1 = {y:real^3 | exp(--(inv(sqrt(&2) * dl))) < norm y /\ norm y < &1}` THEN
    SUBGOAL_THEN `open (M1:real^3->bool) /\ (x:real^3) IN M1 /\ p3_std_nc g0 A0 x IN N1`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
        check (fun th -> can (find_term ((=) `N1:real^3->bool`)) (concl th) &&
                         can (find_term ((=) `p3s_ncinv g0 A0`)) (concl th))) THEN
      SUBGOAL_THEN `(x:real^3) IN M1` ASSUME_TAC THENL
       [EXPAND_TAC "M1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `A0 + &4 - p3_std_dist g0 x < &0` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `vec 0:real^3`] P3S_ROT_DIST) THEN
      ASM_REWRITE_TAC[NORM_0; P3S_RHO_0] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param topX atlasX M1 ((e:num->real^3->B) i o p3_std_nc g0 A0) /\
      mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D) M1
                (e i o p3_std_nc g0 A0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`N1:real^3->bool`; `N1:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                             (e i o p3_std_nc g0 A0) gT x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_RFS_PULLBACK_LOCAL THEN EXISTS_TAC `M1:real^3->bool` THEN
      ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `w:real^3` THEN
      EXPAND_TAC "M1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfs_pullback atlasX ((e:num->real^3->B) i o p3_std_nc g0 A0) gl x` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `rfs_pullback (atlasX:((B->bool)#(B->real^3))->bool)`)) (concl th) &&
        is_forall(concl th) && can (find_term ((=) `mfd_param:(B)topology->((B->bool)#(B->real^3)->bool)->(real^3->bool)->(real^3->B)->bool`)) (concl th))) THEN
      EXISTS_TAC `M1:real^3->bool` THEN ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (p3_std_nc g0 A0) (rfs_pullback atlasX ((e:num->real^3->B) i) gl) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_RFS_PULLBACK_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[P3S_OPEN_PUNCT; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV];
        MATCH_MP_TAC P3E_PARAM_CHART_DIFF THEN
        MAP_EVERY EXISTS_TAC [`topX:B topology`; `rfs_neck_dom dl`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P3E_SM_NECKDOM THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
        UNDISCH_TAC `p3_std_nc g0 A0 x IN (N1:real^3->bool)` THEN EXPAND_TAC "N1" THEN
        REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (p3_std_nc g0 A0)
                  (rfs_pullback (restrict_atlas atlasX Om) ((e:num->real^3->B) i)
                                (restrict_metric atlasX Om gl)) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3E_MPULLBACK_POINT THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P3E_PULLBACK_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`topX:B topology`; `rfs_neck_dom dl`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3E_SM_NECKDOM THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      UNDISCH_TAC `p3_std_nc g0 A0 x IN (N1:real^3->bool)` THEN EXPAND_TAC "N1" THEN
      REWRITE_TAC[IN_ELIM_THM];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `M2 = {x:real^3 | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x}` THEN
  SUBGOAL_THEN `(x:real^3) IN M2` ASSUME_TAC THENL
   [EXPAND_TAC "M2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    check (fun th -> can (find_term ((=) `M2:real^3->bool`)) (concl th) &&
                     can (find_term ((=) `p3e_thinv g0 A0`)) (concl th) &&
                     can (find_term ((=) `diffeomorphism_on:(real^3->bool)->(real^3->bool)->(real^3->real^3)->(real^3->real^3)->bool`)) (concl th))) THEN
  SUBGOAL_THEN `p3e_theta g0 A0 x IN ball(vec 0,&2)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                           (p3e_ccm e nw i o p3e_theta g0 A0) gT x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_RFS_PULLBACK_LOCAL THEN EXISTS_TAC `M2:real^3->bool` THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(w:real^3) IN M2` THEN
    UNDISCH_TAC `{x:real^3 | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x} = M2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3e_theta g0 A0)
                (rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                              (p3e_ccm e nw i) gT) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_RFS_PULLBACK_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `M2:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3E_PARAM_CHART_DIFF THEN
      MAP_EVERY EXISTS_TAC [`p3e_ytop (topX:B topology) J e nw D`; `ball(vec 0:real^3,&2)`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3e_theta g0 A0)
                (mpullback (p3e_thinv g0 A0) ((gS:num->real^3->real^3^3) i)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3E_MPULLBACK_POINT THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[p3e_gcap];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (p3e_thinv g0 A0 o p3e_theta g0 A0) ((gS:num->real^3->real^3^3) i) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_MPULLBACK_COMPOSE THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `M2:real^3->bool`; EXISTS_TAC `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3E_MPULLBACK_ID_OPEN THEN EXISTS_TAC `M2:real^3->bool` THEN
    ASM_SIMP_TAC[o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Transfer of pinching and of positive sectional curvature                  *)
(* through parametrizations and equal metric fields on open sets; the raw   *)
(* cap parametrization clauses p3e_capraw for every surgery neck (13.2's    *)
(* closeness, xi and Jacobian clauses through the key identity).            *)
(* ------------------------------------------------------------------------- *)

let P3E_PINCHED_OPEN_CONG = prove
 (`!s (G1:real^3->real^3^3) G2 t y.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> (rfs_pinched_at (open_set_atlas s) G1 t y <=>
          rfs_pinched_at (open_set_atlas s) G2 t y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_scalar (open_set_atlas s) (G1:real^3->real^3^3) y =
    mfd_scalar (open_set_atlas s) (G2:real^3->real^3^3) y /\
    mfd_sec_min (open_set_atlas s) G1 y = mfd_sec_min (open_set_atlas s) G2 y`
  (fun th -> REWRITE_TAC[rfs_pinched_at; th]) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR] THEN MATCH_MP_TAC LSCALAR_LOCAL THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_sec_min] THEN AP_TERM_TAC THEN ASM_SIMP_TAC[P3S_OPEN_MFD_SECTIONAL] THEN
    SUBGOAL_THEN `!u v. lsectional G1 y u v = lsectional (G2:real^3->real^3^3) y u v`
    (fun th -> REWRITE_TAC[th]) THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let P3E_SECPOS_PARAM = prove
 (`!top atlas (g:A->real^3^3) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s /\
     (!u v. ~collinear {vec 0,u,v}
            ==> &0 < mfd_sectional (open_set_atlas s) (rfs_pullback atlas e g) y u v)
     ==> !u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g (e y) u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_SECSET_PARAM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `mfd_sectional atlas (g:A->real^3^3) ((e:real^3->A) y) u v`) THEN
  MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[]]);;

let P3E_SM_CAPRAW = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi i.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i)) /\
     i IN J
     ==> p3e_capraw (md,g0,A0) (dl,h)
           (p3e_ytop topX J e nw D,p3e_yatlas topX atlasX J e nw D,
            p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS))
           (e i) (p3e_ccm e nw i)
           (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
           (p3e_phi g0 A0 (e i) (p3e_ccm e nw i)) (xi i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MGLUE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  MP_TAC(SPEC_ALL P3E_SM_PHI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x
        ==> rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                         (p3e_phi g0 A0 (e i) (p3e_ccm e nw i))
                         (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS)) x =
            (gS:num->real^3->real^3^3) i x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_SM_KEY THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `d0:real`; `h0:real`; `md:real->real`; `dl:real`;
                          `h:real`; `ts:real`; `yc:num->B`; `xi:num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `p3e_gsok`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[p3e_gsok] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3e_capraw] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `dd:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th) &&
      is_forall(concl th))) THEN
    ASM_REWRITE_TAC[rfs_close_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= d ==> a <= d`) THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `{x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN {x | p3_std_dist g0 x < inv dd /\
                                       --(inv dl) < A0 + &4 - p3_std_dist g0 x}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `p3e_gmet (topX:B topology) atlasX J e nw D gl (p3e_gcap g0 A0 gS)`;
                   `{x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}`;
                   `p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i)`; `x:real^3`]
      P3E_SECPOS_PARAM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN {x | --(inv dl) < A0 + &4 - p3_std_dist g0 x}`
      ASSUME_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[P3S_OPEN_MFD_SECTIONAL] THEN
      SUBGOAL_THEN
       `lsectional (rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                     (p3e_phi g0 A0 (e i) (p3e_ccm e nw i))
                     (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS))) x u' v' =
        lsectional ((gS:num->real^3->real^3^3) i) x u' v'`
      SUBST1_TAC THENL
       [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
        EXISTS_TAC `{x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `u':real^3`; `v':real^3`] o
        check (fun th -> can (find_term (fun t -> is_const t &&
                                fst(dest_const t) = "mfd_sectional")) (concl th) &&
                         can (find_term ((=) `open_set_atlas:(real^3->bool)->((real^3->bool)#(real^3->real^3)->bool)`)) (concl th) &&
                         is_forall(concl th))) THEN
      ASM_SIMP_TAC[P3S_OPEN_MFD_SECTIONAL];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                   (p3e_phi g0 A0 (e i) (p3e_ccm e nw i))
                   (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS))
                   ((xi:num->real^3->real^3) i y) =
      (gS:num->real^3->real^3^3) i (xi i y)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The glued metric is pinched at time ts at every point of Y:               *)
(* at an old point through the inverse of a restricted X chart (the glued    *)
(* metric and the restricted preview metric have the same pullback there),   *)
(* at a core point through Phi i (its pullback is gS i, pinched by 13.2).   *)
(* ------------------------------------------------------------------------- *)

let P3E_SM_OLDCHART = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi p.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i)) /\
     p IN p3e_ysp topX J e nw D /\ p IN topspace topX
     ==> ?s f y. open s /\ y IN s /\ f y = p /\
                 mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D) s f /\
                 mfd_param topX atlasX s f /\
                 mfd_param (subtopology topX Om) (restrict_atlas atlasX Om) s f /\
                 (!z. z IN s ==> f z IN p3e_ysp topX J e nw D INTER topspace topX)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP P3E_MG_OLD th)))) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(last(CONJUNCTS(MATCH_MP P3E_MG_OLD th)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `p:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) p` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  ABBREV_TAC `S = p3e_ysp (topX:B topology) J e nw D INTER topspace topX` THEN
  EXISTS_TAC `IMAGE (psi:B->real^3) (V INTER S)` THEN
  EXISTS_TAC `chart_inv (V INTER S:B->bool,psi:B->real^3)` THEN
  EXISTS_TAC `(psi:B->real^3) p` THEN
  SUBGOAL_THEN `(p:B) IN S` ASSUME_TAC THENL [EXPAND_TAC "S" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(V INTER S:B->bool,psi:B->real^3) IN p3e_yatlas topX atlasX J e nw D`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P3E_MG_XCHART_S THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `p3e_gcap g0 A0 gS`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (psi:B->real^3) (V INTER S)
        ==> chart_inv (V INTER S,psi) z IN V INTER S /\
            chart_inv (V INTER S,psi) z = chart_inv (V,psi) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `V:B->bool`; `psi:B->real^3`; `S:B->bool`; `q:B`]
      MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param topX atlasX (IMAGE (psi:B->real^3) (V INTER S))
                         (chart_inv (V INTER S,psi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_EQ THEN EXISTS_TAC `chart_inv (V:B->bool,psi:B->real^3)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (psi:B->real^3) V` THEN
    ASM_SIMP_TAC[MFD_PARAM_CHART_INV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `V:B->bool`; `psi:B->real^3`; `S:B->bool`; `p:B`]
      MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `V INTER S:B->bool`; `psi:B->real^3`] MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `Om:B->bool`;
                   `IMAGE (psi:B->real^3) (V INTER S)`; `chart_inv (V INTER S:B->bool,psi:B->real^3)`]
      APX_PARAM_RESTRICT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let P3E_SM_PINCHED = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc gS xi p.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc /\
     (!i. i IN J
          ==> p3e_gsok g0 A0 md dl h ts
                (rfs_pullback (restrict_atlas atlasX Om) (e i) (restrict_metric atlasX Om gl))
                (gS i) (xi i)) /\
     p IN topspace (p3e_ytop topX J e nw D)
     ==> rfs_pinched_at (p3e_yatlas topX atlasX J e nw D)
                        (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS)) ts p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_SM_CONSTS) THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MGLUE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_smdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  SUBGOAL_THEN `(p:B) IN p3e_ysp topX J e nw D` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(p:B) IN topspace topX` THENL
   [MP_TAC(SPEC_ALL P3E_SM_OLDCHART) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `f:real^3->B`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(f:real^3->B) y = p`)) THEN
    MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `p3e_gmet (topX:B topology) atlasX J e nw D gl (p3e_gcap g0 A0 gS)`;
                   `s:real^3->bool`; `f:real^3->B`; `ts:real`; `y:real^3`]
      P3E_PINCHED_PARAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
    MP_TAC(ISPECL [`subtopology topX (Om:B->bool)`;
                   `restrict_atlas (atlasX:((B->bool)#(B->real^3))->bool) Om`;
                   `restrict_metric (atlasX:((B->bool)#(B->real^3))->bool) Om gl`;
                   `s:real^3->bool`; `f:real^3->B`; `ts:real`; `y:real^3`]
      P3E_PINCHED_PARAM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) /\ c ==> (b <=> c) ==> a`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_PINCHED_OPEN_CONG THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^3->B) z IN p3e_ysp topX J e nw D INTER topspace topX`
      ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `rfs_pullback atlasX (f:real^3->B) gl z` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `rfs_pullback (atlasX:((B->bool)#(B->real^3))->bool)`))
              (concl th) && is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3E_PULLBACK_RESTRICT THEN
        MAP_EVERY EXISTS_TAC [`topX:B topology`; `s:real^3->bool`] THEN
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`;
                `p3e_gcap g0 A0 gS`; `p:B`] P3E_MG_NEWPT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `p:B`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_THETA_FACTS) THEN
  SUBGOAL_THEN
   `?x. &0 <= A0 + &4 - p3_std_dist g0 x /\ p3e_theta g0 A0 x = (z:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} = cball(vec 0,&1)` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_CBALL_0] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL P3E_SM_PHI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i) x = p3e_ccm e nw i z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `p3e_ccm (e:num->real^3->B) nw i (p3e_theta g0 A0 x)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
    `p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i) x = p3e_ccm e nw i z`)) THEN
  SUBGOAL_THEN `(x:real^3) IN {x | --(inv dl) < A0 + &4 - p3_std_dist g0 x}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                 `p3e_gmet (topX:B topology) atlasX J e nw D gl (p3e_gcap g0 A0 gS)`;
                 `{x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}`;
                 `p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i)`; `ts:real`;
                 `x:real^3`] P3E_PINCHED_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
  MP_TAC(ISPECL [`{x:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 x}`;
                 `rfs_pullback (p3e_yatlas (topX:B topology) atlasX J e nw D)
                               (p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i))
                               (p3e_gmet topX atlasX J e nw D gl (p3e_gcap g0 A0 gS))`;
                 `(gS:num->real^3->real^3^3) i`; `ts:real`; `x:real^3`]
    P3E_PINCHED_OPEN_CONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_SM_KEY THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `d0:real`; `h0:real`; `md:real->real`; `dl:real`;
                            `h:real`; `ts:real`; `yc:num->B`; `xi:num->real^3->real^3`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term ((=) `p3e_gsok`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[p3e_gsok] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPEC `dl:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main theorem P3E_SURGMETRIC.  Under p3e_smdata (cut-and-cap data,     *)
(* discarded set D, preview data at the event time ts, Theorem 13.2 at       *)
(* (g0,A0) with its constants), the new stage Y is a compact Hausdorff       *)
(* smooth manifold with a metric gT that is Riemannian, equals gl on the old *)
(* points, is pinched at ts, and gives every surgery neck a cap              *)
(* parametrization (p3e_capraw).                                             *)
(* ------------------------------------------------------------------------- *)

let P3E_SURGMETRIC = prove
 (`!(topX:B topology) atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc.
     p3e_smdata topX atlasX J e nw D Om gl g0 A0 d0 h0 md dl h ts yc
     ==> hausdorff_space (p3e_ytop topX J e nw D) /\
         compact_space (p3e_ytop topX J e nw D) /\
         smooth_manifold_atlas (p3e_ytop topX J e nw D)
                               (p3e_yatlas topX atlasX J e nw D) /\
         topspace (p3e_ytop topX J e nw D) = p3e_ysp topX J e nw D /\
         ?gT. riemannian_metric (p3e_yatlas topX atlasX J e nw D) gT /\
              rfs_same_metric_on atlasX gl (p3e_yatlas topX atlasX J e nw D) gT
                                 (topspace (p3e_ytop topX J e nw D) INTER topspace topX) /\
              (!p. p IN topspace (p3e_ytop topX J e nw D)
                   ==> rfs_pinched_at (p3e_yatlas topX atlasX J e nw D) gT ts p) /\
              (!i. i IN J
                   ==> ?Phi xi.
                         p3e_capraw (md,g0,A0) (dl,h)
                           (p3e_ytop topX J e nw D,p3e_yatlas topX atlasX J e nw D,gT)
                           (e i) (p3e_ccm e nw i)
                           (rfs_pullback (restrict_atlas atlasX Om) (e i)
                                         (restrict_metric atlasX Om gl))
                           Phi xi)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gS:num->real^3->real^3^3`
    (X_CHOOSE_TAC `xi:num->real^3->real^3`) o MATCH_MP P3E_SM_GSFUN) THEN
  MP_TAC(SPEC_ALL P3E_SM_MGDATA) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MGLUE_FACTS) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  EXISTS_TAC `p3e_gmet (topX:B topology) atlasX J e nw D gl (p3e_gcap g0 A0 gS)` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `p:B` THEN DISCH_TAC THEN MATCH_MP_TAC P3E_SM_PINCHED THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `d0:real`; `h0:real`; `md:real->real`; `dl:real`;
                          `h:real`; `yc:num->B`; `xi:num->real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`p3e_phi g0 A0 ((e:num->real^3->B) i) (p3e_ccm e nw i)`;
                          `(xi:num->real^3->real^3) i`] THEN
    MATCH_MP_TAC P3E_SM_CAPRAW THEN
    MAP_EVERY EXISTS_TAC [`d0:real`; `h0:real`; `ts:real`; `yc:num->B`] THEN
    ASM_REWRITE_TAC[]]);;

