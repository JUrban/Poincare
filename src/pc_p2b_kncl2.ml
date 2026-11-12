(* ========================================================================= *)
(* Unit pc_p2b_kncl2: piece (d) of COR_9_94_L, the positively curved case,   *)
(* part 1: the topology of the soul cap.  At the soul p, a neck e3 centred   *)
(* at a point z3 at distance D rho from p (rho = R(p)^(-1/2)), oriented with *)
(* p on its inner side, gives the re-centred necks e' = e3 o (exp c .) and   *)
(* e_out = e3 o (exp 2c .); the ball chart b of (c) part 2 for e' bounds the *)
(* core Y = b(ball 1), which is the p-side of the level sphere at s = -6 of  *)
(* e3 together with the part of e3 below the sphere S of e'.                 *)
(* ========================================================================= *)

needs "src/pc_p2b_kncl1.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_apx_engine.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic tools.  Points at any distance from a base point of a               *)
(* complete noncompact manifold; distances from a compact set are bounded;   *)
(* the exit bound of a neck as a distance bound; R is within a factor 2 on  *)
(* small necks; the orientation of a neck at a point far from a soul with   *)
(* the soul on the negative side.                                           *)
(* ------------------------------------------------------------------------- *)

let KNCL_FAR_POINT = prove
 (`!top atlas (g:A->real^3^3) p r.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ ~compact_space top /\
     p IN topspace top /\ &0 <= r
     ==> ?z. z IN topspace top /\ mfd_dist (top,atlas) g p z = r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?q:A. q IN topspace top /\ r < mfd_dist (top,atlas) (g:A->real^3^3) p q`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    SUBGOAL_THEN `compact_in top (topspace top:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) p r` THEN
      REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `p:A`] MFD_HOPF_RINOW_POINT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[]]];
      ASM_REWRITE_TAC[GSYM compact_space]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) (p:A) q /\ ~(q = p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `p:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `q:A`] P2AS_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^3^3) p u r` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `u:real^3`] CMPB_GEO_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let KNCL_DIST_BOUNDED = prove
 (`!top atlas (g:A->real^N^N) p K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?R0. !x. x IN K ==> mfd_dist (top,atlas) g p x <= R0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\y. mfd_dist (top,atlas) (g:A->real^N^N) p y) K`
               REAL_COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MESON_TAC[REAL_ARITH `abs x <= B ==> x <= B`]]);;

let KNCL_EXIT_DIST = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y q.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps < &1 /\ y IN rfs_neck_dom eps /\
     mfd_joinable (top,atlas) (e y) q /\ ~(q IN IMAGE e (rfs_neck_dom eps))
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) * (inv eps - abs(apx_sval y))
         <= mfd_dist (top,atlas) g (e y) q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(e:real^3->A) y`; `q:A`;
                 `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                  (inv eps - abs(apx_sval(y:real^3)))`] APX_DIST_SHORT_CURVE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `gamma:real->A`;
                 `&0`; `&1`] APX_NECK_EXIT) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let KNCL_NECK_SCALAR = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps z (e:real^3->A) y.
       &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
       rfs_neck (top,atlas) g eps z e /\ y IN rfs_neck_dom eps
       ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g (e y) /\
           mfd_scalar atlas g (e y) <= &3 / &2 * mfd_scalar atlas g z`,
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC APX_NECK_SCALAR_COMPARE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `z:A`; `e:real^3->A`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Orientation.  A point p outside the middle of an eps-neck e               *)
(* (outside e(neck_dom(3/2 eps))) is far from its centre, so the geodesic   *)
(* tail of KNCL_NECK_SIDE joins p to a neck point at level between -46 and *)
(* -35 of e or of its reversal apx_rev e, missing the central sphere.       *)
(* ------------------------------------------------------------------------- *)

let KNCL_SOUL_SIDE = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) p.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps z e /\
     p IN topspace top /\ ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * eps)))
     ==> ?e' K w. rfs_neck (top,atlas) g eps z e' /\
                  connected_in top K /\ p IN K /\
                  K INTER IMAGE e' (sphere(vec 0,&1)) = {} /\
                  w IN rfs_neck_dom eps /\ e' w IN K /\
                  --(&46) <= apx_sval w /\ apx_sval w <= --(&35) /\
                  mfd_dist (top,atlas) g z (e' w) = &45 * inv(sqrt(mfd_scalar atlas g z)) /\
                  mfd_dist (top,atlas) g z (e' w) + mfd_dist (top,atlas) g (e' w) p =
                  mfd_dist (top,atlas) g z p /\
                  (!y. y IN K
                       ==> &45 * inv(sqrt(mfd_scalar atlas g z)) <= mfd_dist (top,atlas) g z y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom (&3 / &2 * eps) /\ apx_sval y0 = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `&3 / &2 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^3->A) y0 = z`)) THEN
    MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `eps:real`; `z:A`] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&45 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) <=
                mfd_dist (top,atlas) g z p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `&3 / &2 * eps`; `z:A`; `e:real^3->A`; `y0:real^3`; `p:A`]
                  KNCL_EXIT_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_MONO) THEN
        REWRITE_TAC[APX_NECK_MONO_STATEMENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&9 / &10 <= sqrt(&1 - &3 / &2 * eps) /\ &50 <= inv(&3 / &2 * eps)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPECL [`&3 / &2 * eps`; `&1 / &50`] REAL_LE_INV2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `s * k * i = (s * i) * k`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&9 / &10 * &50` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `p:A`] KNCL_NECK_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:A->bool` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `apx_sval(w:real^3) < &0` THENL
   [MAP_EVERY EXISTS_TAC [`e:real^3->A`; `K:A->bool`; `w:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->A`; `eps:real`; `w:real^3`] KNCL_REV_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (apx_rev(e:real^3->A)) (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->A) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    SIMP_TAC[apx_rev; IN_SPHERE_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`apx_rev(e:real^3->A)`; `K:A->bool`; `inv(norm(w:real^3) pow 2) % w`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC APX_REV_NECK THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Point-set tools for images of parametrizations (open,                     *)
(* compact and closed pieces, set operations through an injective map),     *)
(* and the characterization of a component of the complement of S as a      *)
(* connected open set W whose closure adds only points of S.                *)
(* ------------------------------------------------------------------------- *)

let KNCL_ANNULUS_CONNECTED = prove
 (`!r1 r2. connected(annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]);;

let KNCL_PARAM_COMPACT_IMAGE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) t.
     hausdorff_space top /\ mfd_param top atlas s e /\ compact t /\ t SUBSET s
     ==> compact_in top (IMAGE e t) /\ closed_in top (IMAGE e t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `compact_in top (IMAGE (e:real^3->A) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN]]);;

let KNCL_PARAM_SETOPS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) a b.
     mfd_param top atlas s e /\ a SUBSET s /\ b SUBSET s
     ==> IMAGE e a INTER IMAGE e b = IMAGE e (a INTER b) /\
         IMAGE e a DIFF IMAGE e b = IMAGE e (a DIFF b) /\
         (IMAGE e a SUBSET IMAGE e b <=> a SUBSET b) /\
         (IMAGE e a = IMAGE e b <=> a = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s /\ (e:real^3->A) x = e y ==> x = y` MP_TAC THENL
   [ASM_MESON_TAC[MFD_PARAM_INJ]; ALL_TAC] THEN
  UNDISCH_TAC `(a:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(b:real^3->bool) SUBSET s` THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_DIFF; IN_IMAGE] THEN MESON_TAC[]);;

let KNCL_COMPONENT_EQ = prove
 (`!top S (p:A) W.
     connected_in top W /\ open_in top W /\ W SUBSET topspace top DIFF S /\
     top closure_of W SUBSET W UNION S /\ p IN W
     ==> connected_component_of (subtopology top (topspace top DIFF S)) p = W`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`;
                   `connected_component_of (subtopology top (topspace top DIFF S)) (p:A)`;
                   `W:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
    REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EXISTS_TAC `top closure_of W:A->bool` THEN
        REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
        MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] CLOSURE_OF_SUBSET) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
        REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `W:A->bool` THEN ASM SET_TAC[]];
      MATCH_MP_TAC(SET_RULE
       `(p:A) IN c /\ p IN t ==> (c SUBSET t \/ DISJOINT c t ==> c SUBSET t)`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]];
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]]);;

let KNCL_SLAB_CONNECTED = prove
 (`!a b. connected(apx_slab a b)`,
  REWRITE_TAC[apx_slab; KNCL_ANNULUS_CONNECTED]);;

let KNCL_PARAM_DISJ = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) a b.
     mfd_param top atlas s e /\ a SUBSET s /\ b SUBSET s /\ DISJOINT a b
     ==> DISJOINT (IMAGE e a) (IMAGE e b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `a:real^3->bool`; `b:real^3->bool`] KNCL_PARAM_SETOPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[DISJOINT; CONJUNCT1 th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT]) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]);;

(* Membership in slabs, level spheres and closed slabs in terms of sval.     *)

let KNCL_SVAL_TAC =
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_DIFF; NOT_IN_EMPTY;
              APX_SLAB_SVAL; APX_SPHERE_LEVEL; IN_ELIM_THM; APX_CSLAB] THEN
  TRY(X_GEN_TAC `v:real^3` THEN ASM_CASES_TAC `v:real^3 = vec 0`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;;

let KNCL_CORE_YIN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a0 (e:real^3->A) p K w Sig Yin.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     &8 <= a0 /\ mfd_param top atlas (apx_slab (--a0) a0) e /\
     Sig = IMAGE e (sphere(vec 0,exp(--(&6) / sqrt(&2)))) /\
     Yin = connected_component_of (subtopology top (topspace top DIFF Sig)) p /\
     connected_in top K /\ p IN K /\ K INTER Sig = {} /\
     w IN apx_slab (--a0) a0 /\ e w IN K /\ apx_sval w < --(&6)
     ==> closed_in top Sig /\ Sig SUBSET topspace top /\
         p IN Yin /\ open_in top Yin /\ connected_in top Yin /\
         Yin SUBSET topspace top DIFF Sig /\ top closure_of Yin SUBSET Yin UNION Sig /\
         e w IN Yin /\
         IMAGE e (apx_slab (--a0) (--(&6))) SUBSET Yin /\
         DISJOINT Yin (IMAGE e (apx_slab (--(&6)) a0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && not(is_var(rhs c)) then SYM th else th) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &1 <= sqrt(&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[KNCL_SQRT2_POS] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--a0) a0) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,exp(--(&6) / sqrt(&2))) SUBSET apx_slab (--a0) a0 /\
                apx_slab (--a0) (--(&6)) SUBSET apx_slab (--a0) a0 /\
                apx_slab (--(&6)) a0 SUBSET apx_slab (--a0) a0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN KNCL_SVAL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (Sig:A->bool) /\ Sig SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Sig" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `apx_slab (--a0) a0`; `e:real^3->A`;
                     `sphere(vec 0:real^3,exp(--(&6) / sqrt(&2)))`] KNCL_PARAM_COMPACT_IMAGE) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE] THEN SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--a0) a0)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace top DIFF Sig /\ K SUBSET topspace top DIFF Sig`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Yin:A->bool) /\ connected_in top Yin /\
                Yin SUBSET topspace top DIFF Sig /\ p IN Yin /\
                top closure_of Yin SUBSET Yin UNION Sig /\ K SUBSET Yin`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Yin" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Sig:A->bool`;
                     `p:A`] P2AS_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology top (topspace top DIFF Sig):A topology`; `p:A`]
                    CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
      SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
      REWRITE_TAC[P2AS_COMPONENT_SUBSET];
      REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
       [SET_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Sig:A->bool`;
                       `p:A`] P2AS_COMPONENT_UNION_CLOSED) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) w IN Yin` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN apx_slab (--a0) (--(&6))` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN apx_slab (--a0) a0` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!lo hi. --a0 <= lo /\ hi <= a0 /\ (lo < --(&6) /\ hi <= --(&6) \/ --(&6) <= lo)
                        ==> IMAGE (e:real^3->A) (apx_slab lo hi) SUBSET topspace top DIFF Sig /\
                            connected_in top (IMAGE e (apx_slab lo hi))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    (SUBGOAL_THEN `apx_slab lo hi SUBSET apx_slab (--a0) a0 /\
                   DISJOINT (apx_slab lo hi) (sphere(vec 0:real^3,exp(--(&6) / sqrt(&2))))`
     STRIP_ASSUME_TAC THENL [CONJ_TAC THEN KNCL_SVAL_TAC; ALL_TAC]) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET u /\ DISJOINT s t ==> s SUBSET u DIFF t`) THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC SUBSET_TRANS THEN
         EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--a0) a0)` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
         EXPAND_TAC "Sig" THEN MATCH_MP_TAC KNCL_PARAM_DISJ THEN
         MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                               `apx_slab (--a0) a0`] THEN
         ASM_REWRITE_TAC[]];
       MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
       MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `apx_slab (--a0) a0`] THEN
       ASM_REWRITE_TAC[KNCL_SLAB_CONNECTED]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--a0) (--(&6))) SUBSET Yin` ASSUME_TAC THENL
   [EXPAND_TAC "Yin" THEN MATCH_MP_TAC APX_CC_ABSORB THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--a0`; `--(&6)`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `lo:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e:real^3->A) w` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the other side of the level sphere *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `inv a0`; `--(&6)`] APX_LEVEL_SPHERE_SEP) THEN
  ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; REAL_INV_INV] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `q:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--(&6)`; `a0:real`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `lo:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--(&6)) a0) SUBSET Yin` ASSUME_TAC THENL
   [EXPAND_TAC "Yin" THEN MATCH_MP_TAC APX_CC_ABSORB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`--(&6)`; `&3 / &4`] APX_SVAL_SCALED_BASIS) THEN
  MP_TAC(SPECL [`--(&6)`; `&4 / &3`] APX_SVAL_SCALED_BASIS) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &3 / &4 /\ &0 < &4 / &3`] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC APX_LOG_43 THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&3 / &4 % basis 1)) IN Yin /\
    (e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&4 / &3 % basis 1)) IN Yin`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> concl th =
        `IMAGE (e:real^3->A) (apx_slab (--a0) (--(&6))) SUBSET Yin`));
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> concl th =
        `IMAGE (e:real^3->A) (apx_slab (--(&6)) a0) SUBSET Yin`))] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~connected_component_of (subtopology top (topspace top DIFF Sig))
                ((e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&3 / &4 % basis 1)))
                ((e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&4 / &3 % basis 1)))` THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `(e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&3 / &4 % basis 1)) IN Yin` THEN
  UNDISCH_TAC `(e:real^3->A)(exp(--(&6) / sqrt(&2)) % (&4 / &3 % basis 1)) IN Yin` THEN
  EXPAND_TAC "Yin" THEN REWRITE_TAC[IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_OF_SYM; CONNECTED_COMPONENT_OF_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* The core topology.  e is the neck at z3 with domain slab                  *)
(* (-a0,a0) (a0 = 1/eps0), p is joined below level -6 by K; the ball chart *)
(* b of (c) part 2 for e1 = e o (exp(a/sqrt 2) .) (a = 1/eps) has the      *)
(* sphere S = e(level a).  Then Y = b(ball 1) is the p-component of M - S, *)
(* Y = Yin + e(slab(-a0,a)) with Yin the p-side of the level -6 sphere,    *)
(* and U = b(ball 2) + e2(neck_dom eps) = Yin + e(slab(-a0,3a)) satisfies   *)
(* the structural clauses of rfs_cap.                                       *)
(* ------------------------------------------------------------------------- *)

let KNCL_NORM_SET_TAC =
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_DIFF; NOT_IN_EMPTY;
              IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC;;

let KNCL_SE_TAC =
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
    `IMAGE (e:real^3->A) (sphere(vec 0,exp(a / sqrt(&2)))) = S`));;

let KNCL_SB_TAC =
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
    `IMAGE (b:real^3->A) (sphere(vec 0,&1)) = S`));;

let KNCL_YB_TAC =
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
    `IMAGE (b:real^3->A) (ball(vec 0,&1)) = Y`));;

let KNCL_CORE_TOP = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a a0 (e:real^3->A) p K w b f f'
    e1 (e2:real^3->A) Sig S Yin Y U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     &8 <= a /\ &4 * a <= a0 /\
     mfd_param top atlas (apx_slab (--a0) a0) e /\
     e1 = e o (\y. exp(a / sqrt(&2)) % y) /\
     Sig = IMAGE e (sphere(vec 0,exp(--(&6) / sqrt(&2)))) /\
     S = IMAGE e (sphere(vec 0,exp(a / sqrt(&2)))) /\
     Yin = connected_component_of (subtopology top (topspace top DIFF Sig)) p /\
     Y = IMAGE b (ball(vec 0,&1)) /\
     U = IMAGE b (ball(vec 0,&2)) UNION IMAGE e2 (rfs_neck_dom (inv a)) /\
     IMAGE e2 (rfs_neck_dom (inv a)) = IMAGE e (apx_slab a (&3 * a)) /\
     IMAGE e1 (rfs_neck_dom (inv a)) = IMAGE e (apx_slab (&0) (&2 * a)) /\
     connected_in top K /\ p IN K /\ K INTER Sig = {} /\
     w IN apx_slab (--a0) a0 /\ e w IN K /\ apx_sval w < --(&6) /\
     mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\
     p IN Y /\ IMAGE b (sphere(vec 0,&1)) = S /\
     (!y. y IN annulus (&1) (&2) ==> b y = e1 (radial_ext f y))
     ==> open_in top U /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
         IMAGE e2 (rfs_neck_dom (inv a)) = U DIFF IMAGE b (cball(vec 0,&1)) /\
         IMAGE e1 (rfs_neck_dom (inv a)) SUBSET U /\
         p IN Yin /\ open_in top Yin /\ Yin SUBSET topspace top /\
         Y = Yin UNION IMAGE e (apx_slab (--a0) a) /\
         U = Yin UNION IMAGE e (apx_slab (--a0) (&3 * a)) /\
         Y = connected_component_of (subtopology top (topspace top DIFF S)) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && not(is_var(rhs c)) then SYM th else th) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a0:real`;
                 `e:real^3->A`; `p:A`; `K:A->bool`; `w:real^3`; `Sig:A->bool`; `Yin:A->bool`]
                KNCL_CORE_YIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param top atlas (apx_slab (--a0) a0) (e:real^3->A)`)) THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2)) (b:real^3->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_ball_chart]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> concl th = `mfd_param top atlas (ball(vec 0,&2)) (b:real^3->A)`)) THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &1 <= sqrt(&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[KNCL_SQRT2_POS] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--a0) a0) SUBSET topspace top /\
                IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  (* slabs inside the domain *)
  SUBGOAL_THEN
   `apx_slab (--a0) a SUBSET apx_slab (--a0) a0 /\
    apx_slab a (&3 * a) SUBSET apx_slab (--a0) a0 /\
    apx_slab (--a0) (&3 * a) SUBSET apx_slab (--a0) a0 /\
    apx_slab (&0) (&2 * a) SUBSET apx_slab (--a0) a0 /\
    sphere(vec 0:real^3,exp(a / sqrt(&2))) SUBSET apx_slab (--a0) a0 /\
    sphere(vec 0:real^3,exp(--(&6) / sqrt(&2))) SUBSET apx_slab (--a0) a /\
    sphere(vec 0:real^3,exp(a / sqrt(&2))) SUBSET apx_slab (--(&6)) a0 /\
    apx_slab a (&3 * a) SUBSET apx_slab (--(&6)) a0 /\
    cball(vec 0:real^3,exp(a / sqrt(&2))) DIFF ball(vec 0,exp(--(&6) / sqrt(&2)))
      SUBSET apx_slab (--a0) a0 /\
    apx_slab (--a0) a SUBSET
      apx_slab (--a0) (--(&6)) UNION
      (cball(vec 0,exp(a / sqrt(&2))) DIFF ball(vec 0,exp(--(&6) / sqrt(&2)))) /\
    cball(vec 0:real^3,exp(a / sqrt(&2))) DIFF ball(vec 0,exp(--(&6) / sqrt(&2)))
      SUBSET apx_slab (--a0) a UNION sphere(vec 0,exp(a / sqrt(&2))) /\
    DISJOINT (apx_slab (--a0) a) (sphere(vec 0:real^3,exp(a / sqrt(&2)))) /\
    DISJOINT (apx_slab a (&3 * a)) (sphere(vec 0:real^3,exp(a / sqrt(&2)))) /\
    DISJOINT (apx_slab a (&3 * a)) (apx_slab (--a0) a) /\
    apx_slab (--a0) a UNION sphere(vec 0,exp(a / sqrt(&2))) UNION apx_slab a (&3 * a) =
      apx_slab (--a0) (&3 * a) /\
    apx_slab (&0) (&2 * a) SUBSET apx_slab (--a0) (&3 * a) /\
    (w:real^3) IN apx_slab (--a0) a`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN apx_slab (--a0) a0` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN KNCL_SVAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!lo hi. --a0 <= lo /\ hi <= a0
                        ==> open_in top (IMAGE (e:real^3->A) (apx_slab lo hi)) /\
                            connected_in top (IMAGE e (apx_slab lo hi))`
  (LABEL_TAC "slabs") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `apx_slab lo hi SUBSET apx_slab (--a0) a0` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `apx_slab (--a0) a0`] THEN
      ASM_REWRITE_TAC[apx_slab; OPEN_ANNULUS];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `apx_slab (--a0) a0`] THEN
      ASM_REWRITE_TAC[KNCL_SLAB_CONNECTED]];
    ALL_TAC] THEN
  (* disjointness facts through e *)
  SUBGOAL_THEN
   `DISJOINT (IMAGE (e:real^3->A) (apx_slab (--a0) a)) S /\
    DISJOINT (IMAGE (e:real^3->A) (apx_slab a (&3 * a))) S /\
    DISJOINT (IMAGE (e:real^3->A) (apx_slab a (&3 * a))) (IMAGE e (apx_slab (--a0) a)) /\
    DISJOINT Yin S /\ DISJOINT Yin (IMAGE (e:real^3->A) (apx_slab a (&3 * a))) /\
    Sig SUBSET IMAGE (e:real^3->A) (apx_slab (--a0) a)`
  STRIP_ASSUME_TAC THENL
   [KNCL_SE_TAC THEN EXPAND_TAC "Sig" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC KNCL_PARAM_DISJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--a0) a0`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC KNCL_PARAM_DISJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--a0) a0`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC KNCL_PARAM_DISJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--a0) a0`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!y t s. DISJOINT (y:A->bool) t /\ s SUBSET t ==> DISJOINT y s`) THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--(&6)) a0)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      MATCH_MP_TAC(SET_RULE `!y t s. DISJOINT (y:A->bool) t /\ s SUBSET t ==> DISJOINT y s`) THEN
      EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--(&6)) a0)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      ASM_SIMP_TAC[IMAGE_SUBSET]];
    ALL_TAC] THEN
  (* the p-component of M - S is Yin + e(slab(-a0,a)) *)
  SUBGOAL_THEN
   `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) =
    Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC KNCL_COMPONENT_EQ THEN
    USE_THEN "slabs" (MP_TAC o SPECL [`--a0`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A) w` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--a0) a) SUBSET topspace top` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--a0) a0)` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET];
        ASM SET_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `top closure_of (Yin UNION
                    IMAGE (e:real^3->A) (cball(vec 0,exp(a / sqrt(&2))) DIFF
                                         ball(vec 0,exp(--(&6) / sqrt(&2)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MONO THEN
        MATCH_MP_TAC(SET_RULE `!y s t u. (s:A->bool) SUBSET u UNION t /\ u SUBSET y
                                         ==> y UNION s SUBSET y UNION t`) THEN
        EXISTS_TAC `IMAGE (e:real^3->A) (apx_slab (--a0) (--(&6)))` THEN
        ASM_REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_OF_UNION] THEN
      SUBGOAL_THEN
       `top closure_of IMAGE (e:real^3->A) (cball(vec 0,exp(a / sqrt(&2))) DIFF
                                            ball(vec 0,exp(--(&6) / sqrt(&2)))) =
        IMAGE e (cball(vec 0,exp(a / sqrt(&2))) DIFF ball(vec 0,exp(--(&6) / sqrt(&2))))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_CLOSED_IN THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `apx_slab (--a0) a0`; `e:real^3->A`;
                       `cball(vec 0:real^3,exp(a / sqrt(&2))) DIFF
                        ball(vec 0,exp(--(&6) / sqrt(&2)))`] KNCL_PARAM_COMPACT_IMAGE) THEN
        ASM_REWRITE_TAC[APX_CSLAB] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `IMAGE (e:real^3->A) (cball(vec 0,exp(a / sqrt(&2))) DIFF ball(vec 0,exp(--(&6) / sqrt(&2))))
        SUBSET IMAGE e (apx_slab (--a0) a) UNION S`
      MP_TAC THENL
       [KNCL_SE_TAC THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[IN_UNION]];
    ALL_TAC] THEN
  (* Y is the p-component of M - S *)
  SUBGOAL_THEN `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) = Y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC KNCL_COMPONENT_EQ THEN KNCL_YB_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `(y:A->bool) SUBSET u /\ DISJOINT y s ==> y SUBSET u DIFF s`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        KNCL_SB_TAC THEN MATCH_MP_TAC KNCL_PARAM_DISJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `ball(vec 0:real^3,&2)`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN KNCL_NORM_SET_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
        SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `ball(vec 0:real^3,&2)`; `b:real^3->A`; `cball(vec 0:real^3,&1)`]
                      KNCL_PARAM_COMPACT_IMAGE) THEN
        ASM_REWRITE_TAC[COMPACT_CBALL] THEN ANTS_TAC THENL [KNCL_NORM_SET_TAC; SIMP_TAC[]];
        KNCL_SB_TAC THEN
        SUBGOAL_THEN `cball(vec 0:real^3,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
        SUBST1_TAC THENL [KNCL_NORM_SET_TAC; REWRITE_TAC[IMAGE_UNION; SUBSET_REFL]]];
      KNCL_YB_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the collar of b lies in e(slab(a,3a)) *)
  SUBGOAL_THEN `IMAGE (b:real^3->A) (annulus (&1) (&2)) SUBSET IMAGE e (apx_slab a (&3 * a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^3) IN annulus (&1) (&2)`)]) THEN
    EXPAND_TAC "e1" THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SUBGOAL_THEN `norm(radial_ext (f:real^3->real^3) y) = norm y` ASSUME_TAC THENL
     [REWRITE_TAC[radial_ext; NORM_MUL; REAL_ABS_NORM] THEN
      SUBGOAL_THEN `(f:real^3->real^3)(inv(norm(y:real^3)) % y) IN sphere(vec 0,&1)` MP_TAC THENL
       [UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
        DISCH_THEN(MP_TAC o SPEC `inv(norm(y:real^3)) % y` o CONJUNCT2 o CONJUNCT2) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
          MATCH_MP_TAC REAL_MUL_LINV THEN
          UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          SIMP_TAC[]];
        SIMP_TAC[IN_SPHERE_0; REAL_MUL_RID]];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
    REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_ABS_EXP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 * exp(a / sqrt(&2)) <= exp((&3 * a) / sqrt(&2))` MP_TAC THENL
     [SUBGOAL_THEN `exp((&3 * a) / sqrt(&2)) = exp(a / sqrt(&2)) * exp((&2 * a) / sqrt(&2))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MP_TAC(SPEC `(&2 * a) / sqrt(&2)` REAL_EXP_LE_X) THEN
      SUBGOAL_THEN `&1 <= (&2 * a) / sqrt(&2)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(a / sqrt(&2)) * &2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* U in terms of e *)
  SUBGOAL_THEN `U = (Y:A->bool) UNION S UNION IMAGE e (apx_slab a (&3 * a))` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN KNCL_YB_TAC THEN KNCL_SB_TAC THEN
    SUBGOAL_THEN `ball(vec 0:real^3,&2) =
                  ball(vec 0,&1) UNION sphere(vec 0,&1) UNION annulus (&1) (&2)`
    SUBST1_TAC THENL [KNCL_NORM_SET_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `IMAGE (e2:real^3->A) (rfs_neck_dom (inv a)) = IMAGE e (apx_slab a (&3 * a))`) th]) THEN
    UNDISCH_TAC `IMAGE (b:real^3->A) (annulus (&1) (&2)) SUBSET IMAGE e (apx_slab a (&3 * a))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `U = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) (&3 * a))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `U:A->bool`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `Y:A->bool`)) THEN
    KNCL_SE_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `apx_slab (--a0) a UNION sphere(vec 0,exp(a / sqrt(&2))) UNION apx_slab a (&3 * a) =
       apx_slab (--a0) (&3 * a)`)) THEN
    REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) = Y UNION S` ASSUME_TAC THENL
   [KNCL_YB_TAC THEN KNCL_SB_TAC THEN
    SUBGOAL_THEN `cball(vec 0:real^3,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
    SUBST1_TAC THENL [KNCL_NORM_SET_TAC; REWRITE_TAC[IMAGE_UNION]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
      `U = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) (&3 * a))`)) THEN
    MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "slabs" (MP_TAC o SPECL [`--a0`; `&3 * a`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    EXPAND_TAC "U" THEN SET_TAC[];
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `IMAGE (e2:real^3->A) (rfs_neck_dom (inv a)) = IMAGE e (apx_slab a (&3 * a))`) th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `IMAGE (b:real^3->A) (cball(vec 0,&1)) = Y UNION S`) th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `U = (Y:A->bool) UNION S UNION IMAGE e (apx_slab a (&3 * a))`) th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `Y = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) a)`) th]) THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (e:real^3->A) (apx_slab a (&3 * a))) S`;
      `DISJOINT (IMAGE (e:real^3->A) (apx_slab a (&3 * a))) (IMAGE e (apx_slab (--a0) a))`;
      `DISJOINT (Yin:A->bool) (IMAGE (e:real^3->A) (apx_slab a (&3 * a)))`] THEN
    SET_TAC[];
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
      `U = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) (&3 * a))`)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `IMAGE (e1:real^3->A) (rfs_neck_dom (inv a)) = IMAGE e (apx_slab (&0) (&2 * a))`) th]) THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s SUBSET (y:A->bool) UNION t`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(Yin:A->bool) SUBSET topspace top DIFF Sig` THEN SET_TAC[];
    FIRST_ASSUM(ACCEPT_TAC o check (fun th -> concl th =
      `Y = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) a)`));
    FIRST_ASSUM(ACCEPT_TAC o check (fun th -> concl th =
      `U = Yin UNION IMAGE (e:real^3->A) (apx_slab (--a0) (&3 * a))`));
    FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> concl th =
      `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) = Y`))]);;

(* ------------------------------------------------------------------------- *)
(* Distance estimates for the soul cap.  With p joined to the                *)
(* level -46..-35 point e(w0) of the neck e at z by a minimal geodesic tail: *)
(* the level -6 sphere and e(w0) are closer to p than z (KNCL_SIG_IN_BALL); *)
(* the levels >= 5 are farther from p than z (KNCL_S_FAR); the level a      *)
(* sphere is at distance >= 2a h from the complement of e(slab(-1/eps,3a))  *)
(* (KNCL_U_EXIT).  h = R(z)^(-1/2).                                         *)
(* ------------------------------------------------------------------------- *)

let KNCL_SQRT_BOUNDS = prove
 (`!x. &0 <= x /\ x <= &1 ==> sqrt(&1 + x) <= &1 + x / &2 /\ &1 - x <= sqrt(&1 - x)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN MP_TAC(SPEC `x:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= (&1 - x) * x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let KNCL_CENTRE_DIST = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) v.
     hausdorff_space top /\ riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps z e /\
     eps < &1 /\ v IN rfs_neck_dom eps
     ==> mfd_joinable (top,atlas) z (e v) /\
         mfd_dist (top,atlas) g z (e v) <=
           sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g z)) * (abs(apx_sval v) + sqrt(&2) * pi) /\
         sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) *
           min (abs(apx_sval v)) (&2 * inv eps - abs(apx_sval v))
         <= mfd_dist (top,atlas) g z (e v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(e:real^3->A) y0`; `e:real^3->A`; `y0:real^3`; `v:real^3`]
                APX_NECK_DIST_UPPER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(e:real^3->A) y0`; `e:real^3->A`; `y0:real^3`; `v:real^3`]
                APX_NECK_DIST_LOWER) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
  SIMP_TAC[]);;

let KNCL_SIG_IN_BALL = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) p w0.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     &0 < eps /\ eps <= &1 / &400 /\ rfs_neck (top,atlas) g eps z e /\ p IN topspace top /\
     w0 IN rfs_neck_dom eps /\ --(&46) <= apx_sval w0 /\ apx_sval w0 <= --(&35) /\
     mfd_dist (top,atlas) g z (e w0) = &45 * inv(sqrt(mfd_scalar atlas g z)) /\
     mfd_dist (top,atlas) g z (e w0) + mfd_dist (top,atlas) g (e w0) p =
     mfd_dist (top,atlas) g z p
     ==> mfd_dist (top,atlas) g p (e w0) < mfd_dist (top,atlas) g z p /\
         !u. u IN IMAGE e (sphere(vec 0,exp(--(&6) / sqrt(&2))))
             ==> mfd_dist (top,atlas) g p u < mfd_dist (top,atlas) g z p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) p (e(w0:real^3)) =
                mfd_dist (top,atlas) g z p - &45 * h`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `p:A`; `(e:real^3->A) w0`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `&400 <= inv eps` MP_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &400`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) w0 IN topspace top /\ (e:real^3->A) v IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `eps:real`; `z:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `(e:real^3->A) w0`; `(e:real^3->A) v`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `w0:real^3`; `v:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h * (abs(apx_sval w0 - --(&6)) + sqrt(&2) * pi) <=
                &801 / &800 * h * (&224 / &5)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + eps / &2` THEN CONJ_TAC THENL
       [MP_TAC(SPEC `eps:real` KNCL_SQRT_BOUNDS) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= x + y`) THEN
      SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; SQRT_POS_LE; REAL_POS; PI_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let KNCL_S_FAR = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) p K w0 v.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ apx_sphere_sep top atlas /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps z e /\ p IN topspace top /\
     connected_in top K /\ p IN K /\ K INTER IMAGE e (sphere(vec 0,&1)) = {} /\
     w0 IN rfs_neck_dom eps /\ e w0 IN K /\ apx_sval w0 < &0 /\
     v IN rfs_neck_dom eps /\ &5 <= apx_sval v
     ==> mfd_dist (top,atlas) g z p < mfd_dist (top,atlas) g p (e v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) v IN topspace top /\ (z:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `eps:real`; `z:A`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `eps:real`; `z:A`] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* p and e v are separated by the central sphere *)
  SUBGOAL_THEN `apx_separates top (IMAGE (e:real^3->A) (sphere(vec 0,&1))) p (e v)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`] P2FL_NECK_SEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`; `(e:real^3->A)(&3 / &4 % basis 1)`;
                   `(e:real^3->A)(&4 / &3 % basis 1)`; `w0:real^3`; `v:real^3`;
                   `K:A->bool`; `{(e:real^3->A) v}`; `p:A`; `(e:real^3->A) v`]
                  P2FL_NECK_OPP_SEP) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SING; IN_SING] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SET_RULE `{x:A} INTER s = {} <=> ~(x IN s)`; IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `z:A`; `e:real^3->A`; `v:real^3`; `y:real^3`] KNCL_NECK_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
        ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `&5 <= apx_sval(y:real^3)` THEN
        ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* a minimal path from p to e v crosses the central sphere at q *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `IMAGE (e:real^3->A) (sphere(vec 0,&1))`; `p:A`; `p:A`; `(e:real^3->A) v`]
                P2AS_CROSS_DIST) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `apx_separates top (IMAGE (e:real^3->A) (sphere(vec 0,&1))) p (e v)` THEN
    REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(q:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ apx_sval y1 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  (* bounds *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `y1:real^3`] KNCL_CENTRE_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `y1:real^3`; `v:real^3`]
                APX_NECK_DIST_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `z:A`; `(e:real^3->A) y1`; `p:A`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `p:A`; `(e:real^3->A) y1`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `(e:real^3->A) y1`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  (* arithmetic: sqrt(1 - eps) 5 > sqrt(1 + eps) sqrt 2 pi *)
  SUBGOAL_THEN `abs(apx_sval(v:real^3)) = apx_sval v /\
                min (apx_sval v) (&2 * inv eps - apx_sval v) = apx_sval v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(v:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `abs(apx_sval(v:real^3)) = apx_sval v`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `min (apx_sval(v:real^3)) (&2 * inv eps - apx_sval v) = apx_sval v`]) THEN
  MP_TAC(SPEC `eps:real` KNCL_SQRT_BOUNDS) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h * sqrt(&2) * pi <= &201 / &200 * h * (&24 / &5) /\
                &99 / &100 * h * &5 <= sqrt(&1 - eps) * h * apx_sval(v:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        TRY(ASM_REAL_ARITH_TAC) THEN
        SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS; PI_POS_LE]) THEN
    TRY(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MP_TAC APX_SQRT2_PI THEN ASM_REAL_ARITH_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let KNCL_U_EXIT = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) a v q.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ &0 < eps /\ eps < &1 /\ rfs_neck (top,atlas) g eps z e /\
     &0 < a /\ &4 * a <= inv eps /\
     v IN rfs_neck_dom eps /\ apx_sval v = a /\ q IN topspace top /\
     ~(q IN IMAGE e (apx_slab (--inv eps) (&3 * a)))
     ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * (&2 * a)
         <= mfd_dist (top,atlas) g (e v) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 - eps) * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(q:A) IN IMAGE e (rfs_neck_dom eps)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `&3 * a <= apx_sval(v':real^3) /\ apx_sval v' < inv eps` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((e:real^3->A) v' IN IMAGE e (apx_slab (--inv eps) (&3 * a)))` THEN
      UNDISCH_TAC `(v':real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REPEAT STRIP_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(REAL_ARITH `~(x < y) ==> y <= x`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((e:real^3->A) v' IN IMAGE e (apx_slab (--inv eps) (&3 * a)))` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`; `v:real^3`; `v':real^3`]
                  APX_NECK_DIST_LOWER) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= d ==> x <= d`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `s * h * x = (s * h) * x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z:A`; `e:real^3->A`; `v:real^3`; `q:A`] KNCL_EXIT_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `eps:real`; `z:A`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= d ==> x <= d`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH `s * h * x = (s * h) * x`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The soul cap.  At a point p with all other points regular                 *)
(* for d_p (a soul), with necks of scale eps/K1 at distance >= Dst rho from  *)
(* p (rho = R(p)^(-1/2)) and the two parts of (c): a cap U, Y in the sense  *)
(* of rfs_cap (structure only) with the closed Dst rho ball inside Y, U     *)
(* inside the ball and one neck e3 at a point z3 at distance Dst rho, and   *)
(* the width of U beyond the sphere S of the inner neck (for clause 7).     *)
(* ------------------------------------------------------------------------- *)

(* Helper used by tactics below: does term tm occur in the conclusion of th? *)
let kncl_has tm th = can (find_term (fun u -> aconv u tm)) (concl th);;

let KNCL_SEGMENT_SET = prove
 (`!top atlas (g:A->real^3^3) p y.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p IN topspace top /\ y IN topspace top
     ==> ?G. connected_in top G /\ p IN G /\ y IN G /\
             !x. x IN G ==> x IN topspace top /\ mfd_joinable (top,atlas) p x /\
                            mfd_dist (top,atlas) g p x <= mfd_dist (top,atlas) g p y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:A = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `{p:A}` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SING; IN_SING] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `y:A`] P2AS_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `u:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (mfd_geo (top,atlas) (g:A->real^3^3) p u)
                    (real_interval[&0,mfd_dist (top,atlas) g p y])` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal
                  (real_interval[&0,mfd_dist (top,atlas) (g:A->real^3^3) p y])` THEN
    ASM_SIMP_TAC[P2AS_GEO_CONT; CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL;
                 SUBSET_REFL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) p y` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `mfd_dist (top,atlas) (g:A->real^3^3) p y`))
        (concl th) && not(can (find_term ((=) `mfd_exp (top,atlas) (g:A->real^3^3)`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

(* No interior maximum: the p-component of the complement of a compact set  *)
(* Sig that is closer to p than r lies in the open r-ball (P2AS_CASE_B).     *)

let KNCL_YIN_IN_BALL = prove
 (`!top atlas (g:A->real^3^3) p Sig Yin K r.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     compact_in top Sig /\
     Yin = connected_component_of (subtopology top (topspace top DIFF Sig)) p /\
     compact_in top K /\ Yin SUBSET K /\ &0 < r /\
     (!u. u IN Sig ==> mfd_dist (top,atlas) g p u < r)
     ==> Yin SUBSET mfd_ball (top,atlas) g p r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `K:A->bool`] KNCL_DIST_BOUNDED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `R0:real`)] THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN Yin` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN DISCH_THEN(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `Sig:A->bool`; `p:A`; `z:A`; `&0`; `R0:real`] P2AS_CASE_B) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`] MFD_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(z:A) IN Yin` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN];
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(u:A) IN Sig`)) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(Yin:A->bool) SUBSET K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN]]);;

(* A ball about p whose radius is below the distance to S lies in the        *)
(* p-component of the complement of S.                                       *)

let KNCL_BALL_IN_COMP = prove
 (`!top atlas (g:A->real^3^3) p S r.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!s. s IN S ==> r < mfd_dist (top,atlas) g p s)
     ==> mfd_ball (top,atlas) g p r SUBSET
         connected_component_of (subtopology top (topspace top DIFF S)) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `y:A`] KNCL_SEGMENT_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `G:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(G:A->bool) SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN G`) o
      check (fun th -> is_forall(concl th) && kncl_has `G:A->bool` th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN S`)) THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(y:A) IN G` THEN SET_TAC[]]);;

(* The width of the cap beyond S (for clause 7): a point y of the p-side of *)
(* S and a point q outside U are joined through a point s of S, and s is at *)
(* distance >= 2a sqrt(1 - eps) R(z)^(-1/2) from q (KNCL_U_EXIT).          *)

let KNCL_WIDTH = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) a p S U y q.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     &0 < eps /\ eps < &1 /\ rfs_neck (top,atlas) g eps z e /\
     &0 < a /\ &4 * a <= inv eps /\
     S = IMAGE e (sphere(vec 0,exp(a / sqrt(&2)))) /\
     IMAGE e (apx_slab (--inv eps) (&3 * a)) SUBSET U /\
     connected_component_of (subtopology top (topspace top DIFF S)) p SUBSET U /\
     connected_component_of (subtopology top (topspace top DIFF S)) p y /\
     q IN topspace top /\ ~(q IN U)
     ==> ?s. s IN IMAGE e (rfs_neck_dom eps) /\ mfd_joinable (top,atlas) y s /\
             mfd_dist (top,atlas) g y s +
             sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * (&2 * a)
             <= mfd_dist (top,atlas) g y q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE o check (fun th ->
      kncl_has `y:A` th && kncl_has `connected_component_of:A topology->A->A->bool` th)) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S:A->bool`; `p:A`; `y:A`; `q:A`] P2AS_CROSS_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) SUBSET U` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[IN];
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `s:A` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(s:A) IN S` THEN ASM_REWRITE_TAC[IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `a:real`; `v:real^3`; `q:A`] KNCL_U_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((q:A) IN U)` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (--inv eps) (&3 * a)) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(s:A) = e(v:real^3)`)) THEN
  ASM_REAL_ARITH_TAC);;


let KNCL_C_EQ = prove
 (`!eps. &0 < eps
         ==> inv(sqrt(&2) * eps) = inv eps / sqrt(&2) /\
             &2 * inv(sqrt(&2) * eps) = (&2 * inv eps) / sqrt(&2) /\
             &3 * inv(sqrt(&2) * eps) = (&3 * inv eps) / sqrt(&2)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC KNCL_SQRT2_POS THEN
  UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD);;

let KNCL_MUL3_LE = prove
 (`!s s' h x x'. &0 <= s /\ s <= s' /\ &0 <= h /\ &0 <= x /\ x <= x'
                 ==> s * h * x <= s' * h * x'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;


let KNCL_SOUL_CAP = prove
 (`!top atlas (g:A->real^3^3) eps K1 p Dst.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ apx_sphere_sep top atlas /\
     ~compact_space top /\ p IN topspace top /\ &0 < mfd_scalar atlas g p /\
     &0 < eps /\ eps <= &1 / &100 /\ &4 <= K1 /\ &0 < Dst /\
     (!z (e:real^3->A). rfs_neck (top,atlas) g (eps / K1) z e
        ==> rfs_neck (top,atlas) g eps (e(exp(inv(sqrt(&2) * eps)) % basis 1))
                     (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) /\
            rfs_neck (top,atlas) g eps (e(exp(&2 * inv(sqrt(&2) * eps)) % basis 1))
                     (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) /\
            IMAGE (e o (\w. exp(inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
              IMAGE e (annulus (&1) (exp(&2 * inv(sqrt(&2) * eps)))) /\
            IMAGE (e o (\w. exp(&2 * inv(sqrt(&2) * eps)) % w)) (rfs_neck_dom eps) =
              IMAGE e (annulus (exp(inv(sqrt(&2) * eps))) (exp(&3 * inv(sqrt(&2) * eps))))) /\
     (!z (e:real^3->A). rfs_neck (top,atlas) g (eps / K1) z e
            ==> ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * (eps / K1))))) /\
     (!z (e:real^3->A). rfs_neck (top,atlas) g eps z e /\ ~(p IN IMAGE e (rfs_neck_dom eps)) /\
            apx_separates top (IMAGE e (sphere(vec 0,&1))) p (e(&4 / &3 % basis 1))
            ==> ?b f f'. mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\
                         p IN IMAGE b (ball(vec 0,&1)) /\
                         IMAGE b (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1)) /\
                         (!y. y IN annulus (&1) (&2) ==> b y = e(radial_ext f y))) /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     (!x. x IN topspace top /\
          Dst * inv(sqrt(mfd_scalar atlas g p)) <= mfd_dist (top,atlas) g p x
          ==> ?e:real^3->A. rfs_neck (top,atlas) g (eps / K1) x e)
     ==> ?U Y z3 (e3:real^3->A) w0.
           (?b e e' z z' f f'.
              mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
              Y = IMAGE b (ball(vec 0,&1)) /\
              rfs_neck (top,atlas) g eps z e /\
              IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
              rfs_neck (top,atlas) g eps z' e' /\
              IMAGE e' (rfs_neck_dom eps) SUBSET U /\
              IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
              sphere_diffeo f f' /\
              (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) /\
           open_in top U /\ Y SUBSET U /\
           mfd_ball (top,atlas) g p (Dst * inv(sqrt(mfd_scalar atlas g p))) SUBSET Y /\
           rfs_neck (top,atlas) g (eps / K1) z3 e3 /\
           U SUBSET mfd_ball (top,atlas) g p (Dst * inv(sqrt(mfd_scalar atlas g p))) UNION
                    IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) /\
           IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET U /\
           w0 IN apx_slab (--inv(eps / K1)) (&3 * inv eps) /\
           e3 w0 IN mfd_ball (top,atlas) g p (Dst * inv(sqrt(mfd_scalar atlas g p))) /\
           (!y q. y IN Y /\ q IN topspace top /\ ~(q IN U)
                  ==> ?s. s IN IMAGE e3 (rfs_neck_dom (eps / K1)) /\
                          mfd_joinable (top,atlas) y s /\
                          mfd_dist (top,atlas) g y s +
                          sqrt(&1 - eps / K1) * inv(sqrt(mfd_scalar atlas g z3)) *
                          (&2 * inv eps)
                          <= mfd_dist (top,atlas) g y q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `rho = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) p))` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &1 <= sqrt(&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[KNCL_SQRT2_POS] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` KNCL_C_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o SYM) (CONJUNCTS th)) THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  ABBREV_TAC `eps0 = eps / K1` THEN
  SUBGOAL_THEN `&100 <= inv eps /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &100`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps0 /\ eps0 <= &1 / &400 /\ K1 * inv eps = inv eps0 /\
                &0 < c /\ &60 <= c /\ K1 * c = inv(sqrt(&2) * eps0) /\ &0 < inv eps`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps0" THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= K1 ==> &0 < K1`] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`sqrt(&2) * eps`; `&3 / &200`] REAL_LE_INV2) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &1 / &100` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `~(K1 = &0) /\ ~(eps = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC KNCL_SQRT2_POS THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the neck e3 at z3, oriented with p below level -35 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `Dst * rho`] KNCL_FAR_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `z3:A` o check (kncl_has `Dst:real`) o
    check (fun th -> is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_THEN(X_CHOOSE_TAC `e0:real^3->A`)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps0:real`; `z3:A`; `e0:real^3->A`; `p:A`] KNCL_SOUL_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real^3->A` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(p IN IMAGE (e3:real^3->A) (rfs_neck_dom (&3 / &2 * eps0)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h3 = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z3))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
    check (fun th -> concl th = `rfs_neck (top,atlas) (g:A->real^3^3) eps0 z3 e3`)) THEN
  SUBGOAL_THEN `&0 < h3` ASSUME_TAC THENL
   [EXPAND_TAC "h3" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the re-centred necks e1 (inner) and e2 (outer) *)
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP (check (kncl_has `&3 * c`) th)
    (ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps0 z3 e3`))) THEN
  (* separation by the sphere of e1 (KNCL_SHIFT_SEP) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps0:real`; `z3:A`; `e3:real^3->A`; `K:A->bool`; `w0:real^3`; `p:A`; `c:real`;
                 `eps:real`; `(e3:real^3->A)(exp c % basis 1)`] KNCL_SHIFT_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(&4 * c)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `exp(&4 * c) = exp c * exp(&3 * c)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      REWRITE_TAC[REAL_EXP_POS_LT] THEN MP_TAC(SPEC `&3 * c` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * c = inv(sqrt(&2) * eps0)`)) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  (* p is not in the middle of e1 *)
  SUBGOAL_THEN `~(p IN IMAGE ((e3:real^3->A) o (\w. exp c % w)) (rfs_neck_dom eps))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(p IN IMAGE (e3:real^3->A) (rfs_neck_dom (&3 / &2 * eps0)))` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> ~((p:A) IN t) ==> ~(p IN s)`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[rfs_neck_dom] THEN
    SUBGOAL_THEN `inv(sqrt(&2) * (&3 / &2 * eps0)) = &2 / &3 * (K1 * c)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC KNCL_SQRT2_POS THEN UNDISCH_TAC `&0 < eps0` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT; REAL_NEG_LT0] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * c = inv(sqrt(&2) * eps0)`)) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(&2 * c)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * c = inv(sqrt(&2) * eps0)`)) THEN
      MATCH_MP_TAC(REAL_ARITH `&3 * c <= K1 * c ==> &2 * c <= &2 / &3 * (K1 * c)`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the ball chart b of (c) part 2 for e1 *)
  FIRST_ASSUM(MP_TAC o SPECL [`(e3:real^3->A)(exp c % basis 1)`;
                               `(e3:real^3->A) o (\w. exp c % w)`] o check (kncl_has `radial_ext:(real^3->real^3)->real^3->real^3`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->A` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  (* K misses the level -6 sphere of e3 *)
  SUBGOAL_THEN `!v. apx_sval v <= &1 / &2 * inv eps0 /\ --(&1 / &2 * inv eps0) <= apx_sval v /\
                    ~(v = vec 0) ==> (v:real^3) IN rfs_neck_dom eps0`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * inv eps = inv eps0`)) THEN
    SUBGOAL_THEN `&0 < K1 * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `apx_sval(v:real^3) <= &1 / &2 * inv eps0` THEN
    UNDISCH_TAC `--(&1 / &2 * inv eps0) <= apx_sval(v:real^3)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * inv eps = inv eps0`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&400 <= inv eps0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps0:real`; `&1 / &400`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `K INTER IMAGE (e3:real^3->A) (sphere(vec 0,exp(--(&6) / sqrt(&2)))) = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)))) THEN
    SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps0:real`; `z3:A`; `e3:real^3->A`; `v:real^3`] KNCL_CENTRE_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `(e3:real^3->A) v IN K`) o
      check (kncl_has `&45 * h3`) o check (fun th -> is_forall(concl th))) THEN
    MP_TAC(SPECL [`sqrt(&1 + eps0)`; `&801 / &800`; `h3:real`;
                  `abs(--(&6)) + sqrt(&2) * pi`; `&6 + &24 / &5`] KNCL_MUL3_LE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `eps0:real` KNCL_SQRT_BOUNDS) THEN ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= abs(--(&6)) + y`) THEN
        SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS; PI_POS_LE];
        MP_TAC APX_SQRT2_PI THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the core topology *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `inv eps`; `inv eps0`;
                 `e3:real^3->A`; `p:A`; `K:A->bool`; `w0:real^3`; `b:real^3->A`;
                 `f:real^3->real^3`; `f':real^3->real^3`;
                 `(e3:real^3->A) o (\w. exp c % w)`; `(e3:real^3->A) o (\w. exp(&2 * c) % w)`;
                 `IMAGE (e3:real^3->A) (sphere(vec 0,exp(--(&6) / sqrt(&2))))`;
                 `IMAGE (e3:real^3->A) (sphere(vec 0,exp(inv eps / sqrt(&2))))`;
                 `connected_component_of
                    (subtopology top (topspace top DIFF
                       IMAGE (e3:real^3->A) (sphere(vec 0,exp(--(&6) / sqrt(&2)))))) p`;
                 `IMAGE (b:real^3->A) (ball(vec 0,&1))`;
                 `IMAGE (b:real^3->A) (ball(vec 0,&2)) UNION
                  IMAGE ((e3:real^3->A) o (\w. exp(&2 * c) % w)) (rfs_neck_dom (inv(inv eps)))`]
                KNCL_CORE_TOP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_INV_INV] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * inv eps = inv eps0`)) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM APX_SLAB_NECK_DOM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[apx_slab] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[apx_slab; REAL_ARITH `&0 / x = &0`; REAL_EXP_0] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM APX_SLAB_NECK_DOM] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IMAGE_o] THEN
      MP_TAC(SPEC `exp c` KNCL_SPHERE_DILATE) THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_INV] THEN
  ABBREV_TAC `Sig = IMAGE (e3:real^3->A) (sphere(vec 0,exp(--(&6) / sqrt(&2))))` THEN
  ABBREV_TAC `S = IMAGE (e3:real^3->A) (sphere(vec 0,exp(inv eps / sqrt(&2))))` THEN
  ABBREV_TAC `Yin = connected_component_of (subtopology top (topspace top DIFF Sig)) (p:A)` THEN
  ABBREV_TAC `Y = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN
  ABBREV_TAC `U = IMAGE (b:real^3->A) (ball(vec 0,&2)) UNION
                  IMAGE ((e3:real^3->A) o (\w. exp(&2 * c) % w)) (rfs_neck_dom eps)` THEN
  STRIP_TAC THEN
  (* distances: the level -6 sphere and e3 w0 are in the ball *)
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) z3 p = Dst * rho` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `z3:A`; `p:A`] MFD_DIST_SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps0:real`; `z3:A`; `e3:real^3->A`; `p:A`; `w0:real^3`] KNCL_SIG_IN_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && (lhs c = `Y:A->bool` || lhs c = `U:A->bool`) then SYM th else th) THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2)) (b:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_ball_chart top atlas (b:real^3->A)` THEN REWRITE_TAC[mfd_ball_chart];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (b:real^3->A) (cball(vec 0,&1))) /\
                (Y:A->bool) SUBSET IMAGE b (cball(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(vec 0:real^3,&2)`; `b:real^3->A`; `cball(vec 0:real^3,&1)`]
                    KNCL_PARAM_COMPACT_IMAGE) THEN
      ASM_REWRITE_TAC[COMPACT_CBALL] THEN ANTS_TAC THENL [KNCL_NORM_SET_TAC; SIMP_TAC[]];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (b:real^3->A) (ball(vec 0,&1)) = Y`)) THEN
      SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  (* Yin lies in the ball (no interior maximum of d_p) *)
  SUBGOAL_THEN `(Yin:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) p (Dst * rho)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC KNCL_YIN_IN_BALL THEN
    MAP_EVERY EXISTS_TAC [`Sig:A->bool`; `IMAGE (b:real^3->A) (cball(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Sig" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps0`; `e3:real^3->A`;
                     `sphere(vec 0:real^3,exp(--(&6) / sqrt(&2)))`] KNCL_PARAM_COMPACT_IMAGE) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE] THEN ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      UNDISCH_TAC `(Y:A->bool) SUBSET IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
      UNDISCH_TAC `Yin UNION IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (inv eps)) = Y` THEN
      SET_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the sphere S is beyond the ball *)
  SUBGOAL_THEN `&4 * inv eps <= inv eps0` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `K1 * inv eps = inv eps0`)) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN S ==> Dst * rho < mfd_dist (top,atlas) (g:A->real^3^3) p s`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; APX_SPHERE_LEVEL; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `mfd_dist (top,atlas) (g:A->real^3^3) z3 p = Dst * rho`)) THEN
    MATCH_MP_TAC KNCL_S_FAR THEN
    MAP_EVERY EXISTS_TAC [`eps0:real`; `K:A->bool`; `w0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ball lies in Y *)
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) p (Dst * rho) SUBSET Y` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) = Y`)) THEN
    MATCH_MP_TAC KNCL_BALL_IN_COMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (&3 * inv eps)) SUBSET U /\
                Y SUBSET U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `Yin UNION IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (&3 * inv eps)) = U` THEN
      SET_TAC[];
      UNDISCH_TAC `Yin UNION IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (&3 * inv eps)) = U` THEN
      UNDISCH_TAC `Yin UNION IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (inv eps)) = Y` THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t
                             ==> y UNION s = Y ==> y UNION t = U ==> Y SUBSET U`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the final assembly *)
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `Y:A->bool`; `z3:A`; `e3:real^3->A`; `w0:real^3`] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:real^3->A`; `(e3:real^3->A) o (\w. exp(&2 * c) % w)`;
                          `(e3:real^3->A) o (\w. exp c % w)`;
                          `(e3:real^3->A)(exp(&2 * c) % basis 1)`;
                          `(e3:real^3->A)(exp c % basis 1)`;
                          `f:real^3->real^3`; `f':real^3->real^3`] THEN
    REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE FIRST_ASSUM(ACCEPT_TAC o SYM));
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `Yin UNION IMAGE (e3:real^3->A) (apx_slab (--inv eps0) (&3 * inv eps)) = U` THEN
    UNDISCH_TAC `(Yin:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) p (Dst * rho)` THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `(w0:real^3) IN rfs_neck_dom eps0` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC KNCL_NECK_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `eps0:real`; `z3:A`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN EXPAND_TAC "h3" THEN MATCH_MP_TAC KNCL_WIDTH THEN
    MAP_EVERY EXISTS_TAC [`p:A`; `S:A->bool`; `U:A->bool`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
      `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) = Y`) th]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[GSYM IN]]]);;

