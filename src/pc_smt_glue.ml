(* ========================================================================= *)
(* pc_smt_glue: the gluing layer of the smooth topology part (re-capping     *)
(* balls, twisted spheres, ball complements in S^3, sphere sums) and the     *)
(* standard S^3 (its pair of ball charts, conversion to the form of          *)
(* POINCARE_SMOOTH_STATEMENT).                                               *)
(* The real^N inputs (Smale, the weak disc theorem) enter as the statement   *)
(* constants SMT_SMALE_RADIAL_STATEMENT and SMT_DISC_STATEMENT of            *)
(* pc_smt_defs.ml.                                                           *)
(*                                                                           *)
(* Gluing continuous maps, smooth maps and diffeomorphisms                   *)
(* along two open sets; parametrizations restricted and composed.           *)
(* ========================================================================= *)

needs "src/pc_smt_defs.ml";;
needs "src/pc_mfd_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

let MFDG_CONTINUOUS_GLUE = prove
 (`!top (top':B topology) W1 W2 (f1:A->B) f2 h.
        open_in top W1 /\ open_in top W2 /\
        continuous_map (subtopology top W1,top') f1 /\
        continuous_map (subtopology top W2,top') f2 /\
        (!x. x IN W1 ==> h x = f1 x) /\ (!x. x IN W2 ==> h x = f2 x)
        ==> continuous_map (subtopology top (W1 UNION W2),top') h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `W1:A->bool`] OPEN_IN_SUBSET) THEN
  MP_TAC(ISPECL [`top:A topology`; `W2:A->bool`] OPEN_IN_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (W1:A->bool)`; `top':B topology`; `f1:A->B`]
      CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    MP_TAC(ISPECL [`subtopology top (W2:A->bool)`; `top':B topology`; `f2:A->B`]
      CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_UNION] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:B->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN CONJ_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN
     `{x | x IN topspace top INTER (W1 UNION W2) /\ (h:A->B) x IN u} =
      {x | x IN W1 /\ f1 x IN u} UNION {x | x IN W2 /\ f2 x IN u}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[]]);;

let MFDG_SMOOTH_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^M))->bool)
    W1 W2 (f1:A->B) f2 h.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        open_in top W1 /\ open_in top W2 /\
        continuous_map (subtopology top W1,top') f1 /\
        continuous_map (subtopology top W2,top') f2 /\
        mfd_smooth_map atlas atlas' W1 f1 /\ mfd_smooth_map atlas atlas' W2 f2 /\
        (!x. x IN W1 ==> h x = f1 x) /\ (!x. x IN W2 ==> h x = f2 x)
        ==> mfd_smooth_map atlas atlas' (W1 UNION W2) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology top (W1 UNION W2),top') (h:A->B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDG_CONTINUOUS_GLUE THEN
    MAP_EVERY EXISTS_TAC [`f1:A->B`; `f2:A->B`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W1 UNION W2:A->bool`; `h:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[OPEN_IN_UNION];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; IN_UNION] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(f1:A->B) x IN FST(c':(B->bool)#(B->real^M))` ASSUME_TAC THENL
     [UNDISCH_TAC `(h:A->B) x IN FST(c':(B->bool)#(B->real^M))` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                  {x | x IN FST c INTER W1 /\
                       (f1:A->B) x IN FST(c':(B->bool)#(B->real^M))}` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W1:A->bool`; `f1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c':(B->bool)#(B->real^M)) o (f1:A->B) o
                chart_inv(c:(A->bool)#(A->real^N))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                     (atlas':((B->bool)#(B->real^M))->bool) W1 (f1:A->B)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(f2:A->B) x IN FST(c':(B->bool)#(B->real^M))` ASSUME_TAC THENL
     [UNDISCH_TAC `(h:A->B) x IN FST(c':(B->bool)#(B->real^M))` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                  {x | x IN FST c INTER W2 /\
                       (f2:A->B) x IN FST(c':(B->bool)#(B->real^M))}` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W2:A->bool`; `f2:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c':(B->bool)#(B->real^M)) o (f2:A->B) o
                chart_inv(c:(A->bool)#(A->real^N))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                     (atlas':((B->bool)#(B->real^M))->bool) W2 (f2:A->B)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* Gluing two diffeomorphisms: h and k agree with f1, g1 and f2, g2 on the   *)
(* two pieces of open covers of the two manifolds.                          *)

let MFD_DIFFEO_GLUE = prove
 (`!topX (atlasX:((A->bool)#(A->real^N))->bool)
    topY (atlasY:((B->bool)#(B->real^M))->bool)
    W1 W2 V1 V2 f1 g1 f2 g2 h k.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_diffeo topX atlasX W1 topY atlasY V1 f1 g1 /\
        mfd_diffeo topX atlasX W2 topY atlasY V2 f2 g2 /\
        W1 UNION W2 = topspace topX /\ V1 UNION V2 = topspace topY /\
        (!x. x IN W1 ==> h x = f1 x) /\ (!x. x IN W2 ==> h x = f2 x) /\
        (!y. y IN V1 ==> k y = g1 y) /\ (!y. y IN V2 ==> k y = g2 y)
        ==> mfd_diffeo topX atlasX (topspace topX) topY atlasY (topspace topY) h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `W1:A->bool`; `topY:B topology`;
                 `atlasY:((B->bool)#(B->real^M))->bool`; `V1:B->bool`;
                 `f1:A->B`; `g1:B->A`] MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `W2:A->bool`; `topY:B topology`;
                 `atlasY:((B->bool)#(B->real^M))->bool`; `V2:B->bool`;
                 `f2:A->B`; `g2:B->A`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_diffeo]) THEN
  SUBGOAL_THEN
   `continuous_map (subtopology topX (W1 UNION W2),topY) (h:A->B) /\
    mfd_smooth_map (atlasX:((A->bool)#(A->real^N))->bool)
                   (atlasY:((B->bool)#(B->real^M))->bool) (W1 UNION W2) h /\
    continuous_map (subtopology topY (V1 UNION V2),topX) (k:B->A) /\
    mfd_smooth_map atlasY atlasX (V1 UNION V2) k`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDG_CONTINUOUS_GLUE THEN
      MAP_EVERY EXISTS_TAC [`f1:A->B`; `f2:A->B`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_SMOOTH_GLUE THEN
      MAP_EVERY EXISTS_TAC
       [`topX:A topology`; `topY:B topology`; `f1:A->B`; `f2:A->B`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_CONTINUOUS_GLUE THEN
      MAP_EVERY EXISTS_TAC [`g1:B->A`; `g2:B->A`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_SMOOTH_GLUE THEN
      MAP_EVERY EXISTS_TAC
       [`topY:B topology`; `topX:A topology`; `g1:B->A`; `g2:B->A`] THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN W1 ==> (f1:A->B) x IN V1) /\ (!x. x IN W2 ==> (f2:A->B) x IN V2) /\
    (!y. y IN V1 ==> (g1:B->A) y IN W1) /\ (!y. y IN V2 ==> (g2:B->A) y IN W2)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE;
                  homeomorphic_maps] THEN
  UNDISCH_TAC `W1 UNION W2 = topspace (topX:A topology)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `V1 UNION V2 = topspace (topY:B topology)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_UNION] THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Parametrizations of open sets of real^N.                                  *)
(* ------------------------------------------------------------------------- *)

let MFD_EUCLIDEAN_ATLAS = prove
 (`smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`,
  MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let MFD_PARAM_MAPS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A).
        mfd_param top atlas s e
        ==> ?e'. open s /\ open_in top (IMAGE e s) /\
                 continuous_map (subtopology euclidean s,top) e /\
                 continuous_map (subtopology top (IMAGE e s),euclidean) e' /\
                 IMAGE e' (IMAGE e s) = s /\
                 (!x. x IN s ==> e'(e x) = x) /\
                 (!y. y IN IMAGE e s ==> e(e' y) = y) /\
                 mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas
                            (IMAGE e s) e e'`,
  REWRITE_TAC[mfd_param] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `e':A->real^N`) THEN EXISTS_TAC `e':A->real^N` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SIMP_TAC[OPEN_IN_EUCLIDEAN]);;

let MFD_PARAM_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s t (e:real^N->A).
        mfd_param top atlas s e /\ open t /\ t SUBSET s
        ==> mfd_param top atlas t e`,
  REWRITE_TAC[mfd_param] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `e':A->real^N` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `IMAGE (e:real^N->A) s`] THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN]);;

let MFD_PARAM_IMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s t (e:real^N->A).
        mfd_param top atlas s e /\ open t /\ t SUBSET s
        ==> open_in top (IMAGE e t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `t:real^N->bool`; `e:real^N->A`]
                MFD_PARAM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MESON_TAC[]);;

let MFD_PARAM_INJ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) x y.
        mfd_param top atlas s e /\ x IN s /\ y IN s /\ e x = e y ==> x = y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  ASM_MESON_TAC[]);;

let MFD_PARAM_COMPACT_IMAGE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) k.
        mfd_param top atlas s e /\ compact k /\ k SUBSET s
        ==> compact_in top (IMAGE e k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN]);;

let MFD_PARAM_COMPOSE_DIFFEO = prove
 (`!topX (atlasX:((A->bool)#(A->real^N))->bool) topY (atlasY:((B->bool)#(B->real^N))->bool)
    s (e:real^N->A) W W' F G.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_param topX atlasX s e /\
        mfd_diffeo topX atlasX W topY atlasY W' F G /\ IMAGE e s SUBSET W
        ==> mfd_param topY atlasY s (F o e)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  REWRITE_TAC[mfd_param] THEN EXISTS_TAC `(e':A->real^N) o (G:B->A)` THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
    `IMAGE (e:real^N->A) s`] THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
  MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `W':B->bool`] THEN ASM_REWRITE_TAC[]);;

let MFD_PARAM_PRECOMPOSE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) t t' h h'.
        smooth_manifold_atlas top atlas /\
        mfd_param top atlas s e /\ diffeomorphism_on t t' h h' /\ t' SUBSET s
        ==> mfd_param top atlas t (e o h)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) t' (e:real^N->A)`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  REWRITE_TAC[mfd_param] THEN EXISTS_TAC `(h':real^N->real^N) o (e':A->real^N)` THEN
  SUBGOAL_THEN `IMAGE ((e:real^N->A) o (h:real^N->real^N)) t = IMAGE e t'`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
  MAP_EVERY EXISTS_TAC
   [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
    `t':real^N->bool`] THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN]);;

(* ------------------------------------------------------------------------- *)
(* Smooth maps and diffeomorphisms depend only on values on the set; inverse *)
(* charts are parametrizations; the standard pair of ball charts of S^3      *)
(* (SMT_S3_STANDARD_BALLS); immersions composed with diffeomorphisms and the *)
(* conversion to the form of POINCARE_SMOOTH_STATEMENT                       *)
(* (SMT_POINCARE_CONVERSION).                                                *)
(* ------------------------------------------------------------------------- *)

let MFD_SMOOTH_MAP_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (atlas':((B->bool)#(B->real^M))->bool)
    W (f:A->B) g.
        smooth_manifold_atlas top atlas /\
        mfd_smooth_map atlas atlas' W f /\ (!x. x IN W ==> g x = f x)
        ==> mfd_smooth_map atlas atlas' W g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN FST c INTER W /\ (g:A->B) x IN FST(c':(B->bool)#(B->real^M))} =
    {x | x IN FST(c:(A->bool)#(A->real^N)) INTER W /\ (f:A->B) x IN FST c'}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `SND(c':(B->bool)#(B->real^M)) o (f:A->B) o
              chart_inv(c:(A->bool)#(A->real^N))` THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
  ASM_SIMP_TAC[]);;

let MFD_DIFFEO_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W top' (atlas':((B->bool)#(B->real^M))->bool) W'
    f g f' g'.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas W top' atlas' W' f g /\
        (!x. x IN W ==> f' x = f x) /\ (!y. y IN W' ==> g' y = g y)
        ==> mfd_diffeo top atlas W top' atlas' W' f' g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAPS_EQ THEN
    MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`] THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->B`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_EQ THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `g:B->A`] THEN ASM_REWRITE_TAC[]]);;

let MFD_PARAM_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) e1.
        smooth_manifold_atlas top atlas /\
        mfd_param top atlas s e /\ (!x. x IN s ==> e1 x = e x)
        ==> mfd_param top atlas s e1`,
  REWRITE_TAC[mfd_param] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (e1:real^N->A) s = IMAGE e s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `e':A->real^N` THEN MATCH_MP_TAC MFD_DIFFEO_EQ THEN
  MAP_EVERY EXISTS_TAC [`e:real^N->A`; `e':A->real^N`] THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS]);;

(* The inverse of a chart parametrizes the chart domain. *)

let MFD_PARAM_CHART_INV = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> mfd_param top atlas (IMAGE phi U) (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (chart_inv (U,phi)) (IMAGE (phi:A->real^N) U) = U`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x. x IN U ==> chart_inv (U,phi) ((phi:A->real^N) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param] THEN EXISTS_TAC `phi:A->real^N` THEN
  ASM_REWRITE_TAC[mfd_diffeo; OPEN_IN_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM] THEN
    REWRITE_TAC[homeomorphic_maps] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP);
      MATCH_MP_TAC MFDC_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`U0:real^N->bool`; `id0:real^N->real^N`;
                         `V:A->bool`; `psi:A->real^N`] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST1_TAC) ASSUME_TAC) THEN
    REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
    SUBGOAL_THEN
     `{y | y IN IMAGE (phi:A->real^N) U /\ chart_inv (U,phi) y IN V} =
      IMAGE phi (U INTER V)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
          MP_TAC) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `chart_trans (U:A->bool,phi:A->real^N) (V,psi)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans; SND] THEN
      SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
      MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`;
                         `U0:real^N->bool`; `id0:real^N->real^N`] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)) THEN
    REWRITE_TAC[FST; SND; IN_UNIV; SET_RULE `{x:A | x IN s} = s`] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `chart_trans (V:A->bool,psi:A->real^N) (U,phi)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans; SND];
      MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The standard pair of ball charts of S^3.                                  *)
(* ------------------------------------------------------------------------- *)

let SMT_CHART_INV_STEREO3 = prove
 (`(!y. chart_inv (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n) y =
        stereo3_n_inv y) /\
   (!y. chart_inv (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s) y =
        stereo3_s_inv y)`,
  REWRITE_TAC[chart_inv; FST; SND] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `x:real^4` THEN EQ_TAC THENL
   [MESON_TAC[STEX_STEREO3_N_LEFT];
    MESON_TAC[STEX_STEREO3_N_INV_IN; STEX_STEREO3_N_RIGHT];
    MESON_TAC[STEX_STEREO3_S_LEFT];
    MESON_TAC[STEX_STEREO3_S_INV_IN; STEX_STEREO3_S_RIGHT]]);;

let SMT_STEREO3_PARAMS = prove
 (`mfd_param (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas
             (:real^3) stereo3_n_inv /\
   mfd_param (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas
             (:real^3) stereo3_s_inv`,
  CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_EQ THENL
   [EXISTS_TAC `chart_inv (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n)` THEN
    REWRITE_TAC[SPHERE3_ATLAS] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                     `sphere3_atlas`; `sphere(vec 0:real^4,&1) DELETE basis 4`;
                     `stereo3_n`] MFD_PARAM_CHART_INV) THEN
      REWRITE_TAC[SPHERE3_ATLAS; sphere3_atlas; IN_INSERT;
                  STEX_STEREO3_HOMEOMORPHISMS];
      REWRITE_TAC[SMT_CHART_INV_STEREO3]];
    EXISTS_TAC `chart_inv (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s)` THEN
    REWRITE_TAC[SPHERE3_ATLAS] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                     `sphere3_atlas`; `sphere(vec 0:real^4,&1) DELETE --(basis 4)`;
                     `stereo3_s`] MFD_PARAM_CHART_INV) THEN
      REWRITE_TAC[SPHERE3_ATLAS; sphere3_atlas; IN_INSERT;
                  STEX_STEREO3_HOMEOMORPHISMS];
      REWRITE_TAC[SMT_CHART_INV_STEREO3]]]);;

let SMT_S3_HEMISPHERES = prove
 (`sphere(vec 0:real^4,&1) =
      IMAGE stereo3_n_inv (cball(vec 0,&1)) UNION
      IMAGE stereo3_s_inv (cball(vec 0,&1)) /\
   DISJOINT (IMAGE stereo3_n_inv (ball(vec 0,&1)))
            (IMAGE stereo3_s_inv (ball(vec 0,&1)))`,
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_CBALL_0] THEN
      X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^4)$4 <= &0` THENL
       [DISJ1_TAC THEN EXISTS_TAC `stereo3_n (x:real^4)` THEN
        SUBGOAL_THEN `(x:real^4) IN sphere(vec 0,&1) DELETE basis 4` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `(basis 4:real^4)$4 <= &0` THEN
          SIMP_TAC[BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[STEX_STEREO3_N_LEFT] THEN
        MP_TAC(SPEC `x:real^4` STEX_STEREO3_N_NORM2) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN REWRITE_TAC[NORM_LE_SQUARE; GSYM NORM_POW_2] THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_POW_ONE] THEN
        SUBGOAL_THEN `&0 < &1 - (x:real^4)$4` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN EXISTS_TAC `stereo3_s (x:real^4)` THEN
        SUBGOAL_THEN `(x:real^4) IN sphere(vec 0,&1) DELETE --(basis 4)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `~((--(basis 4):real^4)$4 <= &0)` THEN
          SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[STEX_STEREO3_S_LEFT] THEN
        MP_TAC(SPEC `x:real^4` STEX_STEREO3_S_NORM2) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN REWRITE_TAC[NORM_LE_SQUARE; GSYM NORM_POW_2] THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_POW_ONE] THEN
        SUBGOAL_THEN `&0 < &1 + (x:real^4)$4` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE] THEN
      MESON_TAC[STEX_STEREO3_N_INV_IN; STEX_STEREO3_S_INV_IN; IN_DELETE]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_BALL_0] THEN
    X_GEN_TAC `z:real^4` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(stereo3_n_inv y)$4 = (stereo3_s_inv w)$4` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[STEX_STEREO3_N_INV_COMPONENTS; STEX_STEREO3_S_INV_COMPONENTS] THEN
    SUBGOAL_THEN `norm(y:real^3) pow 2 < &1 /\ norm(w:real^3) pow 2 < &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      ASM_REWRITE_TAC[NORM_POS_LE; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3) pow 2 + &1 /\ &0 < norm(w:real^3) pow 2 + &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> &0 < a + &1`) THEN
      REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(norm(y:real^3) pow 2 - &1) / (norm y pow 2 + &1) < &0 /\
                  &0 < (&1 - norm(w:real^3) pow 2) / (norm w pow 2 + &1)`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let SMT_S3_STANDARD_BALLS = prove
 (`SMT_S3_STANDARD_BALLS_STATEMENT`,
  REWRITE_TAC[SMT_S3_STANDARD_BALLS_STATEMENT; mfd_ball_chart] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SMT_STEREO3_PARAMS; OPEN_BALL; SUBSET_UNIV];
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SMT_STEREO3_PARAMS; OPEN_BALL; SUBSET_UNIV];
    REWRITE_TAC[SMT_S3_HEMISPHERES];
    REWRITE_TAC[SMT_S3_HEMISPHERES];
    ACCEPT_TAC SMT_STEREO3_INVERSION]);;

(* ------------------------------------------------------------------------- *)
(* Immersions composed with diffeomorphisms; SMT_POINCARE_CONVERSION.        *)
(* ------------------------------------------------------------------------- *)

let MFDG_LEFT_INVERSE_DERIV_INJ = prove
 (`!s t (k:real^M->real^N) (k':real^N->real^M) y h.
        open s /\ open t /\ smooth_map_on s k /\ smooth_map_on t k' /\
        IMAGE k s SUBSET t /\ (!x. x IN s ==> k'(k x) = x) /\ y IN s /\
        frechet_derivative k (at y) h = vec 0
        ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((k:real^M->real^N) has_derivative frechet_derivative k (at y))
                (at y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->real^N`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((k':real^N->real^M) has_derivative
                 frechet_derivative k' (at ((k:real^M->real^N) y)))
                (at (k y))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `k':real^N->real^M`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^M. x) has_derivative
     (frechet_derivative (k':real^N->real^M) (at ((k:real^M->real^N) y)) o
      frechet_derivative k (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`(k':real^N->real^M) o (k:real^M->real^N)`; `s:real^M->bool`] THEN
    ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (k':real^N->real^M) (at ((k:real^M->real^N) y)) o
    frechet_derivative k (at y) = (\h:real^M. h)`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^M. x`; `y:real^M`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^M`) THEN ASM_REWRITE_TAC[o_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (k':real^N->real^M)
                        (at ((k:real^M->real^N) y))` LINEAR_0) THEN
  UNDISCH_TAC `((k':real^N->real^M) has_derivative
                frechet_derivative k' (at ((k:real^M->real^N) y))) (at (k y))` THEN
  SIMP_TAC[has_derivative]);;

(* The local step: near a point, i o F o chart_inv is g' o k with k a chart  *)
(* transition of F (left invertible) and g' the immersion representative.    *)

let MFDG_IMMERSION_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    (i:B->real^K) Fm Gm U phi x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        smooth_immersion_into atlas' i /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') Fm Gm /\
        (U,phi) IN atlas /\ x IN U
        ==> ?t g1. open t /\ phi x IN t /\ t SUBSET IMAGE phi U /\
                   smooth_map_on t g1 /\
                   (!y. y IN t ==> g1 y = (i o Fm o chart_inv (U,phi)) y) /\
                   (!h. frechet_derivative g1 (at (phi x)) h = vec 0 ==> h = vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  UNDISCH_TAC `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
    (topspace top) (top':B topology) (atlas':((B->bool)#(B->real^N))->bool)
    (topspace top') (Fm:A->B) (Gm:B->A)` THEN
  REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fm:A->B) x IN topspace top'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?V psi. (V,psi) IN (atlas':((B->bool)#(B->real^N))->bool) /\
                        (Fm:A->B) x IN V`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_manifold_atlas]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `V:B->bool`; `psi:B->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `V:B->bool`; `psi:B->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`V:B->bool`; `psi:B->real^N`] o
    GEN_REWRITE_RULE I [smooth_immersion_into]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^N->real^K`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                 `topspace top:A->bool`; `Fm:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(V:B->bool,psi:B->real^N)`; `(U:A->bool,phi:A->real^N)`;
                 `topspace top':B->bool`; `Gm:B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; FST; SND] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (phi:A->real^N)
                {y | y IN U INTER topspace top /\ (Fm:A->B) y IN V}` THEN
  EXISTS_TAC `(g':real^N->real^K) o
              ((psi:B->real^N) o (Fm:A->B) o chart_inv (U:A->bool,phi:A->real^N))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (psi:B->real^N) V` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                     (atlas':((B->bool)#(B->real^N))->bool) (topspace top) (Fm:A->B)` THEN
      REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`;
                                 `(V:B->bool,psi:B->real^N)`]) THEN
      ASM_REWRITE_TAC[FST; SND]];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = (psi:B->real^N) o (Fm:A->B) o chart_inv (U:A->bool,phi:A->real^N)` THEN
  X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (phi:A->real^N)
                     {y | y IN U INTER topspace top /\ (Fm:A->B) y IN V})
                  (k:real^N->real^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^N))->bool) (topspace top) (Fm:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`;
                               `(V:B->bool,psi:B->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `((k:real^N->real^N) has_derivative frechet_derivative k (at (phi(x:A))))
                (at (phi x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:A->real^N)
                     {y | y IN U INTER topspace top /\ (Fm:A->B) y IN V}`;
                   `k:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->real^N)(phi(x:A)) IN IMAGE (psi:B->real^N) V` ASSUME_TAC
  THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g':real^N->real^K) has_derivative
                 frechet_derivative g' (at ((k:real^N->real^N)(phi(x:A)))))
                (at (k(phi x)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (psi:B->real^N) V`; `g':real^N->real^K`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative ((g':real^N->real^K) o (k:real^N->real^N)) (at (phi(x:A))) =
    frechet_derivative g' (at (k(phi x))) o frechet_derivative k (at (phi x))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (k:real^N->real^N) (at (phi(x:A))) h = vec 0`
  MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN
    EXISTS_TAC `(k:real^N->real^N)(phi(x:A))` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frechet_derivative ((g':real^N->real^K) o (k:real^N->real^N))
                   (at (phi(x:A))) h = vec 0` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC MFDG_LEFT_INVERSE_DERIV_INJ THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:A->real^N) {y | y IN U INTER topspace top /\ (Fm:A->B) y IN V}`;
    `IMAGE (psi:B->real^N) {z | z IN V INTER topspace top' /\ (Gm:B->A) z IN U}`;
    `k:real^N->real^N`;
    `(phi:A->real^N) o (Gm:B->A) o chart_inv (V:B->bool,psi:B->real^N)`;
    `phi(x:A):real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth_map (atlas':((B->bool)#(B->real^N))->bool)
                   (atlas:((A->bool)#(A->real^N))->bool) (topspace top') (Gm:B->A)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`(V:B->bool,psi:B->real^N)`;
                               `(U:A->bool,phi:A->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND];
    EXPAND_TAC "k" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    ASM SET_TAC[];
    EXPAND_TAC "k" THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]]);;

let MFD_IMMERSION_COMPOSE_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^N))->bool)
    (i:B->real^K) Fm Gm.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        smooth_immersion_into atlas' i /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') Fm Gm
        ==> smooth_immersion_into atlas (i o Fm)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_immersion_into] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(i:B->real^K) o (Fm:A->B) o chart_inv (U:A->bool,phi:A->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `i:B->real^K`; `Fm:A->B`; `Gm:B->A`; `U:A->bool`;
                   `phi:A->real^N`; `x:A`] MFDG_IMMERSION_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
      (X_CHOOSE_THEN `g1:real^N->real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g1:real^N->real^K` THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `i:B->real^K`; `Fm:A->B`; `Gm:B->A`; `U:A->bool`;
                   `phi:A->real^N`; `x:A`] MFDG_IMMERSION_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
      (X_CHOOSE_THEN `g1:real^N->real^K` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative (g1:real^N->real^K) (at (phi(x:A))) =
      frechet_derivative ((i:B->real^K) o (Fm:A->B) o chart_inv (U,phi))
                         (at (phi x))`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`g1:real^N->real^K`; `t:real^N->bool`] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `g1:real^N->real^K`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[]]);;

let SMT_POINCARE_CONVERSION = prove
 (`!u:A->bool. SMT_POINCARE_CONVERSION_STATEMENT u`,
  REWRITE_TAC[SMT_POINCARE_CONVERSION_STATEMENT; mfd_diffeomorphic] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `Fm:A->real^4` (X_CHOOSE_TAC `Gm:real^4->A`)))) THEN
  EXISTS_TAC `Fm:A->real^4` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `sphere3_atlas`; `\x:real^4. x`; `Fm:A->real^4`;
                   `Gm:real^4->A`] MFD_IMMERSION_COMPOSE_DIFFEO) THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS; SPHERE3_INCLUSION_IMMERSION] THEN
    REWRITE_TAC[o_DEF; ETA_AX];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP]]);;

(* The main theorem from the classification statement: closed, simply        *)
(* connected smooth 3-manifolds are diffeomorphic to the standard S^3.       *)

let SMT_HEADLINE_FROM_DIFFEOMORPHIC = prove
 (`!u:A->bool.
        (!top atlas.
            hausdorff_space top /\
            smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
            compact_space top /\ ~(topspace top = {}) /\
            simply_connected_space top
            ==> mfd_diffeomorphic top atlas
                  (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas)
        ==> POINCARE_SMOOTH_STATEMENT u`,
  MESON_TAC[SMT_HEADLINE_FROM_CONVERSION; SMT_POINCARE_CONVERSION]);;

(* ------------------------------------------------------------------------- *)
(* Re-capping a ball (M1, SMT_GLUE_BALL_STATEMENT) from Smale's              *)
(* theorem in radial form.                                                   *)
(* ------------------------------------------------------------------------- *)

(* A norm-preserving diffeomorphism of R^N restricts to every ball. *)

let SMT_NORM_PRESERVING_BALL = prove
 (`!(h:real^N->real^N) k s.
        diffeomorphism_on (:real^N) (:real^N) h k /\ (!x. norm(h x) = norm x)
        ==> (!y. norm(k y) = norm y) /\
            IMAGE h (ball(vec 0,s)) = ball(vec 0,s) /\
            IMAGE k (ball(vec 0,s)) = ball(vec 0,s) /\
            diffeomorphism_on (ball(vec 0,s)) (ball(vec 0,s)) h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV]) THEN
  SUBGOAL_THEN `!y. norm((k:real^N->real^N) y) = norm y` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM(SPEC `y:real^N` th)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (ball(vec 0,s)) = ball(vec 0,s) /\
                IMAGE (k:real^N->real^N) (ball(vec 0,s)) = ball(vec 0,s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN CONJ_TAC THEN
    X_GEN_TAC `y:real^N` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_BALL] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

(* The ball piece of the glued map: c o h o b^-1 on b(ball(0,s)).           *)

let SMT_GLUE_PIECE = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topY (atlasY:((B->bool)#(B->real^3))->bool) b c h k s.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_ball_chart topX atlasX b /\ mfd_ball_chart topY atlasY c /\
        diffeomorphism_on (:real^3) (:real^3) h k /\ (!x. norm(h x) = norm x) /\
        &0 < s /\ s <= &2
        ==> ?f1 g1. mfd_diffeo topX atlasX (IMAGE b (ball(vec 0,s)))
                               topY atlasY (IMAGE c (ball(vec 0,s))) f1 g1 /\
                    (!x. x IN ball(vec 0,s) ==> f1(b x) = c(h x)) /\
                    (!y. y IN ball(vec 0,s) ==> g1(c y) = b(k y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ball(vec 0:real^3,s) SUBSET ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `k:real^3->real^3`; `s:real`]
    SMT_NORM_PRESERVING_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param topX atlasX (ball(vec 0:real^3,s)) (b:real^3->A) /\
                mfd_param topY atlasY (ball(vec 0:real^3,s)) (c:real^3->B)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM mfd_ball_chart];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c':B->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  MAP_EVERY EXISTS_TAC
   [`(c:real^3->B) o (h:real^3->real^3) o (b':A->real^3)`;
    `((b:real^3->A) o (k:real^3->real^3)) o (c':B->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
      `ball(vec 0:real^3,s)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
    MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
      `ball(vec 0:real^3,s)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]]);;

(* Re-capping in general form: the ball pieces are matched by a             *)
(* norm-preserving diffeomorphism h of R^3 (inverse k), and F(b x) = c(h x)  *)
(* on a collar.  The glued map is c o h o b^-1 on b(ball(0,s)), s = min r 2, *)
(* and F elsewhere.                                                          *)

let SMT_GLUE_BALL_GEN = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topY (atlasY:((B->bool)#(B->real^3))->bool) b c Fm Gm h k r.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_ball_chart topX atlasX b /\ mfd_ball_chart topY atlasY c /\
        diffeomorphism_on (:real^3) (:real^3) h k /\ (!x. norm(h x) = norm x) /\
        mfd_diffeo topX atlasX (topspace topX DIFF IMAGE b (cball(vec 0,&1)))
                   topY atlasY (topspace topY DIFF IMAGE c (cball(vec 0,&1))) Fm Gm /\
        &1 < r /\ (!x. x IN annulus (&1) r ==> Fm(b x) = c(h x))
        ==> ?H K. mfd_diffeo topX atlasX (topspace topX)
                             topY atlasY (topspace topY) H K /\
                  (!p. p IN topspace topX DIFF IMAGE b (ball(vec 0,&2))
                       ==> H p = Fm p)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "collar") THEN
  SUBGOAL_THEN `?s. &1 < s /\ s <= &2 /\ s <= r` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r (&2)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `b:real^3->A`; `c:real^3->B`; `h:real^3->real^3`;
                 `k:real^3->real^3`; `s:real`] SMT_GLUE_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:A->B` (X_CHOOSE_THEN `g1:B->A`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `k:real^3->real^3`; `s:real`]
    SMT_NORM_PRESERVING_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* facts about the two ball charts *)
  SUBGOAL_THEN
   `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET topspace topX /\
    IMAGE (c:real^3->B) (ball(vec 0,&2)) SUBSET topspace topY /\
    (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ b x = b y ==> x = y) /\
    (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[mfd_ball_chart]) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`atlasX:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`atlasY:((B->bool)#(B->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      ASM_MESON_TAC[MFD_PARAM_INJ];
      ASM_MESON_TAC[MFD_PARAM_INJ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,s) SUBSET ball(vec 0,&2) /\
                cball(vec 0:real^3,&1) SUBSET ball(vec 0,s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the radial collar relation *)
  SUBGOAL_THEN `!x:real^3. x IN annulus (&1) s ==> (Fm:A->B)((b:real^3->A) x) = (c:real^3->B)((h:real^3->real^3) x)`
  (LABEL_TAC "coll2") THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "collar" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topspace topX DIFF IMAGE (b:real^3->A) (cball(vec 0,&1))`;
                 `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `topspace topY DIFF IMAGE (c:real^3->B) (cball(vec 0,&1))`;
                 `Fm:A->B`; `Gm:B->A`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\p:A. if p IN IMAGE (b:real^3->A) (ball(vec 0,s)) then (f1:A->B) p else Fm p` THEN
  EXISTS_TAC `\q:B. if q IN IMAGE (c:real^3->B) (ball(vec 0,s)) then (g1:B->A) q else Gm q` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC MFD_DIFFEO_GLUE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (b:real^3->A) (ball(vec 0,s))`;
    `topspace topX DIFF IMAGE (b:real^3->A) (cball(vec 0,&1))`;
    `IMAGE (c:real^3->B) (ball(vec 0,s))`;
    `topspace topY DIFF IMAGE (c:real^3->B) (cball(vec 0,&1))`;
    `f1:A->B`; `g1:B->A`; `Fm:A->B`; `Gm:B->A`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    SIMP_TAC[];
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC o
      REWRITE_RULE[IN_IMAGE]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "coll2" MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[IN_BALL_0]] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE; GSYM IN_CBALL_0] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?x'. (b:real^3->A) x = b x' /\ x' IN cball(vec 0,&1))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[];
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN X_GEN_TAC `q:B` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
      REWRITE_RULE[IN_IMAGE]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(norm(y:real^3) <= &1)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_CBALL_0] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?x'. (c:real^3->B) y = c x' /\ x' IN cball(vec 0,&1))` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(k:real^3->real^3) y IN annulus (&1) s` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN ball(vec 0,s)` THEN REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3)(k(y:real^3)) = y` ASSUME_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on (:real^3) (:real^3) (h:real^3->real^3) k` THEN
      REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^3->B) y = Fm((b:real^3->A)(k y))` SUBST1_TAC THENL
     [USE_THEN "coll2" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
    SUBGOAL_THEN
     `(b:real^3->A)(k(y:real^3)) IN topspace topX DIFF IMAGE b (cball(vec 0,&1))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET topspace topX` THEN
        MATCH_MP_TAC(SET_RULE
         `(x:A) IN IMAGE (f:real^3->A) s ==> IMAGE f s SUBSET t ==> x IN t`) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(k:real^3->real^3) y IN annulus (&1) s` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(k:real^3->real^3) y = z` MP_TAC THENL
         [UNDISCH_TAC `!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\
                             (b:real^3->A) x = b y ==> x = y` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(k:real^3->real^3) y IN annulus (&1) s` THEN
          UNDISCH_TAC `(z:real^3) IN cball(vec 0,&1)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
        UNDISCH_TAC `(k:real^3->real^3) y IN annulus (&1) s` THEN
        UNDISCH_TAC `(z:real^3) IN cball(vec 0,&1)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM; IN_CBALL_0] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* M1 from Smale's theorem in radial form. *)

let SMT_GLUE_BALL = prove
 (`SMT_SMALE_RADIAL_STATEMENT
   ==> !u:A->bool v:B->bool. SMT_GLUE_BALL_STATEMENT u v`,
  REWRITE_TAC[SMT_SMALE_RADIAL_STATEMENT; SMT_GLUE_BALL_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
    `b:real^3->A`; `c:real^3->B`; `Fm:A->B`; `Gm:B->A`;
    `f:real^3->real^3`; `g:real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "collar"))))))))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^3->real^3`; `g:real^3->real^3`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `radial_ext:(real^3->real^3)->real^3->real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3`
    (X_CHOOSE_THEN `k:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hrad"))))) THEN
  MATCH_MP_TAC SMT_GLUE_BALL_GEN THEN
  MAP_EVERY EXISTS_TAC
   [`c:real^3->B`; `Gm:B->A`; `h:real^3->real^3`; `k:real^3->real^3`;
    `min r (&2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) x = radial_ext f x` SUBST1_TAC THENL
   [USE_THEN "hrad" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "collar" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Gluing over open subsets, complements of a pair of balls,                 *)
(* the standard S^3 as a manifold, twisted spheres (M2).                     *)
(* ------------------------------------------------------------------------- *)

(* Gluing two diffeomorphisms between open sets (not necessarily covering). *)

let MFD_DIFFEO_GLUE_OPEN = prove
 (`!topX (atlasX:((A->bool)#(A->real^N))->bool)
    topY (atlasY:((B->bool)#(B->real^M))->bool)
    W1 W2 V1 V2 f1 g1 f2 g2 h k.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_diffeo topX atlasX W1 topY atlasY V1 f1 g1 /\
        mfd_diffeo topX atlasX W2 topY atlasY V2 f2 g2 /\
        (!x. x IN W1 ==> h x = f1 x) /\ (!x. x IN W2 ==> h x = f2 x) /\
        (!y. y IN V1 ==> k y = g1 y) /\ (!y. y IN V2 ==> k y = g2 y)
        ==> mfd_diffeo topX atlasX (W1 UNION W2) topY atlasY (V1 UNION V2) h k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `W1:A->bool`; `topY:B topology`;
                 `atlasY:((B->bool)#(B->real^M))->bool`; `V1:B->bool`;
                 `f1:A->B`; `g1:B->A`] MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^N))->bool`;
                 `W2:A->bool`; `topY:B topology`;
                 `atlasY:((B->bool)#(B->real^M))->bool`; `V2:B->bool`;
                 `f2:A->B`; `g2:B->A`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_diffeo]) THEN
  SUBGOAL_THEN
   `continuous_map (subtopology topX (W1 UNION W2),topY) (h:A->B) /\
    mfd_smooth_map (atlasX:((A->bool)#(A->real^N))->bool)
                   (atlasY:((B->bool)#(B->real^M))->bool) (W1 UNION W2) h /\
    continuous_map (subtopology topY (V1 UNION V2),topX) (k:B->A) /\
    mfd_smooth_map atlasY atlasX (V1 UNION V2) k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDG_CONTINUOUS_GLUE THEN
      MAP_EVERY EXISTS_TAC [`f1:A->B`; `f2:A->B`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_SMOOTH_GLUE THEN
      MAP_EVERY EXISTS_TAC
       [`topX:A topology`; `topY:B topology`; `f1:A->B`; `f2:A->B`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_CONTINUOUS_GLUE THEN
      MAP_EVERY EXISTS_TAC [`g1:B->A`; `g2:B->A`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDG_SMOOTH_GLUE THEN
      MAP_EVERY EXISTS_TAC
       [`topY:B topology`; `topX:A topology`; `g1:B->A`; `g2:B->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN W1 ==> (f1:A->B) x IN V1) /\ (!x. x IN W2 ==> (f2:A->B) x IN V2) /\
    (!y. y IN V1 ==> (g1:B->A) y IN W1) /\ (!y. y IN V2 ==> (g2:B->A) y IN W2)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_diffeo; OPEN_IN_UNION; homeomorphic_maps;
               CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_UNION] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Points of a ball chart on the unit sphere are limits from inside and from *)
(* outside the unit ball.                                                    *)

let MFDG_BALL_CHART_SPHERE_APPROX = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b U y.
        mfd_ball_chart top atlas b /\ open_in top U /\ norm y = &1 /\ b y IN U
        ==> (?y'. norm y' < &1 /\ b y' IN U) /\
            (?y'. &1 < norm y' /\ norm y' < &2 /\ b y' IN U)`,
  REWRITE_TAC[mfd_ball_chart] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `open {x:real^N | x IN ball(vec 0,&2) /\ (b:real^N->A) x IN U}`
  MP_TAC THENL
   [REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!d. abs d < e ==> (b:real^N->A)((&1 + d) % y) IN U` ASSUME_TAC THENL
   [X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(y:real^N,e) SUBSET
                 {x | x IN ball(vec 0,&2) /\ (b:real^N->A) x IN U}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(&1 + d) % y:real^N`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; dist;
                  VECTOR_ARITH `y - (&1 + d) % y:real^N = (--d) % y`] THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; REAL_ABS_NEG];
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(&1 + --(min (e / &2) (&1 / &2))) % y:real^N` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    EXISTS_TAC `(&1 + min (e / &2) (&1 / &2)) % y:real^N` THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* If two ball charts cover a Hausdorff space by their closed unit balls and *)
(* have disjoint open unit balls, the complement of one closed ball is the   *)
(* other open ball.                                                          *)

let MFDG_BALL_PAIR_COMPLEMENT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b c.
        hausdorff_space top /\
        mfd_ball_chart top atlas b /\ mfd_ball_chart top atlas c /\
        topspace top = IMAGE b (cball(vec 0,&1)) UNION IMAGE c (cball(vec 0,&1)) /\
        DISJOINT (IMAGE b (ball(vec 0,&1))) (IMAGE c (ball(vec 0,&1)))
        ==> topspace top DIFF IMAGE b (cball(vec 0,&1)) = IMAGE c (ball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(vec 0:real^N,&1) SUBSET ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (b:real^N->A) (cball(vec 0,&1)))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC
     [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; GSYM mfd_ball_chart];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF IMAGE (b:real^N->A) (cball(vec 0,&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (c:real^N->A) (ball(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM mfd_ball_chart] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ (c:real^N->A) x = c y
          ==> x = y`
  (LABEL_TAC "cinj") THENL
   [UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^N))->bool) c` THEN
    REWRITE_TAC[mfd_ball_chart] THEN MESON_TAC[MFD_PARAM_INJ];
    ALL_TAC] THEN
  UNDISCH_TAC `topspace top = IMAGE (b:real^N->A) (cball(vec 0,&1)) UNION
                              IMAGE (c:real^N->A) (cball(vec 0,&1))` THEN
  DISCH_THEN(LABEL_TAC "cover" o SYM) THEN
  (* the unit sphere of c lies in the closed ball of b *)
  SUBGOAL_THEN `!y. norm y = &1 ==> (c:real^N->A) y IN IMAGE (b:real^N->A) (cball(vec 0,&1))`
  (LABEL_TAC "i") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:real^N->A`;
                   `topspace top DIFF IMAGE (b:real^N->A) (cball(vec 0,&1))`;
                   `y:real^N`] MFDG_BALL_CHART_SPHERE_APPROX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN
      USE_THEN "cover" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_CBALL_0; REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(c:real^N->A) z IN topspace top DIFF IMAGE (b:real^N->A) (cball(vec 0,&1))` THEN
    USE_THEN "cover" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_DIFF; IN_UNION] THEN
    REWRITE_TAC[TAUT `(p \/ q) /\ ~p <=> ~p /\ q`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^N = w` SUBST_ALL_TAC THENL
     [USE_THEN "cinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the unit sphere of b misses the open ball of c *)
  SUBGOAL_THEN `!x. norm x = &1 ==> ~((b:real^N->A) x IN IMAGE (c:real^N->A) (ball(vec 0,&1)))`
  (LABEL_TAC "ii") THENL
   [X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `b:real^N->A`; `IMAGE (c:real^N->A) (ball(vec 0,&1))`;
                   `x:real^N`] MFDG_BALL_CHART_SPHERE_APPROX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `DISJOINT (IMAGE (b:real^N->A) (ball(vec 0,&1)))
                          (IMAGE (c:real^N->A) (ball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `(b:real^N->A) z` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (c:real^N->A) (cball(vec 0,&1))` MP_TAC THENL
     [UNDISCH_TAC `(p:A) IN topspace top` THEN
      USE_THEN "cover" (fun th -> REWRITE_TAC[GSYM th]) THEN
      UNDISCH_TAC `~((p:A) IN IMAGE (b:real^N->A) (cball(vec 0,&1)))` THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_BALL_0; REAL_LT_LE] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~((p:A) IN IMAGE (b:real^N->A) (cball(vec 0,&1)))` THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(p:A) IN IMAGE (c:real^N->A) (ball(vec 0,&1))` THEN
      SUBGOAL_THEN `IMAGE (c:real^N->A) (ball(vec 0,&1)) SUBSET
                    IMAGE (c:real^N->A) (cball(vec 0,&1))` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
        ALL_TAC] THEN
      USE_THEN "cover" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0; REAL_LE_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC DISJ_CASES_TAC)) THENL
       [UNDISCH_TAC `DISJOINT (IMAGE (b:real^N->A) (ball(vec 0,&1)))
                              (IMAGE (c:real^N->A) (ball(vec 0,&1)))` THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                    NOT_FORALL_THM] THEN
        EXISTS_TAC `(b:real^N->A) x` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
        USE_THEN "ii" (MP_TAC o SPEC `x:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]]]);;

(* The standard S^3. *)

let SMT_S3_HAUSDORFF = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN]);;

let SMT_S3_CONNECTED = prove
 (`connected_space (subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEAN] THEN MATCH_MP_TAC CONNECTED_SPHERE THEN
  REWRITE_TAC[DIMINDEX_4] THEN ARITH_TAC);;

let SMT_S3_N_COMPLEMENT = prove
 (`sphere(vec 0:real^4,&1) DIFF IMAGE stereo3_n_inv (cball(vec 0,&1)) =
   IMAGE stereo3_s_inv (ball(vec 0,&1))`,
  MP_TAC SMT_S3_STANDARD_BALLS THEN REWRITE_TAC[SMT_S3_STANDARD_BALLS_STATEMENT] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `stereo3_n_inv`; `stereo3_s_inv`] MFDG_BALL_PAIR_COMPLEMENT) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SMT_S3_HAUSDORFF]);;

(* M2. Twisted spheres, from M1 (hence from Smale's theorem). *)

let SMT_TWISTED_SPHERE = prove
 (`SMT_SMALE_RADIAL_STATEMENT ==> !u:A->bool. SMT_TWISTED_SPHERE_STATEMENT u`,
  DISCH_THEN(MP_TAC o SPECL [`(:A)`; `(:real^4)`] o
    MATCH_MP (INST_TYPE [`:real^4`,`:B`] SMT_GLUE_BALL)) THEN
  REWRITE_TAC[SMT_GLUE_BALL_STATEMENT; SMT_TWISTED_SPHERE_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "M1") THEN
  MP_TAC SMT_S3_STANDARD_BALLS THEN REWRITE_TAC[SMT_S3_STANDARD_BALLS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (LABEL_TAC "inv"))))) THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `b1:real^3->A`; `b2:real^3->A`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "collar")))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `b1:real^3->A`; `b2:real^3->A`] MFDG_BALL_PAIR_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,&1)) (b2:real^3->A)`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM mfd_ball_chart] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b2':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `mfd_param (subtopology euclidean (sphere(vec 0:real^4,&1)))
                  sphere3_atlas (ball(vec 0:real^3,&1)) stereo3_s_inv`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SMT_STEREO3_PARAMS; OPEN_BALL; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^4->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  USE_THEN "M1" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
    `b1:real^3->A`; `stereo3_n_inv`;
    `stereo3_s_inv o (b2':A->real^3)`; `(b2:real^3->A) o (s':real^4->real^3)`;
    `f:real^3->real^3`; `g:real^3->real^3`]) THEN
  ANTS_TAC THENL
   [ALL_TAC; REWRITE_TAC[mfd_diffeomorphic] THEN MESON_TAC[]] THEN
  ASM_REWRITE_TAC[SMT_S3_HAUSDORFF; SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  SMT_S3_N_COMPLEMENT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
      `ball(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; SPHERE3_ATLAS] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN annulus (&1) r` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((f:real^3->real^3)(inv(norm(x:real^3)) % x)) = &1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) g` THEN
    REWRITE_TAC[sphere_diffeo; IN_SPHERE_0] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(norm(x:real^3)) % x` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(x:real^3)) % (f:real^3->real^3)(inv(norm x) % x) IN
                ball(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                    REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(b1:real^3->A) x = b2(inv(norm x) % (f:real^3->real^3)(inv(norm x) % x))`
  SUBST1_TAC THENL [USE_THEN "collar" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `norm(radial_ext (f:real^3->real^3) x) = norm(x:real^3)` ASSUME_TAC
  THENL
   [ASM_REWRITE_TAC[radial_ext; NORM_MUL; REAL_ABS_NORM; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `~(radial_ext (f:real^3->real^3) x = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "inv" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `~(radial_ext (f:real^3->real^3) x = vec 0)`)]) THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&1 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The complement of a ball chart of S^3 (M4, from the weak                  *)
(* disc theorem) and sphere sums (M5).                                       *)
(* ------------------------------------------------------------------------- *)

let MFD_PARAM_IMAGE_SUBSET = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) t.
        mfd_param top atlas s e /\ t SUBSET s ==> IMAGE e t SUBSET topspace top`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^N->A) s` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; OPEN_IN_SUBSET]);;

(* Orthogonal transformations are diffeomorphisms of R^N. *)

let SMT_ORTHOGONAL_DIFFEO = prove
 (`!Q:real^N->real^N.
        orthogonal_transformation Q
        ==> ?Q'. orthogonal_transformation Q' /\
                 (!x. Q'(Q x) = x) /\ (!y. Q(Q' y) = y) /\
                 diffeomorphism_on (:real^N) (:real^N) Q Q'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Q':real^N->real^N` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  EXISTS_TAC `Q':real^N->real^N` THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q:real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    REWRITE_TAC[o_DEF; ETA_AX];
    MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`; `Q':real^N->real^N`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    REWRITE_TAC[o_DEF; ETA_AX]]);;

(* M4 from the weak disc theorem (applied to S^3 with b' the north chart). *)

let SMT_S3_BALL_COMPLEMENT = prove
 (`SMT_DISC_STATEMENT (:real^4) (:3) ==> SMT_S3_BALL_COMPLEMENT_STATEMENT`,
  REWRITE_TAC[SMT_DISC_STATEMENT; SMT_S3_BALL_COMPLEMENT_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "disc") THEN
  MP_TAC SMT_S3_STANDARD_BALLS THEN REWRITE_TAC[SMT_S3_STANDARD_BALLS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cover" o SYM)
      (CONJUNCTS_THEN2 (LABEL_TAC "disj") (LABEL_TAC "inv"))))) THEN
  X_GEN_TAC `b:real^3->real^4` THEN DISCH_TAC THEN
  USE_THEN "disc" (MP_TAC o SPECL
   [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
    `b:real^3->real^4`; `stereo3_n_inv`]) THEN
  REWRITE_TAC[SMT_S3_HAUSDORFF; SPHERE3_ATLAS; SMT_S3_CONNECTED] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^4->real^4` (X_CHOOSE_THEN `Psi:real^4->real^4`
    (X_CHOOSE_THEN `Q:real^3->real^3` (X_CHOOSE_THEN `K:real^4->bool`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))`;
                 `subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))`;
                 `Phi:real^4->real^4`; `Psi:real^4->real^4`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!p. p IN sphere(vec 0:real^4,&1) ==> (Phi:real^4->real^4) p IN sphere(vec 0,&1)) /\
    (!p. p IN sphere(vec 0:real^4,&1) ==> (Psi:real^4->real^4) p IN sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm x < &2 ==> (b:real^3->real^4) x IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `ball(vec 0:real^3,&2)`; `b:real^3->real^4`;
                   `ball(vec 0:real^3,&2)`] MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. stereo3_s_inv x IN sphere(vec 0:real^4,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `(:real^3)`; `stereo3_s_inv`; `(:real^3)`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    REWRITE_TAC[SMT_STEREO3_PARAMS; SUBSET_REFL; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm((Q:real^3->real^3) x) = norm x` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(Psi:real^4->real^4) o stereo3_s_inv`; `Q:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the new ball chart *)
    REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
      `topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))`;
      `topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))`;
      `Phi:real^4->real^4`] THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS; GSYM mfd_ball_chart] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[]];
    (* covering *)
    REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_CBALL_0; o_THM] THEN
    X_GEN_TAC `p:real^4` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(Phi:real^4->real^4) p IN
                    IMAGE stereo3_n_inv (cball(vec 0,&1)) UNION
                    IMAGE stereo3_s_inv (cball(vec 0,&1))` MP_TAC THENL
       [USE_THEN "cover" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THENL
       [DISJ1_TAC THEN
        MP_TAC(ISPEC `Q:real^3->real^3` ORTHOGONAL_TRANSFORMATION_SURJECTIVE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^3` o SPEC `z:real^3`) THEN
        EXISTS_TAC `w:real^3` THEN
        SUBGOAL_THEN `norm(w:real^3) <= &1` ASSUME_TAC THENL
         [UNDISCH_TAC `(Q:real^3->real^3) w = z` THEN
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(b:real^3->real^4) w IN sphere(vec 0,&1)` ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(Phi:real^4->real^4)(b(w:real^3)) = Phi p` MP_TAC THENL
         [SUBGOAL_THEN `norm(w:real^3) <= &3 / &2` (fun th -> ASM_SIMP_TAC[th]) THEN
          ASM_REAL_ARITH_TAC;
          DISCH_THEN(MP_TAC o AP_TERM `Psi:real^4->real^4`) THEN ASM_SIMP_TAC[] THEN
          MESON_TAC[]];
        DISJ2_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(Phi:real^4->real^4) p = stereo3_s_inv z` THEN
        DISCH_THEN(MP_TAC o AP_TERM `Psi:real^4->real^4`) THEN ASM_SIMP_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    (* disjoint open cores *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_BALL_0;
                o_THM] THEN
    X_GEN_TAC `p:real^4` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "disj" (MP_TAC o SPEC `stereo3_s_inv y` o
      REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_BALL_0]) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `(Q:real^3->real^3) x` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(Phi:real^4->real^4) p = stereo3_n_inv(Q(x:real^3))` MP_TAC THENL
       [SUBGOAL_THEN `norm(x:real^3) <= &3 / &2` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `p:real^4 = b(x:real^3)` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `p:real^4 = Psi(stereo3_s_inv y)` THEN
        DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    (* the inversion collar *)
    REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(b:real^3->real^4) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Phi:real^4->real^4)(b(x:real^3)) =
                  stereo3_s_inv(inv(norm x pow 2) % Q x)` MP_TAC THENL
     [SUBGOAL_THEN `norm(x:real^3) <= &3 / &2` (fun th -> ASM_SIMP_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~((Q:real^3->real^3) x = vec 0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "inv" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `~((Q:real^3->real^3) x = vec 0)`)]) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `Psi:real^4->real^4`) THEN ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sphere sums (M5).                                                         *)
(* ------------------------------------------------------------------------- *)

let OPEN_ANNULUS = prove
 (`!r1 r2. open(annulus r1 r2:real^N->bool)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `annulus r1 r2:real^N->bool = ball(vec 0,r2) DIFF cball(vec 0,r1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[annulus; EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]]);;

(* The inversion x |-> x / |x|^2 commutes with orthogonal maps. *)

let SMT_INVERSION_ORTHOGONAL = prove
 (`!Q:real^N->real^N x.
        orthogonal_transformation Q /\ ~(x = vec 0)
        ==> norm(inv(norm x pow 2) % x) = inv(norm x) /\
            inv(norm(inv(norm x pow 2) % x) pow 2) % Q(inv(norm x pow 2) % x) = Q x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(x:real^N) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv(norm x pow 2) % (x:real^N)) = inv(norm x)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `~(norm(x:real^N) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL
    (MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR th)]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(norm(x:real^N) = &0)` THEN CONV_TAC REAL_FIELD);;

(* An open set X2 parametrized by the unit ball, agreeing with a neck chart  *)
(* e on the inner collar, together with the neck is a ball chart b.          *)

let SMT_CAP_BALL_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e X2 psi psi'.
        smooth_manifold_atlas top atlas /\
        mfd_neck_chart top atlas e /\
        DISJOINT X2 (IMAGE e (annulus (&1) (&2))) /\
        DISJOINT X2 (IMAGE e (sphere(vec 0,&1))) /\
        mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&1))
                   top atlas X2 psi psi' /\
        (!x. x IN annulus (&2 / &3) (&1) ==> psi x = e x)
        ==> ?b. mfd_ball_chart top atlas b /\
                (!x. x IN annulus (&2 / &3) (&2) ==> b x = e x) /\
                (!x. x IN ball(vec 0,&1) ==> b x = psi x) /\
                IMAGE b (ball(vec 0,&1)) = X2 /\
                IMAGE b (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pe")))))) THEN
  SUBGOAL_THEN `mfd_param top atlas (annulus (&2 / &3) (&2)) (e:real^3->A)` MP_TAC
  THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; GSYM mfd_neck_chart] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `ball(vec 0:real^3,&1)`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `X2:A->bool`;
                 `psi:real^3->A`; `psi':A->real^3`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN annulus (&2 / &3) (&2)
        ==> (if norm x < &1 then (psi:real^3->A) x else e x) = e x`
  (LABEL_TAC "he") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "pe" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&2 / &3) (&2)` THEN
    UNDISCH_TAC `norm(x:real^3) < &1` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&2))
               top (atlas:((A->bool)#(A->real^3))->bool)
               (X2 UNION IMAGE e (annulus (&2 / &3) (&2)))
               (\x. if norm x < &1 then (psi:real^3->A) x else e x)
               (\p. if p IN X2 then (psi':A->real^3) p else e' p)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(vec 0:real^3,&2) = ball(vec 0,&1) UNION annulus (&2 / &3) (&2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIFFEO_GLUE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`psi:real^3->A`; `psi':A->real^3`; `e:real^3->A`; `e':A->real^3`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[IN_BALL_0];
      SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `norm(x:real^3) < &1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
         [UNDISCH_TAC `DISJOINT (X2:A->bool) (IMAGE (e:real^3->A) (annulus (&1) (&2)))` THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
          EXISTS_TAC `(e:real^3->A) x` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          UNDISCH_TAC `(x:real^3) IN annulus (&2 / &3) (&2)` THEN
          UNDISCH_TAC `&1 < norm(x:real^3)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          UNDISCH_TAC `DISJOINT (X2:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,&1)))` THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
          EXISTS_TAC `(e:real^3->A) x` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          UNDISCH_TAC `&1 = norm(x:real^3)` THEN
          REWRITE_TAC[IN_SPHERE_0] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(psi':A->real^3)(e x) = x /\ (e':A->real^3)(e x) = x`
       (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(e:real^3->A) x = psi x` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "pe" MATCH_MP_TAC THEN
          UNDISCH_TAC `(x:real^3) IN annulus (&2 / &3) (&2)` THEN
          UNDISCH_TAC `norm(x:real^3) < &1` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (find_term ((=) `psi':A->real^3`)) (concl th) &&
            can (find_term ((=) `ball(vec 0:real^3,&1)`)) (concl th) &&
            is_forall (concl th))) THEN
          ASM_REWRITE_TAC[IN_BALL_0]];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `ball(vec 0:real^3,&2)`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`;
                 `X2 UNION IMAGE (e:real^3->A) (annulus (&2 / &3) (&2))`;
                 `\x. if norm x < &1 then (psi:real^3->A) x else e x`;
                 `\p. if p IN X2 then (psi':A->real^3) p else e' p`]
                MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. if norm x < &1 then (psi:real^3->A) x else e x` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart; mfd_param] THEN
    EXISTS_TAC `\p. if p IN X2 then (psi':A->real^3) p else e' p` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN USE_THEN "he" ACCEPT_TAC;
    SIMP_TAC[IN_BALL_0];
    SUBGOAL_THEN `IMAGE (\x. if norm x < &1 then (psi:real^3->A) x else e x)
                        (ball(vec 0,&1)) = IMAGE psi (ball(vec 0,&1))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = g x) ==> IMAGE (f:real^3->A) s = IMAGE g s`) THEN
      SIMP_TAC[IN_BALL_0];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE (f:real^3->A) s = IMAGE g s`) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "he" (MP_TAC o SPEC `x:real^3`) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]]);;

(* The inner side of a sphere sum whose capped inner side is S^3: by M4 it   *)
(* is parametrized by the open unit ball, by a map equal to the neck chart   *)
(* on an inner collar.                                                       *)

let SMT_SPHERE_SUM_INNER = prove
 (`SMT_S3_BALL_COMPLEMENT_STATEMENT
   ==> !topX (atlasX:((A->bool)#(A->real^3))->bool)
         topZ (atlasZ:((C->bool)#(C->real^3))->bool) e X2 cZ FZ GZ.
         smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topZ atlasZ /\
         mfd_ball_chart topZ atlasZ cZ /\
         mfd_diffeo topX atlasX X2
                    topZ atlasZ (topspace topZ DIFF IMAGE cZ (cball(vec 0,&1)))
                    FZ GZ /\
         IMAGE e (annulus (&1 / &2) (&1)) SUBSET X2 /\
         (!x. x IN annulus (&1 / &2) (&1) ==> FZ(e x) = cZ(inv(norm x pow 2) % x)) /\
         mfd_diffeomorphic topZ atlasZ
           (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
         ==> ?psi psi'. mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&1))
                                   topX atlasX X2 psi psi' /\
                        (!x. x IN annulus (&2 / &3) (&1) ==> psi x = e x)`,
  REWRITE_TAC[SMT_S3_BALL_COMPLEMENT_STATEMENT] THEN DISCH_THEN(LABEL_TAC "M4") THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "collZ") MP_TAC)))))) THEN
  REWRITE_TAC[mfd_diffeomorphic; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `Th:C->real^4` (X_CHOOSE_THEN `Th':real^4->C`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `X2:A->bool`; `topZ:C topology`;
                 `atlasZ:((C->bool)#(C->real^3))->bool`;
                 `topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1))`;
                 `FZ:A->C`; `GZ:C->A`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (cZ:real^3->C) (ball(vec 0,&2)) SUBSET topspace topZ`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC
     [`atlasZ:((C->bool)#(C->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball_chart (subtopology euclidean (sphere(vec 0:real^4,&1)))
                  sphere3_atlas ((Th:C->real^4) o (cZ:real^3->C))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`topZ:C topology`; `atlasZ:((C->bool)#(C->real^3))->bool`;
      `topspace topZ:C->bool`; `sphere(vec 0:real^4,&1)`; `Th':real^4->C`] THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS; GSYM mfd_ball_chart];
    ALL_TAC] THEN
  USE_THEN "M4" (fun th -> MP_TAC(MATCH_MP th (ASSUME
   `mfd_ball_chart (subtopology euclidean (sphere(vec 0:real^4,&1)))
                   sphere3_atlas ((Th:C->real^4) o (cZ:real^3->C))`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->real^4` (X_CHOOSE_THEN `Q:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "coll3"))))))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `(Th:C->real^4) o (cZ:real^3->C)`; `c':real^3->real^4`]
                MFDG_BALL_PAIR_COMPLEMENT) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SMT_S3_HAUSDORFF]; DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (cZ:real^3->C) (cball(vec 0,&1)) SUBSET topspace topZ`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (cZ:real^3->C) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Th:C->real^4) (topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1))) =
                IMAGE (c':real^3->real^4) (ball(vec 0,&1))` ASSUME_TAC THENL
   [UNDISCH_TAC `sphere(vec 0:real^4,&1) DIFF
                 IMAGE ((Th:C->real^4) o (cZ:real^3->C)) (cball(vec 0,&1)) =
                 IMAGE (c':real^3->real^4) (ball(vec 0,&1))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (cZ:real^3->C) (cball(vec 0,&1)) SUBSET topspace topZ` THEN
    UNDISCH_TAC `!x. x IN topspace topZ ==> (Th':real^4->C)((Th:C->real^4) x) = x` THEN
    UNDISCH_TAC `IMAGE (Th:C->real^4) (topspace topZ) = sphere(vec 0,&1)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* c' on the unit ball, Q on the unit ball *)
  SUBGOAL_THEN `mfd_param (subtopology euclidean (sphere(vec 0:real^4,&1)))
                  sphere3_atlas (ball(vec 0:real^3,&1)) c'` MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM mfd_ball_chart] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c'':real^4->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Q':real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP SMT_ORTHOGONAL_DIFFEO) THEN
  MP_TAC(ISPECL [`Q:real^3->real^3`; `Q':real^3->real^3`; `&1`]
    SMT_NORM_PRESERVING_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; STRIP_TAC] THEN
  (* the composite parametrization of X2 *)
  SUBGOAL_THEN
   `mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&1))
               (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas
               (IMAGE (c':real^3->real^4) (ball(vec 0,&1)))
               ((c':real^3->real^4) o (Q:real^3->real^3))
               ((Q':real^3->real^3) o (c'':real^4->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
      `ball(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; SPHERE3_ATLAS; MFD_DIFFEO_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas
               (IMAGE (c':real^3->real^4) (ball(vec 0,&1)))
               topZ (atlasZ:((C->bool)#(C->real^3))->bool)
               (topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1)))
               (Th':real^4->C) (Th:C->real^4)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1)) =
                  IMAGE (Th':real^4->C) (IMAGE (c':real^3->real^4) (ball(vec 0,&1)))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (Th:C->real^4) (topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1))) =
                   IMAGE (c':real^3->real^4) (ball(vec 0,&1))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `!x. x IN topspace topZ ==> (Th':real^4->C)((Th:C->real^4) x) = x` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^4,&1)`; `topspace topZ:C->bool`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `IMAGE (c':real^3->real^4) (ball(vec 0,&1))`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo euclidean (open_set_atlas (:real^3)) (ball(vec 0,&1))
               topZ (atlasZ:((C->bool)#(C->real^3))->bool)
               (topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1)))
               ((Th':real^4->C) o (c':real^3->real^4) o (Q:real^3->real^3))
               (((Q':real^3->real^3) o (c'':real^4->real^3)) o (Th:C->real^4))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^4`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
      `IMAGE (c':real^3->real^4) (ball(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; SPHERE3_ATLAS];
    ALL_TAC] THEN
  (* the collar identity *)
  SUBGOAL_THEN
   `!x. x IN annulus (&2 / &3) (&1)
        ==> ((GZ:C->A) o (Th':real^4->C) o (c':real^3->real^4) o (Q:real^3->real^3)) x =
            (e:real^3->A) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`Q:real^3->real^3`; `x:real^3`] SMT_INVERSION_ORTHOGONAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c':real^3->real^4)(Q(x:real^3)) =
                  (Th:C->real^4)((cZ:real^3->C)(inv(norm x pow 2) % x))`
    SUBST1_TAC THENL
     [USE_THEN "coll3" (MP_TAC o SPEC `inv(norm(x:real^3) pow 2) % x`) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
          MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `&3 / &2 = inv(&2 / &3)` SUBST1_TAC THENL
           [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(cZ:real^3->C)(inv(norm x pow 2) % x) = FZ((e:real^3->A) x)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "collZ" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->A) x IN X2` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1)) SUBSET X2` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(FZ:A->C)(e(x:real^3)) IN topspace topZ` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (FZ:A->C) X2 SUBSET
                   topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1))` THEN
      UNDISCH_TAC `(e:real^3->A) x IN X2` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(GZ:C->A) o (Th':real^4->C) o (c':real^3->real^4) o (Q:real^3->real^3)`;
    `(((Q':real^3->real^3) o (c'':real^4->real^3)) o (Th:C->real^4)) o (FZ:A->C)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`; `:3`,`:M`; `:C`,`:B`; `:3`,`:N`;
                          `:A`,`:C`; `:3`,`:P`] MFD_DIFFEO_COMPOSE) THEN
  MAP_EVERY EXISTS_TAC
   [`topZ:C topology`; `atlasZ:((C->bool)#(C->real^3))->bool`;
    `topspace topZ DIFF IMAGE (cZ:real^3->C) (cball(vec 0,&1))`] THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
  MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

(* M5 from M4: the inner side together with the neck sphere is a closed      *)
(* ball b(cball(0,1)) of X with b = e near the sphere, and re-capping with   *)
(* the identity collar (SMT_GLUE_BALL_GEN, h = identity) gives X = Y.        *)

let SMT_SPHERE_SUM = prove
 (`SMT_S3_BALL_COMPLEMENT_STATEMENT
   ==> !u:A->bool v:B->bool w:C->bool. SMT_SPHERE_SUM_STATEMENT u v w`,
  DISCH_THEN(LABEL_TAC "inner" o MATCH_MP SMT_SPHERE_SUM_INNER) THEN
  REWRITE_TAC[SMT_SPHERE_SUM_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
    `X1:A->bool`; `X2:A->bool`;
    `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`; `cY:real^3->B`;
    `FY:A->B`; `GY:B->A`;
    `topZ:C topology`; `atlasZ:((C->bool)#(C->real^3))->bool`; `cZ:real^3->C`;
    `FZ:A->C`; `GZ:C->A`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `topspace topX = X1 UNION X2 UNION IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  USE_THEN "inner" (MP_TAC o SPECL
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `topZ:C topology`; `atlasZ:((C->bool)#(C->real^3))->bool`;
    `e:real^3->A`; `X2:A->bool`; `cZ:real^3->C`; `FZ:A->C`; `GZ:C->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->A` (X_CHOOSE_THEN `psi':A->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `e:real^3->A`; `X2:A->bool`; `psi:real^3->A`; `psi':A->real^3`]
                SMT_CAP_BALL_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1) (&2)) SUBSET X1` THEN
    UNDISCH_TAC `DISJOINT (X1:A->bool) X2` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "be") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  SUBGOAL_THEN `topspace topX DIFF IMAGE (b:real^3->A) (cball(vec 0,&1)) = X1`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `X1 UNION X2 UNION IMAGE (e:real^3->A) (sphere(vec 0,&1)) =
                 topspace topX` THEN
    UNDISCH_TAC `DISJOINT (X1:A->bool) X2` THEN
    UNDISCH_TAC `DISJOINT (X1:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,&1)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
                 `b:real^3->A`; `cY:real^3->B`; `FY:A->B`; `GY:B->A`;
                 `\x:real^3. x`; `\x:real^3. x`; `&2`] SMT_GLUE_BALL_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_UNIV; REAL_ARITH `&1 < &2`] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(b:real^3->A) x = e x` SUBST1_TAC THENL
     [USE_THEN "be" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    REWRITE_TAC[mfd_diffeomorphic] THEN MESON_TAC[]]);;

