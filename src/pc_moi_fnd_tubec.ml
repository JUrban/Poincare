(* ========================================================================= *)
(* pc_moi_fnd_tubec: foundations of the Moise PL core, the solid tori of   *)
(* the graph tube.  Main theorem GRAPH_TUBE_TRIANGLE_SOLID_TORUS (the       *)
(* statement term MOI_FND_SOLID_TORUS_TRIANGLE, Moise p.240): for a         *)
(* 2-simplex s of t with edges in the graph, the union N_s of the dual      *)
(* cells of its vertices is a solid torus with core Bd s.  The polygon case *)
(* POLYGON_NBHD_SOLID_TORUS is proved in pc_moi_fnd_tubep.                  *)
(* Orientation of N_s: one 3-simplex sigma1 of t with the 2-simplex s as a  *)
(* face gives the convex wedge Omega = conv(s, barycentre sigma1); every    *)
(* cell of the decomposition of N_s is inside or outside the one set Omega, *)
(* so the cyclic gluing of the three dual cells cannot flip.                 *)
(* Loads pc_moi_s34_outer (SPHERE_SPLIT, RADIAL_CIRCLE, CIRCLE_ARC,         *)
(* CONE_ARC, CELL_SPHERE, CELL_PULLBACK, SPHERE_PIECE).                      *)
(*                                                                           *)
(* Shared tools (THETA3, radial tools, 2-d tools, TRIPLE, product assembly, *)
(* models, TORUS_SPINE) are in pc_moi_fnd_tubecm.                          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_tubecm.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_fnd_rnsc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The orientation certificate exists.  A vertex of a complex               *)
(* whose union is a PL 1-sphere lies in a bigger simplex; hence (vertex     *)
(* links of the graph are PL 2-spheres, MOI_FTA_S2LINK) the 2-simplex s is  *)
(* a face of a 3-simplex conv{a,b,c,x} of t.                                *)
(* ========================================================================= *)

let MOI_FTC_PL_SPHERE1_NOT_SING = prove
 (`!K:real^N->bool. pl_sphere 1 K ==> ~(?z. K = {z})`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!w:real^N. w IN {p,q,r} ==> w IN relative_frontier k`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC EXTREME_POINT_IN_RELATIVE_FRONTIER THEN CONJ_TAC THENL
     [UNDISCH_TAC `k = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `V:real^N->bool`] HULL_SUBSET) THEN
      UNDISCH_TAC `k = convex hull (V:real^N->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier (k:real^N->bool),{z:real^N})
                 (f:real^N->real^N,g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N) IN relative_frontier k /\ (q:real^N) IN relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) p = z /\ f q = z` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) ((f:real^N->real^N) p) = p /\ g (f q) = q`
  MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[]]);;

(* A non-isolated point of the union of an lf complex lies in a simplex     *)
(* other than its singleton.                                                 *)

let MOI_FTC_NONISOLATED_SIMPLEX = prove
 (`!(L:(real^N->bool)->bool) c.
     lf_simplicial_complex L /\ c IN UNIONS L /\ c limit_point_of UNIONS L
     ==> ?r. r IN L /\ c IN r /\ ~(r = {c})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `c:real^N` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  ABBREV_TAC `Q = UNIONS {r | r IN L /\ ~(r INTER u = {}) /\ ~(r = {c:real^N})}` THEN
  SUBGOAL_THEN `closed (Q:real^N->bool) /\ ~((c:real^N) IN Q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{r | r IN L /\ ~(r INTER u = {}:real^N->bool)}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o
          GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(c:real^N) limit_point_of UNIONS L` THEN REWRITE_TAC[limit_point_of] THEN
  DISCH_THEN(MP_TAC o SPEC `u DIFF Q:real^N->bool`) THEN
  ASM_SIMP_TAC[OPEN_DIFF; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((y:real^N) IN Q)` THEN EXPAND_TAC "Q" THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `(y:real^N) IN {c}` THEN
  ASM_REWRITE_TAC[IN_SING]);;

(* Small simplex facts. *)

let MOI_FTC_SIMPLEX2_VERTS = prove
 (`!s:real^N->bool.
     &2 simplex s
     ==> ?a b c. ~(a = b) /\ ~(a = c) /\ ~(b = c) /\ ~affine_dependent {a,b,c} /\
                 s = convex hull {a,b,c}`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FTC_HULL_FACE = prove
 (`!V W:real^N->bool.
     ~affine_dependent V /\ W SUBSET V ==> convex hull W face_of convex hull V`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FTC_NOT_IN_HULL = prove
 (`!(a:real^N) W.
     ~affine_dependent (a INSERT W) /\ ~(a IN W) ==> ~(a IN convex hull W)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~affine_dependent ((a:real^N) INSERT W)` THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `a:real^N` THEN
  REWRITE_TAC[IN_INSERT] THEN
  SUBGOAL_THEN `((a:real^N) INSERT W) DELETE a = W` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]);;

let MOI_FTC_VERTEX_OF = prove
 (`!(t:(real^N->bool)->bool) r v.
     lf_simplicial_complex t /\ r IN t /\ {v} IN t /\ v IN r
     ==> v extreme_point_of r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[moi_bar_complex] THEN
  ASM_MESON_TAC[lf_simplicial_complex]);;

(* The 3-simplex: s = conv{a,b,c} is a face of conv{a,b,c,x} IN t. *)

let MOI_FTC_TET = prove
 (`!(t:(real^N->bool)->bool) l s.
     graph_in_complex t l /\ s IN t /\ aff_dim s = &2 /\
     (!e. e face_of s /\ aff_dim e = &1 ==> e IN l)
     ==> ?a b c x. ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
                   ~(x = a) /\ ~(x = b) /\ ~(x = c) /\
                   ~affine_dependent {a,b,c,x} /\
                   s = convex hull {a,b,c} /\ convex hull {a,b,c,x} IN t /\
                   segment[a,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l /\
                   {a} IN l /\ {b} IN l /\ {c} IN l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `&2 simplex (s:real^N->bool)` MP_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FTC_SIMPLEX2_VERTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  (* the edges and vertices of s *)
  SUBGOAL_THEN
   `!p q:real^N. p IN {a,b,c} /\ q IN {a,b,c} /\ ~(p = q) ==> segment[p,q] IN l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_HULL_FACE THEN ASM SET_TAC[];
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      SUBGOAL_THEN `~affine_dependent {p:real^N,q}` ASSUME_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `{a:real^N,b,c}` THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; CARD_CLAUSES; FINITE_INSERT;
                   FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[ARITH_RULE `SUC(SUC 0) = 2`] THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN {a,b,c} ==> {p} IN l` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?q:real^N. q IN {a,b,c} /\ ~(p = q)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `simplicial_subcomplex l (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    EXISTS_TAC `segment[p:real^N,q]` THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  (* the second link *)
  ABBREV_TAC `L2 = simplicial_link (simplicial_link t a) (b:real^N)` THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (L2:(real^N->bool)->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "L2" THEN MATCH_MP_TAC MOI_FTA_S2LINK THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET; IN_INSERT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; IN_INSERT];
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_INSERT];
        ASM_REWRITE_TAC[IN_SING];
        EXISTS_TAC `segment[a:real^N,b]` THEN
        ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT] THEN
        ASM_MESON_TAC[SUBSET; IN_INSERT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (L2:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L2" THEN ASM_MESON_TAC[MOI_FTA_LINK_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `{c:real^N} IN L2` ASSUME_TAC THENL
   [EXPAND_TAC "L2" THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_INSERT];
      ASM_REWRITE_TAC[IN_SING];
      EXISTS_TAC `segment[a:real^N,c]` THEN
      ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT] THEN
      ASM_MESON_TAC[SUBSET; IN_INSERT];
      ASM_REWRITE_TAC[IN_SING];
      EXISTS_TAC `segment[b:real^N,c]` THEN
      ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET; IN_INSERT];
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_FTC_NOT_IN_HULL THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
        EXISTS_TAC `convex hull {a:real^N,b,c}` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [MESON_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_FTC_HULL_FACE THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L2:(real^N->bool)->bool`; `c:real^N`] MOI_FTC_NONISOLATED_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:real^N) IN UNIONS L2` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{c:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
    ASM_SIMP_TAC[MOI_S4O_SPHERE1_CONNECTED; MOI_FTC_PL_SPHERE1_NOT_SING];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(r:real^N->bool) IN L2` THEN EXPAND_TAC "L2" THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r1:real^N->bool`
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r1 /\ r1 SUBSET r2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?W. ~affine_dependent W /\ r = convex hull (W:real^N->bool)`
  (X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[simplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `?W2. ~affine_dependent W2 /\ r2 = convex hull (W2:real^N->bool)`
  (X_CHOOSE_THEN `W2:real^N->bool` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `?n. n simplex (r2:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[simplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N) IN W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`; `c:real^N`]
      MOI_FTC_VERTEX_OF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_INSERT]; ALL_TAC] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN W /\ ~(x = c)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!W c:real^N. c IN W /\ ~(W = {c}) ==> ?x. x IN W /\ ~(x = c)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(r = {c:real^N})` THEN ASM_REWRITE_TAC[CONVEX_HULL_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN r /\ {x} IN t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N,b,c,x} SUBSET W2` ASSUME_TAC THENL
   [SUBGOAL_THEN `!p:real^N. p IN r2 /\ {p} IN t ==> p IN W2` MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r2:real^N->bool`; `p:real^N`]
        MOI_FTC_VERTEX_OF) THEN
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) = a) /\ ~(x = b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `~((a:real^N) IN r1)` THEN UNDISCH_TAC `(r:real^N->bool) SUBSET r1` THEN
      UNDISCH_TAC `(x:real^N) IN r` THEN SET_TAC[];
      UNDISCH_TAC `~((b:real^N) IN r)` THEN UNDISCH_TAC `(x:real^N) IN r` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,c,x} /\ convex hull {a:real^N,b,c,x} IN t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `W2:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o
        GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      EXISTS_TAC `r2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FTC_HULL_FACE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l /\
    {a:real^N} IN l /\ {b} IN l /\ {c} IN l`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Simplicial facts in the first barycentric subdivision near                *)
(* the triangle s = conv{a,b,c} and the 3-simplex sigma1 = conv{a,b,c,x}    *)
(* (STAR_CHAIN and TRIPLE are in the shared file pc_moi_fnd_tubecm).        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Explicit convex geometry of the triangle s = conv{a,b,c} and the wedge    *)
(* Omega = conv{a,b,c,b1}, b1 the barycentre of conv{a,b,c,x}.               *)
(* ------------------------------------------------------------------------- *)

let MOI_FTC_IN_HULL4 = prove
 (`!a b c d x:real^N.
     x IN convex hull {a,b,c,d} <=>
     ?u1 u2 u3 u4. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\
                   u1 + u2 + u3 + u4 = &1 /\
                   x = u1 % a + u2 % b + u3 % c + u4 % d`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONVEX_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[CONVEX_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_IN_HULL3 = prove
 (`!a b c x:real^N.
     x IN convex hull {a,b,c} <=>
     ?u1 u2 u3. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ u1 + u2 + u3 = &1 /\
                x = u1 % a + u2 % b + u3 % c`,
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_BARY3 = prove
 (`!a b c:real^N.
     ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> simplex_barycentre (convex hull {a,b,c}) = inv(&3) % (a + b + c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_BAR_SIMPLEX_BARYCENTRE_HULL th]) THEN
  REWRITE_TAC[barycentre; FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {a:real^N,b,c} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_FTC_BARY4 = prove
 (`!a b c d:real^N.
     ~affine_dependent {a,b,c,d} /\ ~(a = b) /\ ~(a = c) /\ ~(a = d) /\
     ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> simplex_barycentre (convex hull {a,b,c,d}) = inv(&4) % (a + b + c + d)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_BAR_SIMPLEX_BARYCENTRE_HULL th]) THEN
  REWRITE_TAC[barycentre; FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {a:real^N,b,c,d} = 4` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* One ordering of the coordinates: the barycentric chamber. *)

let MOI_FTC_ORD4 = prove
 (`!a b c d:real^N p q r s.
     q <= p /\ r <= q /\ &0 <= r /\ &0 <= s /\ p + q + r + s = &1
     ==> p % a + q % b + r % c + s % d IN
         convex hull {a, midpoint(a,b), inv(&3) % (a + b + c), d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p % a + q % b + r % c + s % d:real^N =
    (p - q) % a + (&2 * (q - r)) % midpoint(a,b) +
    (&3 * r) % (inv(&3) % (a + b + c)) + s % d`
  SUBST1_TAC THENL [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FM3_IN_CONVEX_HULL_4 THEN ASM_REAL_ARITH_TAC);;

let MOI_FTC_ORD3 = prove
 (`!a b c:real^N p q r.
     q <= p /\ r <= q /\ &0 <= r /\ p + q + r = &1
     ==> p % a + q % b + r % c IN
         convex hull {a, midpoint(a,b), inv(&3) % (a + b + c)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p % a + q % b + r % c:real^N =
    (p - q) % a + (&2 * (q - r)) % midpoint(a,b) + (&3 * r) % (inv(&3) % (a + b + c))`
  SUBST1_TAC THENL [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOI_FTC_IN_HULL3] THEN
  MAP_EVERY EXISTS_TAC [`p - q:real`; `&2 * (q - r)`; `&3 * r`] THEN
  REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_FTC_ORD2 = prove
 (`!a b d:real^N p q s.
     q <= p /\ &0 <= q /\ &0 <= s /\ p + q + s = &1
     ==> p % a + q % b + s % d IN convex hull {a, midpoint(a,b), d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p % a + q % b + s % d:real^N = (p - q) % a + (&2 * q) % midpoint(a,b) + s % d`
  SUBST1_TAC THENL [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOI_FTC_IN_HULL3] THEN
  MAP_EVERY EXISTS_TAC [`p - q:real`; `&2 * q`; `s:real`] THEN
  REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chains and closed stars.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FTC_FACE_IN = prove
 (`!(t:(real^N->bool)->bool) V W.
     lf_simplicial_complex t /\ convex hull V IN t /\ ~affine_dependent V /\ W SUBSET V
     ==> convex hull W IN t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  EXISTS_TAC `convex hull V:real^N->bool` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FTC_STAR_CHAIN_SUB = prove
 (`!(t:(real^N->bool)->bool) v h h'.
     lf_simplicial_complex t /\ {v} IN t /\ moi_bar_chain t h /\
     (!c. c IN h /\ v IN c ==> c IN h')
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER
         convex hull (IMAGE simplex_barycentre h) SUBSET
         convex hull (IMAGE simplex_barycentre h')`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FTC_STAR_CHAIN] THEN
  MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]);;

let MOI_FTC_STAR_CHAIN_IN = prove
 (`!(t:(real^N->bool)->bool) v h.
     moi_bar_chain t h /\ {v} IN h
     ==> convex hull (IMAGE simplex_barycentre h) SUBSET
         UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
  REWRITE_TAC[IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN CONJ_TAC THENL
   [EXISTS_TAC `h:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]]);;

(* The data of one vertex v of s = conv{v,u,u'} with the 3-simplex          *)
(* conv{v,u,u',x} of t; symmetric in v, u, u' up to the order in the sets.  *)

let moi_ftc_blk = new_definition
 `moi_ftc_blk (t:(real^N->bool)->bool) v u u' x <=>
    lf_simplicial_complex t /\ convex hull {v,u,u',x} IN t /\
    ~affine_dependent {v,u,u',x} /\
    ~(v = u) /\ ~(v = u') /\ ~(v = x) /\ ~(u = u') /\ ~(u = x) /\ ~(u' = x)`;;

let MOI_FTC_BLK_FACTS = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> {v} IN t /\ {u} IN t /\ {u'} IN t /\ segment[v,u] IN t /\
         segment[v,u'] IN t /\ segment[u,u'] IN t /\ convex hull {v,u,u'} IN t /\
         ~affine_dependent {v,u,u'} /\
         simplex_barycentre (convex hull {v,u,u'}) = inv(&3) % (v + u + u') /\
         simplex_barycentre (convex hull {v,u,u',x}) = inv(&4) % (v + u + u' + x) /\
         moi_bar_chain t {{v}, segment[v,u], convex hull {v,u,u'}, convex hull {v,u,u',x}} /\
         moi_bar_chain t {{v}, segment[v,u'], convex hull {v,u,u'}, convex hull {v,u,u',x}} /\
         moi_bar_chain t {{u}, segment[u,v], convex hull {v,u,u'}, convex hull {v,u,u',x}} /\
         moi_bar_chain t {{u}, segment[u,u'], convex hull {v,u,u'}, convex hull {v,u,u',x}} /\
         moi_bar_chain t {{u'}, segment[u',v], convex hull {v,u,u'}, convex hull {v,u,u',x}} /\
         moi_bar_chain t {{u'}, segment[u',u], convex hull {v,u,u'}, convex hull {v,u,u',x}}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_blk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,u,u'}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,u,u',x}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!W. W SUBSET {v:real^N,u,u',x} ==> convex hull W IN t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_FACE_IN THEN
    EXISTS_TAC `{v:real^N,u,u',x}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q:real^N. p IN {v,u,u',x} /\ q IN {v,u,u',x}
                 ==> {p} IN t /\ segment[p,q] IN t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `{p:real^N} = convex hull {p}` SUBST1_TAC THENL
       [REWRITE_TAC[CONVEX_HULL_SING]; ALL_TAC];
      REWRITE_TAC[SEGMENT_CONVEX_HULL]] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v:real^N,u,u'} IN t /\ convex hull {v,u,u'} = convex hull {u,v,u'} /\
    convex hull {v,u,u'} = convex hull {u',v,u}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r:real^N. {p,q,r} = {v,u,u'} /\ ~(p = q)
       ==> moi_bar_chain t {{p}, segment[p,q], convex hull {v,u,u'},
                            convex hull {v,u,u',x}}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_bar_chain] THEN
    SUBGOAL_THEN `(p:real^N) IN {v,u,u',x} /\ q IN {v,u,u',x}` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{p:real^N} SUBSET segment[p,q] /\ segment[p,q] SUBSET convex hull {v,u,u'} /\
      convex hull {v,u,u'} SUBSET convex hull {v:real^N,u,u',x}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT; SEGMENT_CONVEX_HULL] THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(segment[p:real^N,q] = {}) /\ ~(convex hull {v:real^N,u,u'} = {}) /\
                  ~(convex hull {v:real^N,u,u',x} = {})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM_MESON_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FTC_BARY3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FTC_BARY4 THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `u:real^N`; `u':real^N`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `u':real^N`; `u:real^N`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`; `u':real^N`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `u':real^N`; `v:real^N`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `v:real^N`; `u:real^N`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `u:real^N`; `v:real^N`])] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The barycentric decompositions of the wedge, the triangle, the fin and    *)
(* the boundary of the triangle into hulls of chains.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FTC_ORDER3 = prove
 (`!p q r:real.
     (q <= p /\ r <= q) \/ (r <= p /\ q <= r) \/ (p <= q /\ r <= p) \/
     (r <= q /\ p <= r) \/ (p <= r /\ q <= p) \/ (q <= r /\ p <= q)`,
  REAL_ARITH_TAC);;

let MOI_FTC_ORD4E = prove
 (`!a b c d e:real^N p q r s.
     &3 % e = a + b + c /\
     q <= p /\ r <= q /\ &0 <= r /\ &0 <= s /\ p + q + r + s = &1
     ==> p % a + q % b + r % c + s % d IN convex hull {a, midpoint(a,b), e, d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e:real^N = inv(&3) % (a + b + c)` SUBST1_TAC THENL
   [UNDISCH_TAC `&3 % e:real^N = a + b + c` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    MATCH_MP_TAC MOI_FTC_ORD4 THEN ASM_REWRITE_TAC[]]);;

let MOI_FTC_ORD3E = prove
 (`!a b c e:real^N p q r.
     &3 % e = a + b + c /\ q <= p /\ r <= q /\ &0 <= r /\ p + q + r = &1
     ==> p % a + q % b + r % c IN convex hull {a, midpoint(a,b), e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e:real^N = inv(&3) % (a + b + c)` SUBST1_TAC THENL
   [UNDISCH_TAC `&3 % e:real^N = a + b + c` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    MATCH_MP_TAC MOI_FTC_ORD3 THEN ASM_REWRITE_TAC[]]);;

let MOI_FTC_DEC_OM = prove
 (`!a b c d e:real^N.
     &3 % e = a + b + c
     ==> convex hull {a,b,c,d} =
         convex hull {a,midpoint(a,b),e,d} UNION convex hull {a,midpoint(a,c),e,d} UNION
         convex hull {b,midpoint(b,a),e,d} UNION convex hull {b,midpoint(b,c),e,d} UNION
         convex hull {c,midpoint(c,a),e,d} UNION convex hull {c,midpoint(c,b),e,d}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FTC_IN_HULL4] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `r:real`
      (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))))) THEN
    REWRITE_TAC[IN_UNION] THEN
    MP_TAC(SPECL [`p:real`; `q:real`; `r:real`] MOI_FTC_ORDER3) THEN STRIP_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_FTC_ORD4E THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `c:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                     `p:real`; `r:real`; `q:real`; `s:real`] MOI_FTC_ORD4E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `a:real^N`; `c:real^N`; `d:real^N`; `e:real^N`;
                     `q:real`; `p:real`; `r:real`; `s:real`] MOI_FTC_ORD4E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `c:real^N`; `a:real^N`; `d:real^N`; `e:real^N`;
                     `q:real`; `r:real`; `p:real`; `s:real`] MOI_FTC_ORD4E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                     `r:real`; `p:real`; `q:real`; `s:real`] MOI_FTC_ORD4E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `b:real^N`; `a:real^N`; `d:real^N`; `e:real^N`;
                     `r:real`; `q:real`; `p:real`; `s:real`] MOI_FTC_ORD4E)] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
                                     ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{a:real^N,b,c,d} SUBSET convex hull {a,b,c,d} /\
    midpoint(a,b) IN convex hull {a,b,c,d} /\ midpoint(a,c) IN convex hull {a,b,c,d} /\
    midpoint(b,c) IN convex hull {a,b,c,d} /\ e IN convex hull {a,b,c,d}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HULL_SUBSET; MOI_FTC_IN_HULL4; midpoint] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`inv(&2)`; `inv(&2)`; `&0`; `&0`];
      MAP_EVERY EXISTS_TAC [`inv(&2)`; `&0`; `inv(&2)`; `&0`];
      MAP_EVERY EXISTS_TAC [`&0`; `inv(&2)`; `inv(&2)`; `&0`];
      MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`; `&0`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv(&3)):real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MIDPOINT_SYM] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FTC_DEC_S = prove
 (`!a b c e:real^N.
     &3 % e = a + b + c
     ==> convex hull {a,b,c} =
         convex hull {a,midpoint(a,b),e} UNION convex hull {a,midpoint(a,c),e} UNION
         convex hull {b,midpoint(b,a),e} UNION convex hull {b,midpoint(b,c),e} UNION
         convex hull {c,midpoint(c,a),e} UNION convex hull {c,midpoint(c,b),e}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FTC_IN_HULL3] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `r:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
    REWRITE_TAC[GSYM MOI_FTC_IN_HULL3; IN_UNION] THEN
    MP_TAC(SPECL [`p:real`; `q:real`; `r:real`] MOI_FTC_ORDER3) THEN STRIP_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_FTC_ORD3E THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `c:real^N`; `b:real^N`; `e:real^N`;
                     `p:real`; `r:real`; `q:real`] MOI_FTC_ORD3E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `a:real^N`; `c:real^N`; `e:real^N`;
                     `q:real`; `p:real`; `r:real`] MOI_FTC_ORD3E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `c:real^N`; `a:real^N`; `e:real^N`;
                     `q:real`; `r:real`; `p:real`] MOI_FTC_ORD3E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `a:real^N`; `b:real^N`; `e:real^N`;
                     `r:real`; `p:real`; `q:real`] MOI_FTC_ORD3E);
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `b:real^N`; `a:real^N`; `e:real^N`;
                     `r:real`; `q:real`; `p:real`] MOI_FTC_ORD3E)] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
                                     ASM_REAL_ARITH_TAC]; ALL_TAC]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{a:real^N,b,c} SUBSET convex hull {a,b,c} /\
    midpoint(a,b) IN convex hull {a,b,c} /\ midpoint(a,c) IN convex hull {a,b,c} /\
    midpoint(b,c) IN convex hull {a,b,c} /\ e IN convex hull {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[HULL_SUBSET; MOI_FTC_IN_HULL3; midpoint] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`inv(&2)`; `inv(&2)`; `&0`];
      MAP_EVERY EXISTS_TAC [`inv(&2)`; `&0`; `inv(&2)`];
      MAP_EVERY EXISTS_TAC [`&0`; `inv(&2)`; `inv(&2)`];
      MAP_EVERY EXISTS_TAC [`inv(&3)`; `inv(&3)`; `inv(&3)`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv(&3)):real^N->real^N`) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MIDPOINT_SYM] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FTC_DEC_F = prove
 (`!a b d:real^N.
     convex hull {a,b,d} =
     convex hull {a,midpoint(a,b),d} UNION convex hull {b,midpoint(b,a),d}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FTC_IN_HULL3] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `r:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
    REWRITE_TAC[GSYM MOI_FTC_IN_HULL3; IN_UNION] THEN
    ASM_CASES_TAC `q <= p` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_FTC_ORD2 THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      MP_TAC(ISPECL [`b:real^N`; `a:real^N`; `d:real^N`; `q:real`; `p:real`; `r:real`]
        MOI_FTC_ORD2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  SIMP_TAC[HULL_INC; IN_INSERT] THEN
  REWRITE_TAC[MOI_FTC_IN_HULL3; midpoint] THEN
  MAP_EVERY EXISTS_TAC [`inv(&2)`; `inv(&2)`; `&0`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC);;

let MOI_FTC_DEC_K = prove
 (`!a b:real^N.
     segment[a,b] = segment[a,midpoint(a,b)] UNION segment[b,midpoint(b,a)]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `segment[b:real^N,midpoint(b,a)] = segment[midpoint(a,b),b]`
  SUBST1_TAC THENL [MESON_TAC[SEGMENT_SYM; MIDPOINT_SYM]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC UNION_SEGMENT THEN
  REWRITE_TAC[MIDPOINT_IN_SEGMENT]);;

(* ------------------------------------------------------------------------- *)
(* The closed star of v in sd t meets the wedge, the triangle, the fin and   *)
(* the edges of the triangle in the parts at v.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FTC_BLK_PERM = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> moi_ftc_blk t v u' u x /\ moi_ftc_blk t u v u' x /\ moi_ftc_blk t u u' v x /\
         moi_ftc_blk t u' v u x /\ moi_ftc_blk t u' u v x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_blk] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{v:real^N,u',u,x} = {v,u,u',x} /\ {u,v,u',x} = {v,u,u',x} /\
    {u,u',v,x} = {v,u,u',x} /\ {u',v,u,x} = {v,u,u',x} /\ {u',u,v,x} = {v,u,u',x}`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_FTC_BLK_NOT_IN_SEG = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x ==> ~(v IN segment[u,u'])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of segment[u,u']` MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FTA_LF_BAR];
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_EXTREME_SEGMENT) THEN ASM_MESON_TAC[]]);;

let MOI_FTC_STAR_OM = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER
         convex hull {v,u,u',simplex_barycentre (convex hull {v,u,u',x})} =
         convex hull {v,midpoint(v,u),simplex_barycentre (convex hull {v,u,u'}),
                      simplex_barycentre (convex hull {v,u,u',x})} UNION
         convex hull {v,midpoint(v,u'),simplex_barycentre (convex hull {v,u,u'}),
                      simplex_barycentre (convex hull {v,u,u',x})}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_NOT_IN_SEG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `bs = simplex_barycentre (C3:real^N->bool)` THEN
  ABBREV_TAC `b1 = simplex_barycentre (C4:real^N->bool)` THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `&3 % bs:real^N = v + u + u'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bs:real^N`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b1:real^N`)) THEN
  SUBGOAL_THEN `(v:real^N) IN C3 /\ v IN C4` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C3"; "C4"] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z:real^N. convex hull (IMAGE simplex_barycentre {{w}, segment[w,z], C3, C4}) =
                 convex hull {w, midpoint(w,z), bs, b1} /\
                 convex hull (IMAGE simplex_barycentre {segment[w,z], C3, C4}) =
                 convex hull {midpoint(w,z), bs, b1} /\
                 convex hull (IMAGE simplex_barycentre {C3, C4:real^N->bool}) =
                 convex hull {bs, b1}`
  (LABEL_TAC "img") THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `u:real^N`; `u':real^N`; `b1:real^N`; `bs:real^N`]
    MOI_FTC_DEC_OM) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!w z h'. moi_bar_chain t {{w}, segment[w,z], C3, C4} /\
             (!c. c IN {{w}, segment[w,z], C3, C4} ==> (v:real^N) IN c ==> c IN h')
             ==> St INTER convex hull {w, midpoint(w,z), bs, b1} SUBSET
                 convex hull (IMAGE simplex_barycentre h')`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN segment[u',u])` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v, midpoint(v,u), bs, b1} SUBSET St /\
    convex hull {v, midpoint(v,u'), bs, b1} SUBSET (St:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_IN THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `St INTER convex hull {u, midpoint(u,v), bs, b1} SUBSET
      convex hull {v, midpoint(v,u), bs, b1} /\
    St INTER convex hull {u', midpoint(u',v), bs, b1} SUBSET
      convex hull {v, midpoint(v,u'), bs, b1} /\
    St INTER convex hull {u, midpoint(u,u'), bs, b1} SUBSET
      convex hull {v, midpoint(v,u), bs, b1} /\
    St INTER convex hull {u', midpoint(u',u), bs, b1} SUBSET
      convex hull {v:real^N, midpoint(v,u), bs, b1}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`;
        `{segment[u:real^N,v], C3, C4}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `v:real^N`;
        `{segment[u':real^N,v], C3, C4}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `u':real^N`; `{C3:real^N->bool, C4}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `u:real^N`; `{C3:real^N->bool, C4}`])] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; IN_SING] THEN
    MATCH_MP_TAC(SET_RULE `(b:real^N->bool) SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
    MESON_TAC[MIDPOINT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!St T1 T2 T3 T4 T5 T6:real^N->bool.
      T1 SUBSET St /\ T2 SUBSET St /\ St INTER T3 SUBSET T1 /\ St INTER T5 SUBSET T2 /\
      St INTER T4 SUBSET T1 /\ St INTER T6 SUBSET T1
      ==> St INTER (T1 UNION T2 UNION T3 UNION T4 UNION T5 UNION T6) = T1 UNION T2`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTC_CHAIN_SUBSET = prove
 (`!c f g:(real^N->bool)->bool. moi_bar_chain c f /\ g SUBSET f ==> moi_bar_chain c g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `g:(real^N->bool)->bool = f INTER g` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[MOI_FTA_CHAIN_INTER]]);;

let MOI_FTC_STAR_S = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER convex hull {v,u,u'} =
         convex hull {v,midpoint(v,u),simplex_barycentre (convex hull {v,u,u'})} UNION
         convex hull {v,midpoint(v,u'),simplex_barycentre (convex hull {v,u,u'})}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_NOT_IN_SEG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `bs = simplex_barycentre (C3:real^N->bool)` THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `&3 % bs:real^N = v + u + u'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bs:real^N`)) THEN
  SUBGOAL_THEN `(v:real^N) IN C3` ASSUME_TAC THENL
   [EXPAND_TAC "C3" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z:real^N. convex hull (IMAGE simplex_barycentre {{w}, segment[w,z], C3}) =
                 convex hull {w, midpoint(w,z), bs} /\
                 convex hull (IMAGE simplex_barycentre {segment[w,z], C3}) =
                 convex hull {midpoint(w,z), bs} /\
                 convex hull (IMAGE simplex_barycentre {C3:real^N->bool}) =
                 convex hull {bs}`
  (LABEL_TAC "img") THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z. moi_bar_chain t {{w}, segment[w,z], C3, C4}
          ==> moi_bar_chain t {{w:real^N}, segment[w,z], C3}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_CHAIN_SUBSET THEN
    EXISTS_TAC `{{w:real^N}, segment[w,z], C3, C4}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `u:real^N`; `u':real^N`; `bs:real^N`] MOI_FTC_DEC_S) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!w z h'. moi_bar_chain t {{w}, segment[w,z], C3} /\
             (!c. c IN {{w}, segment[w,z], C3} ==> (v:real^N) IN c ==> c IN h')
             ==> St INTER convex hull {w, midpoint(w,z), bs} SUBSET
                 convex hull (IMAGE simplex_barycentre h')`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN segment[u',u])` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v, midpoint(v,u), bs} SUBSET St /\
    convex hull {v, midpoint(v,u'), bs} SUBSET (St:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_IN THEN
    ASM_SIMP_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `St INTER convex hull {u, midpoint(u,v), bs} SUBSET
      convex hull {v, midpoint(v,u), bs} /\
    St INTER convex hull {u', midpoint(u',v), bs} SUBSET
      convex hull {v, midpoint(v,u'), bs} /\
    St INTER convex hull {u, midpoint(u,u'), bs} SUBSET
      convex hull {v, midpoint(v,u), bs} /\
    St INTER convex hull {u', midpoint(u',u), bs} SUBSET
      convex hull {v:real^N, midpoint(v,u), bs}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`;
        `{segment[u:real^N,v], C3}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `v:real^N`;
        `{segment[u':real^N,v], C3}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `u':real^N`; `{C3:real^N->bool}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `u:real^N`; `{C3:real^N->bool}`])] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[IN_INSERT; IN_SING] THEN
    MATCH_MP_TAC(SET_RULE `(b:real^N->bool) SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
    MESON_TAC[MIDPOINT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!St T1 T2 T3 T4 T5 T6:real^N->bool.
      T1 SUBSET St /\ T2 SUBSET St /\ St INTER T3 SUBSET T1 /\ St INTER T5 SUBSET T2 /\
      St INTER T4 SUBSET T1 /\ St INTER T6 SUBSET T1
      ==> St INTER (T1 UNION T2 UNION T3 UNION T4 UNION T5 UNION T6) = T1 UNION T2`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTC_STAR_F = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER
         (convex hull {v,u,simplex_barycentre (convex hull {v,u,u',x})} UNION
          convex hull {u,u',simplex_barycentre (convex hull {v,u,u',x})} UNION
          convex hull {v,u',simplex_barycentre (convex hull {v,u,u',x})}) =
         convex hull {v,midpoint(v,u),simplex_barycentre (convex hull {v,u,u',x})} UNION
         convex hull {v,midpoint(v,u'),simplex_barycentre (convex hull {v,u,u',x})}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_NOT_IN_SEG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `b1 = simplex_barycentre (C4:real^N->bool)` THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b1:real^N`)) THEN
  SUBGOAL_THEN `(v:real^N) IN C4` ASSUME_TAC THENL
   [EXPAND_TAC "C4" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z:real^N. convex hull (IMAGE simplex_barycentre {{w}, segment[w,z], C4}) =
                 convex hull {w, midpoint(w,z), b1} /\
                 convex hull (IMAGE simplex_barycentre {segment[w,z], C4}) =
                 convex hull {midpoint(w,z), b1} /\
                 convex hull (IMAGE simplex_barycentre {C4:real^N->bool}) =
                 convex hull {b1}`
  (LABEL_TAC "img") THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z. moi_bar_chain t {{w}, segment[w,z], C3, C4}
          ==> moi_bar_chain t {{w:real^N}, segment[w,z], C4}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_CHAIN_SUBSET THEN
    EXISTS_TAC `{{w:real^N}, segment[w,z], C3, C4}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun th -> SUBST1_TAC th)
   [ISPECL [`v:real^N`; `u:real^N`; `b1:real^N`] MOI_FTC_DEC_F;
    ISPECL [`u:real^N`; `u':real^N`; `b1:real^N`] MOI_FTC_DEC_F;
    ISPECL [`v:real^N`; `u':real^N`; `b1:real^N`] MOI_FTC_DEC_F] THEN
  SUBGOAL_THEN
   `!w z h'. moi_bar_chain t {{w}, segment[w,z], C4} /\
             (!c. c IN {{w}, segment[w,z], C4} ==> (v:real^N) IN c ==> c IN h')
             ==> St INTER convex hull {w, midpoint(w,z), b1} SUBSET
                 convex hull (IMAGE simplex_barycentre h')`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN segment[u',u])` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v, midpoint(v,u), b1} SUBSET St /\
    convex hull {v, midpoint(v,u'), b1} SUBSET (St:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    USE_THEN "img" (fun th -> REWRITE_TAC[GSYM(GEN_ALL(CONJUNCT1(SPEC_ALL th)))]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_IN THEN
    ASM_SIMP_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `St INTER convex hull {u, midpoint(u,v), b1} SUBSET
      convex hull {v, midpoint(v,u), b1} /\
    St INTER convex hull {u', midpoint(u',v), b1} SUBSET
      convex hull {v, midpoint(v,u'), b1} /\
    St INTER convex hull {u, midpoint(u,u'), b1} SUBSET
      convex hull {v, midpoint(v,u), b1} /\
    St INTER convex hull {u', midpoint(u',u), b1} SUBSET
      convex hull {v:real^N, midpoint(v,u), b1}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`;
        `{segment[u:real^N,v], C4}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `v:real^N`;
        `{segment[u':real^N,v], C4}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `u':real^N`; `{C4:real^N->bool}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `u:real^N`; `{C4:real^N->bool}`])] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[IN_INSERT; IN_SING] THEN
    MATCH_MP_TAC(SET_RULE `(b:real^N->bool) SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
    MESON_TAC[MIDPOINT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!St T1 T2 T3 T4 T5 T6:real^N->bool.
      T1 SUBSET St /\ T2 SUBSET St /\ St INTER T3 SUBSET T1 /\ St INTER T5 SUBSET T2 /\
      St INTER T4 SUBSET T1 /\ St INTER T6 SUBSET T1
      ==> St INTER ((T1 UNION T3) UNION (T4 UNION T6) UNION (T2 UNION T5)) =
          T1 UNION T2`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FTC_STAR_K = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> UNIONS {s | s IN barycentric_subdivision t /\ v IN s} INTER
         (segment[v,u] UNION segment[u,u'] UNION segment[v,u']) =
         segment[v,midpoint(v,u)] UNION segment[v,midpoint(v,u')]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_NOT_IN_SEG) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN
   `!w z:real^N. segment[w,midpoint(w,z)] =
                 convex hull (IMAGE simplex_barycentre {{w}, segment[w,z]})`
  (LABEL_TAC "img") THENL
   [REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
                SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z. moi_bar_chain t {{w}, segment[w,z], C3, C4}
          ==> moi_bar_chain t {{w:real^N}, segment[w,z]}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_CHAIN_SUBSET THEN
    EXISTS_TAC `{{w:real^N}, segment[w,z], C3, C4}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun th -> SUBST1_TAC th)
   [ISPECL [`v:real^N`; `u:real^N`] MOI_FTC_DEC_K;
    ISPECL [`u:real^N`; `u':real^N`] MOI_FTC_DEC_K;
    ISPECL [`v:real^N`; `u':real^N`] MOI_FTC_DEC_K] THEN
  SUBGOAL_THEN
   `!w z h'. moi_bar_chain t {{w}, segment[w,z]} /\
             (!c. c IN {{w}, segment[w,z]} ==> (v:real^N) IN c ==> c IN h')
             ==> St INTER segment[w, midpoint(w,z)] SUBSET
                 convex hull (IMAGE simplex_barycentre h')`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN segment[u',u])` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[v, midpoint(v,u)] SUBSET St /\
    segment[v, midpoint(v,u')] SUBSET (St:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "img" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "St" THEN MATCH_MP_TAC MOI_FTC_STAR_CHAIN_IN THEN
    ASM_SIMP_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain t {{u:real^N}, segment[u,v]} /\
    moi_bar_chain t {{u':real^N}, segment[u',v]} /\
    moi_bar_chain t {{u:real^N}, segment[u,u']} /\
    moi_bar_chain t {{u':real^N}, segment[u',u]}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "img" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `St INTER segment[u, midpoint(u,v)] SUBSET segment[v, midpoint(v,u)] /\
    St INTER segment[u', midpoint(u',v)] SUBSET segment[v, midpoint(v,u')] /\
    St INTER segment[u, midpoint(u,u')] SUBSET segment[v, midpoint(v,u)] /\
    St INTER segment[u', midpoint(u',u)] SUBSET segment[v:real^N, midpoint(v,u)]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`; `{segment[u:real^N,v]}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `v:real^N`; `{segment[u':real^N,v]}`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `u':real^N`; `{}:(real^N->bool)->bool`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^N`; `u:real^N`; `{}:(real^N->bool)->bool`])] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; IN_SING; NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_EMPTY;
                    EMPTY_SUBSET; MOI_FTA_BARY_SEGMENT; CONVEX_HULL_SING] THEN
    MATCH_MP_TAC(SET_RULE `(b:real^N->bool) SUBSET c ==> a SUBSET b ==> a SUBSET c`) THEN
    REWRITE_TAC[SING_SUBSET; EMPTY_SUBSET] THEN
    MATCH_MP_TAC(MESON[ENDS_IN_SEGMENT]
     `(m:real^N) = m' ==> m IN segment[w,m']`) THEN
    REWRITE_TAC[MIDPOINT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!St T1 T2 T3 T4 T5 T6:real^N->bool.
      T1 SUBSET St /\ T2 SUBSET St /\ St INTER T3 SUBSET T1 /\ St INTER T5 SUBSET T2 /\
      St INTER T4 SUBSET T1 /\ St INTER T6 SUBSET T1
      ==> St INTER ((T1 UNION T3) UNION (T4 UNION T6) UNION (T2 UNION T5)) =
          T1 UNION T2`) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The level picture near the wedge.  Level sets of an affine               *)
(* function on a triangle with values 1, 0, 0 at the vertices; barycentres  *)
(* of simplices of dimension >= 2 avoid the graph; the corner triangles and *)
(* rim segments of the dual disks on the two triangles of the link.         *)
(* ========================================================================= *)

(* f affine along segments, f a = 1, f b = f c = 0 on the triangle conv{a,b,c}: *)
(* the half {f >= 1/2} is the corner triangle at a, {f = 1/2} its far edge.    *)

let MOI_FTC_AFFINE_COMB3 = prove
 (`!(f:real^N->real) a b c u1 u2 u3.
     (!x y w. f((&1 - w) % x + w % y) = (&1 - w) * f x + w * f y) /\
     &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ u1 + u2 + u3 = &1
     ==> f(u1 % a + u2 % b + u3 % c) = u1 * f a + u2 * f b + u3 * f c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u1 = &1` THENL
   [SUBGOAL_THEN `u2 = &0 /\ u3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u1 % a + u2 % b + u3 % c:real^N =
                (&1 - (&1 - u1)) % a + (&1 - u1) % ((u2 / (&1 - u1)) % b +
                                                     (u3 / (&1 - u1)) % c)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `~(&1 - u1 = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u2 / (&1 - u1)) % b + (u3 / (&1 - u1)) % c:real^N =
                (&1 - u3 / (&1 - u1)) % b + (u3 / (&1 - u1)) % c`
  SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(&1 - u1 = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&1 - u1 = &0)` THEN UNDISCH_TAC `u1 + u2 + u3 = &1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&1 - u1 = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(&1 - u1 = &0)` THEN UNDISCH_TAC `u1 + u2 + u3 = &1` THEN
  CONV_TAC REAL_FIELD);;

let MOI_FTC_LEVEL_TRI = prove
 (`!(f:real^N->real) a b c.
     (!x y w. f((&1 - w) % x + w % y) = (&1 - w) * f x + w * f y) /\
     f a = &1 /\ f b = &0 /\ f c = &0
     ==> {x | x IN convex hull {a,b,c} /\ &1 / &2 <= f x} =
         convex hull {a, midpoint(a,b), midpoint(a,c)} /\
         {x | x IN convex hull {a,b,c} /\ f x = &1 / &2} =
         segment[midpoint(a,b), midpoint(a,c)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u1 u2 u3. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ u1 + u2 + u3 = &1
               ==> (f:real^N->real)(u1 % a + u2 % b + u3 % c) = u1`
  (LABEL_TAC "fv") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `u1:real`; `u2:real`; `u3:real`] MOI_FTC_AFFINE_COMB3) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; MOI_FTC_IN_HULL3;
              SEGMENT_CONVEX_HULL; CONVEX_HULL_2; midpoint] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&2 * u1 - &1`; `&2 * u2`; `&2 * u3`] THEN
    UNDISCH_TAC `&1 / &2 <= (f:real^N->real) x` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fv" (fun th -> ASM_SIMP_TAC[th]) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    SUBGOAL_THEN `u1 = &1 - u2 - u3` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    SUBGOAL_THEN
     `x:real^N = (u1 + u2 / &2 + u3 / &2) % a + (u2 / &2) % b + (u3 / &2) % c`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u1 + u2 / &2 + u3 / &2`; `u2 / &2`; `u3 / &2`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "fv" (fun th -> W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC];
    MAP_EVERY EXISTS_TAC [`&2 * u2`; `&2 * u3`] THEN
    UNDISCH_TAC `(f:real^N->real) x = &1 / &2` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fv" (fun th -> ASM_SIMP_TAC[th]) THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    SUBGOAL_THEN `u1 = &1 / &2 /\ u3 = &1 / &2 - u2` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    SUBGOAL_THEN
     `x:real^N = (&1 / &2) % a + (u / &2) % b + (v / &2) % c`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `u = &1 - v` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 / &2`; `u / &2`; `v / &2`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "fv" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* Barycentres of simplices of t of dimension >= 2 are not on the graph. *)

let MOI_FTC_BARY_NOT_IN_GRAPH = prove
 (`!(t:(real^N->bool)->bool) l c.
     graph_in_complex t l /\ c IN t /\ &2 <= aff_dim c
     ==> ~(simplex_barycentre c IN UNIONS l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  UNDISCH_TAC `simplex_barycentre (c:real^N->bool) IN UNIONS l` THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (c:real^N->bool)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&2 <= aff_dim(c:real^N->bool)` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (c:real^N->bool) IN relative_interior c` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c INTER e:real^N->bool) face_of c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`c:real^N->bool`; `e:real^N->bool`] o CONJUNCT1 o
      CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c INTER e:real^N->bool) = c` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c INTER e:real^N->bool`; `c:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `c:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `simplex_barycentre (c:real^N->bool) IN relative_interior c` THEN
    UNDISCH_TAC `simplex_barycentre (c:real^N->bool) IN e` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(c:real^N->bool) <= aff_dim(e:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `&1:int`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* The level homeomorphism on the union of the closed stars of V (the       *)
(* conclusion of MOI_FTC_THETA3).                                           *)

let moi_ftc_lev = new_definition
 `moi_ftc_lev (t:(real^N->bool)->bool) l V (h:real^N->real^N) k <=>
    pl_homeomorphism (UNIONS (moi_ftc_cs (barycentric_subdivision t) V),
                      UNIONS (moi_ftc_cs (barycentric_subdivision t) V)) (h,k) /\
    (!s. s IN moi_ftc_cs (barycentric_subdivision t) V ==> IMAGE h s = s) /\
    (!v m. v IN V /\ m IN barycentric_subdivision t /\ v IN m
           ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                   (!a. a extreme_point_of m ==> f a = if a IN UNIONS l then &1 else &0) /\
                   f v = &1 /\
                   (!x. x IN IMAGE h (derived_dual_cell t l v) /\ x IN m <=>
                        x IN m /\ &1 / &2 <= f x) /\
                   (!x. x IN IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) /\
                        x IN m <=> x IN m /\ f x = &1 / &2))`;;

let MOI_FTC_LEV_EXISTS = prove
 (`!(t:(real^N->bool)->bool) l V.
     graph_in_complex t l /\ FINITE V /\ (!v. v IN V ==> {v} IN l) /\ ~(V = {})
     ==> ?h k. moi_ftc_lev t l V h k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_ftc_lev] THEN
  MATCH_MP_TAC MOI_FTC_THETA3 THEN ASM_REWRITE_TAC[]);;

(* The level description on a part D of a simplex m of sd t containing v. *)

let MOI_FTC_LEV_FACE = prove
 (`!(t:(real^N->bool)->bool) l V h k v W D.
     moi_ftc_lev t l V h k /\ v IN V /\ convex hull W IN barycentric_subdivision t /\
     v IN convex hull W /\ ~affine_dependent W /\ D SUBSET convex hull W
     ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
             (!a. a IN W ==> f a = if a IN UNIONS l then &1 else &0) /\
             IMAGE h (derived_dual_cell t l v) INTER D = {x | x IN D /\ &1 / &2 <= f x} /\
             IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) INTER D =
             {x | x IN D /\ f x = &1 / &2}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_lev] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `convex hull W:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[]]);;

(* h fixes closed stars of the vertices in V; the image of a dual cell lies *)
(* in the closed star.                                                      *)

let MOI_FTC_LEV_STAR = prove
 (`!(t:(real^N->bool)->bool) l V h k v.
     moi_ftc_lev t l V h k /\ v IN V /\ graph_in_complex t l
     ==> IMAGE h (UNIONS {s | s IN barycentric_subdivision t /\ v IN s}) =
         UNIONS {s | s IN barycentric_subdivision t /\ v IN s} /\
         IMAGE h (derived_dual_cell t l v) SUBSET
         UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_lev] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE h (UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}) =
    UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[moi_ftc_cs; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN
    SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
    MP_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_BS_FACTS; graph_in_complex]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[derived_dual_cell; INTER_SUBSET]);;

let MOI_FTC_BLK_DIMS = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> aff_dim(convex hull {v,u,u'}) = &2 /\ aff_dim(convex hull {v,u,u',x}) = &3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

(* The corner triangle and the rim segment of the dual disk of [v,u] on the *)
(* triangle conv{m1,bs,b1} of the link of v, from the level function of v.  *)

let MOI_FTC_LEV_CORNER = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' x.
     moi_ftc_lev t l V h k /\ v IN V /\ graph_in_complex t l /\
     moi_ftc_blk t v u u' x /\ segment[v,u] IN l
     ==> IMAGE h (derived_dual_cell t l v) INTER
         convex hull {midpoint(v,u), simplex_barycentre(convex hull {v,u,u'}),
                      simplex_barycentre(convex hull {v,u,u',x})} =
         convex hull {midpoint(v,u),
                      midpoint(midpoint(v,u), simplex_barycentre(convex hull {v,u,u'})),
                      midpoint(midpoint(v,u), simplex_barycentre(convex hull {v,u,u',x}))} /\
         IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) INTER
         convex hull {midpoint(v,u), simplex_barycentre(convex hull {v,u,u'}),
                      simplex_barycentre(convex hull {v,u,u',x})} =
         segment[midpoint(midpoint(v,u), simplex_barycentre(convex hull {v,u,u'})),
                 midpoint(midpoint(v,u), simplex_barycentre(convex hull {v,u,u',x}))]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_DIMS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `bs = simplex_barycentre (C3:real^N->bool)` THEN
  ABBREV_TAC `b1 = simplex_barycentre (C4:real^N->bool)` THEN
  ABBREV_TAC `m1 = midpoint(v:real^N,u)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bs:real^N`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b1:real^N`)) THEN
  SUBGOAL_THEN `IMAGE simplex_barycentre {{v}, segment[v,u], C3, C4} = {v:real^N,m1,bs,b1}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`;
                 `{v:real^N,m1,bs,b1}`; `convex hull {m1:real^N,bs,b1}`] MOI_FTC_LEV_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{{v:real^N}, segment[v,u], C3, C4}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{v:real^N,m1,bs,b1}`)) THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(m1:real^N) IN UNIONS l /\ ~((bs:real^N) IN UNIONS l) /\
                ~((b1:real^N) IN UNIONS l)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,u]` THEN
      EXPAND_TAC "m1" THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      EXPAND_TAC "bs" THEN MATCH_MP_TAC MOI_FTC_BARY_NOT_IN_GRAPH THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      EXPAND_TAC "b1" THEN MATCH_MP_TAC MOI_FTC_BARY_NOT_IN_GRAPH THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real) m1 = &1 /\ f bs = &0 /\ f b1 = &0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `UNIONS (l:(real^N->bool)->bool)`)) (concl th))) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `m1:real^N` th) THEN MP_TAC(SPEC `bs:real^N` th) THEN
                         MP_TAC(SPEC `b1:real^N` th)) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`; `m1:real^N`; `bs:real^N`; `b1:real^N`]
    MOI_FTC_LEVEL_TRI) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The dual cell of u does not reach the triangle conv{m2,bs,b1} of the     *)
(* link of v at the other edge [v,u'].                                       *)

let MOI_FTC_LEV_FAR = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' x.
     moi_ftc_lev t l V h k /\ u IN V /\ graph_in_complex t l /\ moi_ftc_blk t v u u' x
     ==> IMAGE h (derived_dual_cell t l u) INTER
         convex hull {midpoint(v,u'), simplex_barycentre(convex hull {v,u,u'}),
                      simplex_barycentre(convex hull {v,u,u',x})} = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_DIMS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  SUBGOAL_THEN `moi_ftc_blk t (u:real^N) v u' x` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTC_BLK_PERM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTC_BLK_NOT_IN_SEG o check (fun th ->
    concl th = `moi_ftc_blk t (u:real^N) v u' x`)) THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk] o check (fun th ->
    concl th = `moi_ftc_blk t (v:real^N) u u' x`)) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `bs = simplex_barycentre (C3:real^N->bool)` THEN
  ABBREV_TAC `b1 = simplex_barycentre (C4:real^N->bool)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bs:real^N`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b1:real^N`)) THEN
  SUBGOAL_THEN `{u:real^N} IN t` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the closed star of u meets the triangle only in segment[bs,b1] *)
  SUBGOAL_THEN
   `UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s} INTER
    convex hull {midpoint(v,u'), bs, b1} SUBSET segment[bs,b1]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull {midpoint(v,u'), bs, b1} =
                  convex hull (IMAGE simplex_barycentre {segment[v:real^N,u'], C3, C4}) /\
                  segment[bs,b1] = convex hull (IMAGE simplex_barycentre {C3:real^N->bool, C4})`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SEGMENT; SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_CHAIN_SUBSET THEN
      EXISTS_TAC `{{v:real^N}, segment[v,u'], C3, C4}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the level function of u vanishes on segment[bs,b1] *)
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (derived_dual_cell t l u) INTER segment[bs:real^N,b1] = {}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE simplex_barycentre {{u}, segment[u,v], C3, C4} =
      {u:real^N, midpoint(u,v), bs, b1}`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain t {{u:real^N}, segment[u,v], C3, C4}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `u:real^N`;
                   `{u:real^N, midpoint(u,v), bs, b1}`; `segment[bs:real^N,b1]`]
      MOI_FTC_LEV_FACE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{{u:real^N}, segment[u,v], C3, C4}` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `{u:real^N, midpoint(u,v), bs, b1}`)) THEN
        MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~((bs:real^N) IN UNIONS l) /\ ~((b1:real^N) IN UNIONS l)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "bs"; EXPAND_TAC "b1"] THEN
      MATCH_MP_TAC MOI_FTC_BARY_NOT_IN_GRAPH THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^N->real) bs = &0 /\ f b1 = &0` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `UNIONS (l:(real^N->bool)->bool)`)) (concl th))) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `bs:real^N` th) THEN MP_TAC(SPEC `b1:real^N` th)) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `u:real^N`] MOI_FTC_LEV_STAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Facts in the original space about the dual cells near the                *)
(* triangle s: vertices off the graph are outside the derived neighbourhood, *)
(* the finger cells avoid the wedge, the traces of the frontier set and of   *)
(* the link on one dual cell, and the relations between wedge, its           *)
(* complement, triangle, fin and core.                                       *)
(* ========================================================================= *)

let MOI_FTC_VERT_NOT_NBHD = prove
 (`!(t:(real^N->bool)->bool) l p.
     graph_in_complex t l /\ {p} IN barycentric_subdivision t /\ ~(p IN UNIONS l)
     ==> ~(p IN derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(p:real^N) IN derived_nbhd t l` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_NBHD; NOT_EXISTS_THM] THEN
  X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `g:(real^N->bool)->bool`; `p:real^N`] MOI_FTA_VERTEX_IN_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(g INTER barycentric_subdivision (l:(real^N->bool)->bool) = {})` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  UNDISCH_TAC `~((p:real^N) IN UNIONS l)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* A vertex of t off conv{v,u,u'} meets the wedge only in b1 (through its   *)
(* closed star in sd t).                                                    *)

let MOI_FTC_FAR_VERTEX_OM = prove
 (`!(t:(real^N->bool)->bool) v u u' x w.
     moi_ftc_blk t v u u' x /\ {w} IN t /\ ~(w IN {v,u,u'})
     ==> UNIONS {s | s IN barycentric_subdivision t /\ w IN s} INTER
         convex hull {v,u,u',simplex_barycentre (convex hull {v,u,u',x})} SUBSET
         {simplex_barycentre (convex hull {v,u,u',x})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  ABBREV_TAC `bs = simplex_barycentre (C3:real^N->bool)` THEN
  ABBREV_TAC `b1 = simplex_barycentre (C4:real^N->bool)` THEN
  SUBGOAL_THEN `&3 % bs:real^N = v + u + u'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `bs:real^N`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b1:real^N`)) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^N) IN C3)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `C3:real^N->bool`; `w:real^N`]
      MOI_FTA_VERTEX_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C3" THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q. p IN {v,u,u'} /\ q IN {v,u,u'} ==> ~((w:real^N) IN segment[p,q])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~((w:real^N) IN C3)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N) IN segment[p,q]` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> w IN s ==> w IN t`) THEN
    EXPAND_TAC "C3" THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `u:real^N`; `u':real^N`; `b1:real^N`; `bs:real^N`]
    MOI_FTC_DEC_OM) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!p q. moi_bar_chain t {{p}, segment[p,q], C3, C4} /\ p IN {v,u,u'} /\ q IN {v,u,u'}
          ==> UNIONS {s | s IN barycentric_subdivision t /\ (w:real^N) IN s} INTER
              convex hull {p, midpoint(p,q), bs, b1} SUBSET {b1}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `convex hull {p, midpoint(p,q), bs, b1} =
                  convex hull (IMAGE simplex_barycentre {{p:real^N}, segment[p,q], C3, C4}) /\
                  {b1} = convex hull (IMAGE simplex_barycentre {C4:real^N->bool})`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
                      CONVEX_HULL_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTC_STAR_CHAIN_SUB THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `c:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SING]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN TRY(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SING]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_OVER_INTER; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The sets of the cell decomposition of N_s (original space).  All are     *)
(* symmetric in v, u, u'.                                                    *)
(* ------------------------------------------------------------------------- *)

let moi_ftc_om = new_definition
 `moi_ftc_om (v:real^N) u u' x =
    convex hull {v,u,u',simplex_barycentre (convex hull {v,u,u',x})}`;;

let moi_ftc_fin = new_definition
 `moi_ftc_fin (v:real^N) u u' x =
    convex hull {v,u,simplex_barycentre (convex hull {v,u,u',x})} UNION
    convex hull {u,u',simplex_barycentre (convex hull {v,u,u',x})} UNION
    convex hull {v,u',simplex_barycentre (convex hull {v,u,u',x})}`;;

let moi_ftc_core = new_definition
 `moi_ftc_core (v:real^N) u u' = segment[v,u] UNION segment[u,u'] UNION segment[v,u']`;;

let moi_ftc_fing = new_definition
 `moi_ftc_fing (t:(real^N->bool)->bool) l v u u' =
    UNIONS {derived_dual_cell t l p INTER derived_dual_cell t l w | p,w |
            p IN {v,u,u'} /\ ~(w IN {v,u,u'}) /\ segment[p,w] IN l}`;;

let moi_ftc_xs = new_definition
 `moi_ftc_xs (t:(real^N->bool)->bool) l v u u' =
    ((derived_dual_cell t l v UNION derived_dual_cell t l u UNION derived_dual_cell t l u')
     INTER derived_frontier t l) UNION moi_ftc_fing t l v u u'`;;

let MOI_FTC_SETS_SYM = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     moi_ftc_om v u u' x = moi_ftc_om u v u' x /\
     moi_ftc_om v u u' x = moi_ftc_om v u' u x /\
     moi_ftc_fin v u u' x = moi_ftc_fin u v u' x /\
     moi_ftc_fin v u u' x = moi_ftc_fin v u' u x /\
     moi_ftc_core v u u' = moi_ftc_core u v u' /\
     moi_ftc_core v u u' = moi_ftc_core v u' u /\
     moi_ftc_fing t l v u u' = moi_ftc_fing t l u v u' /\
     moi_ftc_fing t l v u u' = moi_ftc_fing t l v u' u /\
     moi_ftc_xs t l v u u' = moi_ftc_xs t l u v u' /\
     moi_ftc_xs t l v u u' = moi_ftc_xs t l v u' u /\
     convex hull {v,u,u'} = convex hull {u,v,u'} /\
     convex hull {v,u,u'} = convex hull {v,u',u}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_ftc_om; moi_ftc_fin; moi_ftc_core; moi_ftc_fing; moi_ftc_xs] THEN
  REWRITE_TAC[INSERT_AC; SEGMENT_SYM] THEN REWRITE_TAC[UNION_ACI]);;

(* The dual cell of a graph vertex off s avoids the wedge. *)

let MOI_FTC_FING_OM = prove
 (`!(t:(real^N->bool)->bool) l v u u' x w.
     graph_in_complex t l /\ moi_ftc_blk t v u u' x /\ {w} IN l /\ ~(w IN {v,u,u'})
     ==> derived_dual_cell t l w INTER moi_ftc_om v u u' x = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_DIMS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  SUBGOAL_THEN `{w:real^N} IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`;
                 `x:real^N`; `w:real^N`] MOI_FTC_FAR_VERTEX_OM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~(simplex_barycentre (convex hull {v:real^N,u,u',x}) IN derived_nbhd t l)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_VERT_NOT_NBHD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_BARY_VERTEX THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      MATCH_MP_TAC MOI_FTC_BARY_NOT_IN_GRAPH THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_om] THEN
  UNDISCH_TAC `~(simplex_barycentre (convex hull {v:real^N,u,u',x}) IN derived_nbhd t l)` THEN
  UNDISCH_TAC
   `UNIONS {s | s IN barycentric_subdivision t /\ (w:real^N) IN s} INTER
    convex hull {v,u,u',simplex_barycentre (convex hull {v,u,u',x})} SUBSET
    {simplex_barycentre (convex hull {v,u,u',x})}` THEN
  REWRITE_TAC[derived_dual_cell] THEN SET_TAC[]);;

(* The frontier set and the link on one dual cell. *)

let MOI_FTC_CV_XS = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     graph_in_complex t l /\ moi_ftc_blk t v u u' x /\
     segment[v,u] IN l /\ segment[v,u'] IN l
     ==> derived_dual_cell t l v INTER moi_ftc_xs t l v u u' =
         (derived_dual_cell t l v INTER derived_frontier t l) UNION
         UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                 ~(w IN {v,u,u'}) /\ segment[v,w] IN l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  SUBGOAL_THEN `{v:real^N} IN l /\ {u} IN l /\ {u'} IN l` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_SEG_VERTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p w. p IN {v,u,u'} /\ ~(p = v) /\ ~(w IN {v,u,u'}) /\ segment[p,w] IN l
          ==> derived_dual_cell t l v INTER derived_dual_cell t l p INTER
              derived_dual_cell t l (w:real^N) = {}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTC_TRIPLE THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_MESON_TAC[MOI_FTA_SEG_VERTS]; ALL_TAC]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_xs; moi_ftc_fing] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTER; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[IN_INSERT; IN_INTER]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)))) THEN
  ASM_CASES_TAC `p:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^N`; `w:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "derived_dual_cell"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FTC_CV_LINK = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     graph_in_complex t l /\ moi_ftc_blk t v u u' x /\
     segment[v,u] IN l /\ segment[v,u'] IN l
     ==> derived_dual_cell t l v INTER
         UNIONS (simplicial_link (barycentric_subdivision t) v) =
         (derived_dual_cell t l v INTER derived_dual_cell t l u) UNION
         (derived_dual_cell t l v INTER derived_dual_cell t l u') UNION
         UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                 ~(w IN {v,u,u'}) /\ segment[v,w] IN l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  SUBGOAL_THEN `{v:real^N} IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_SEG_VERTS; graph_in_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_WALLS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC `w:real^N = u` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `w:real^N = u'` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (u:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N` THEN ASM_MESON_TAC[];
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (u':real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `u':real^N` THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[]]);;

(* The wedge is a 3-simplex: {v,u,u',b1} is affinely independent. *)

let MOI_FTC_B1_INDEP = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> ~affine_dependent {v,u,u',simplex_barycentre (convex hull {v,u,u',x})} /\
         ~(simplex_barycentre (convex hull {v,u,u',x}) IN {v,u,u'})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(inv(&4) % (v + u + u' + x):real^N IN affine hull {v,u,u'})`
  ASSUME_TAC THENL
   [REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `r:real`
      STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `~affine_dependent {v:real^N,u,u',x}` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `{v:real^N,u,u',x} DELETE x = {v,u,u'}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&4 * p - &1`; `&4 * q - &1`; `&4 * r - &1`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (&4):real^N->real^N`) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{v:real^N,u,u',inv(&4) % (v + u + u' + x)} =
                  (inv(&4) % (v + u + u' + x)) INSERT {v,u,u'}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(inv(&4) % (v + u + u' + x):real^N IN affine hull {v,u,u'})` THEN
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `{v:real^N,u,u'}`] HULL_SUBSET) THEN
    SET_TAC[]]);;

(* R1: wedge meets the closure of its complement in triangle and fin;     *)
(* R3: triangle meets fin in the core.                                      *)

let MOI_FTC_R1 = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> moi_ftc_om v u u' x INTER ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x)) =
         convex hull {v,u,u'} UNION moi_ftc_fin v u u' x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_B1_INDEP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  REWRITE_TAC[moi_ftc_om; moi_ftc_fin] THEN
  ABBREV_TAC `b1 = simplex_barycentre (convex hull {v:real^N,u,u',x})` THEN
  REWRITE_TAC[SET_RULE `(s:real^N->bool) INTER (UNIV DIFF r) = s DIFF r`] THEN
  SUBGOAL_THEN
   `convex hull {v:real^N,u,u',b1} DIFF relative_interior (convex hull {v,u,u',b1}) =
    relative_frontier (convex hull {v,u,u',b1})`
  SUBST1_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `convex hull {v:real^N,u,u',b1}` CLOSURE_CLOSED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  SUBGOAL_THEN
   `{v:real^N,u,u',b1} DELETE v = {u,u',b1} /\ {v,u,u',b1} DELETE u = {v,u',b1} /\
    {v,u,u',b1} DELETE u' = {v,u,b1} /\ {v,u,u',b1} DELETE b1 = {v,u,u'}`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM]) THEN
    REPEAT CONJ_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FTC_R3 = prove
 (`!(t:(real^N->bool)->bool) v u u' x.
     moi_ftc_blk t v u u' x
     ==> convex hull {v,u,u'} INTER moi_ftc_fin v u u' x = moi_ftc_core v u u'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_B1_INDEP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  REWRITE_TAC[moi_ftc_fin; moi_ftc_core; UNION_OVER_INTER] THEN
  ABBREV_TAC `b1 = simplex_barycentre (convex hull {v:real^N,u,u',x})` THEN
  SUBGOAL_THEN
   `!A B. A SUBSET {v:real^N,u,u',b1} /\ B SUBSET {v,u,u',b1}
          ==> convex hull A INTER convex hull B = convex hull (A INTER B)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_HULL_INTER THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,u,u',b1}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{v:real^N,u,u'} INTER {v,u,b1} = {v,u} /\ {v,u,u'} INTER {u,u',b1} = {u,u'} /\
    {v,u,u'} INTER {v,u',b1} = {v,u'}`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM]) THEN
    REPEAT CONJ_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v:real^N,u,u'} INTER convex hull {v,u,b1} = segment[v,u] /\
    convex hull {v:real^N,u,u'} INTER convex hull {u,u',b1} = segment[u,u'] /\
    convex hull {v:real^N,u,u'} INTER convex hull {v,u',b1} = segment[v,u']`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N,u,u'}`; `{v:real^N,u,b1}`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N,u,u'}`; `{u:real^N,u',b1}`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N,u,u'}`; `{v:real^N,u',b1}`])] THEN
  (ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  ASM_REWRITE_TAC[]);;

(* The graph does not meet the frontier of the derived neighbourhood (in   *)
(* the level picture the graph sits at level 1).                            *)

let MOI_FTC_GRAPH_NOT_FR = prove
 (`!(t:(real^N->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l
     ==> derived_dual_cell t l v INTER derived_frontier t l INTER UNIONS l = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{v:real^N}`]
    MOI_FTC_LEV_EXISTS) THEN
  ASM_REWRITE_TAC[FINITE_SING; IN_SING; NOT_INSERT_EMPTY] THEN
  ANTS_TAC THENL [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_TAC `k:real^N->real^N`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_lev]) THEN
  SUBGOAL_THEN
   `!W. convex hull W IN barycentric_subdivision t /\ (v:real^N) IN convex hull W /\
        ~affine_dependent W /\ (!a. a IN W ==> a IN UNIONS l)
        ==> IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) INTER
            convex hull W = {}`
  (LABEL_TAC "nofr") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{v:real^N}`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`; `W:real^N->bool`;
                   `convex hull W:real^N->bool`] MOI_FTC_LEV_FACE) THEN
    ASM_REWRITE_TAC[IN_SING; SUBSET_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!y. y IN convex hull W ==> (f:real^N->real) y = &1` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_LEVEL_HULL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_CELL_GRAPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_INSERT; IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_frontier t l) INTER
      {v} = {}`
    MP_TAC THENL
     [USE_THEN "nofr" (MP_TAC o SPEC `{v:real^N}`) THEN
      REWRITE_TAC[CONVEX_HULL_SING; IN_SING; AFFINE_INDEPENDENT_1] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) {v} = {v}` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[moi_ftc_cs; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`v:real^N`; `{v:real^N}`] THEN
      ASM_REWRITE_TAC[IN_SING; FACE_OF_SING; EXTREME_POINT_OF_SING];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SET_RULE `{a:real^N} = {b} <=> a = b`] THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^N->bool`)) THEN
  SUBGOAL_THEN `segment[v:real^N,midpoint(v,w)] IN barycentric_subdivision t`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{{v:real^N}, segment[v,w]}` THEN
    REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
                GSYM SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `{v:real^N} IN t /\ segment[v,w] IN t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MOI_FTA_SEG_VERTS]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; SEGMENT_EQ_EMPTY; NOT_INSERT_EMPTY; IN_SING] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_frontier t l) INTER
    segment[v,midpoint(v,w)] = {}`
  MP_TAC THENL
   [USE_THEN "nofr" (MP_TAC o SPEC `{v:real^N, midpoint(v,w)}`) THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN CONJ_TAC THENL
     [REWRITE_TAC[AFFINE_INDEPENDENT_2];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_UNIONS] THENL
       [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
        EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (segment[v,midpoint(v,w)]) =
                segment[v,midpoint(v,w)]` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[moi_ftc_cs; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `segment[v:real^N,midpoint(v,w)]`] THEN
    ASM_REWRITE_TAC[IN_SING; ENDS_IN_SEGMENT] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_SEGMENT];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) y`) THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `segment[v:real^N,midpoint(v,w)]`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;


(* The midpoint of a finger edge is not on another edge of t through two    *)
(* vertices of s; R4: the core misses the frontier set.                      *)

let MOI_FTC_MID_NOT_EDGE = prove
 (`!(t:(real^N->bool)->bool) p w a b.
     lf_simplicial_complex t /\ segment[p,w] IN t /\ segment[a,b] IN t /\
     {w} IN t /\ ~(p = w) /\ ~(w = a) /\ ~(w = b)
     ==> ~(midpoint(p,w) IN segment[a,b])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(segment[p:real^N,w] INTER segment[a,b]) face_of segment[p,w]`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`segment[p:real^N,w]`; `segment[a:real^N,b]`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^N,w] INTER segment[a,b] = segment[p,w]` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[p:real^N,w] INTER segment[a,b]`; `segment[p:real^N,w]`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `midpoint(p:real^N,w)`) THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN segment[a,b]` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[p:real^N,w] INTER segment[a,b] = segment[p,w]` THEN
    MP_TAC(ISPECL [`p:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of segment[a,b]` MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FTA_LF_BAR];
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_EXTREME_SEGMENT) THEN ASM_REWRITE_TAC[]]);;

let MOI_FTC_R4 = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     graph_in_complex t l /\ moi_ftc_blk t v u u' x /\
     segment[v,u] IN l /\ segment[u,u'] IN l /\ segment[v,u'] IN l
     ==> moi_ftc_core v u u' INTER moi_ftc_xs t l v u u' = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  SUBGOAL_THEN `{v:real^N} IN l /\ {u} IN l /\ {u'} IN l` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_SEG_VERTS]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_ftc_core v u (u':real^N) SUBSET UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_core; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N. p IN {v,u,u'}
               ==> derived_dual_cell t l p INTER derived_frontier t l INTER UNIONS l = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTC_GRAPH_NOT_FR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p w:real^N. p IN {v,u,u'} /\ ~(w IN {v,u,u'}) /\ segment[p,w] IN l
                 ==> moi_ftc_core v u u' INTER
                     derived_dual_cell t l p INTER derived_dual_cell t l w = {}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(p:real^N = w)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `p:real^N`;
                   `w:real^N`] MOI_FTA_DISK_GRAPH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(midpoint(p:real^N,w) IN moi_ftc_core v u u')` ASSUME_TAC THENL
     [REWRITE_TAC[moi_ftc_core; IN_UNION; DE_MORGAN_THM] THEN
      SUBGOAL_THEN `{w:real^N} IN t /\ segment[p,w] IN t /\ segment[v,u] IN t /\
                    segment[u,u'] IN t /\ segment[v,u'] IN t`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MOI_FTA_SEG_VERTS]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM]) THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_MID_NOT_EDGE THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_xs; moi_ftc_fing; UNION_OVER_INTER; EMPTY_UNION] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `v:real^N` (ASSUME
      `!p:real^N. p IN {v,u,u'}
                  ==> derived_dual_cell t l p INTER derived_frontier t l INTER UNIONS l = {}`)) THEN
    MP_TAC(SPEC `u:real^N` (ASSUME
      `!p:real^N. p IN {v,u,u'}
                  ==> derived_dual_cell t l p INTER derived_frontier t l INTER UNIONS l = {}`)) THEN
    MP_TAC(SPEC `u':real^N` (ASSUME
      `!p:real^N. p IN {v,u,u'}
                  ==> derived_dual_cell t l p INTER derived_frontier t l INTER UNIONS l = {}`)) THEN
    REWRITE_TAC[IN_INSERT] THEN
    UNDISCH_TAC `moi_ftc_core v u (u':real^N) SUBSET UNIONS l` THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `(!s. s IN f ==> (a:real^N->bool) INTER s = {}) ==> a INTER UNIONS f = {}`) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Abstract 2-dimensional pieces: two triangles glued along an              *)
(* edge (the wedge trace Q on the link), triangles and segments as cells.    *)
(* ========================================================================= *)

let MOI_FTC_TRI_CELL = prove
 (`!a b c:real^N.
     ~collinear {a,b,c}
     ==> pl_cell_with_boundary 2 (convex hull {a,b,c})
           (segment[a,b] UNION segment[b,c] UNION segment[c,a])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [SYM(MATCH_MP RELATIVE_FRONTIER_OF_TRIANGLE th)]) THEN
  MATCH_MP_TAC MOI_S5V_SIMPLEX_CELL THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `{a:real^N,b,c}` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV);;

(* Two triangles glued along their common edge [bs,b1]. *)

let MOI_FTC_Q_CELL = prove
 (`!m1 m2 bs b1:real^N.
     ~collinear {m1,bs,b1} /\ ~collinear {m2,bs,b1} /\
     convex hull {m1,bs,b1} INTER convex hull {m2,bs,b1} = segment[bs,b1]
     ==> pl_cell_with_boundary 2 (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})
           (segment[m1,bs] UNION segment[bs,m2] UNION segment[m1,b1] UNION
            segment[b1,m2])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull {m1:real^N,bs,b1}`;
                 `segment[m1:real^N,bs] UNION segment[bs,b1] UNION segment[b1,m1]`;
                 `convex hull {m2:real^N,bs,b1}`;
                 `segment[m2:real^N,bs] UNION segment[bs,b1] UNION segment[b1,m2]`;
                 `bs:real^N`; `b1:real^N`] MOI_FTC_GLUE_SEG) THEN
  ASM_SIMP_TAC[MOI_FTC_TRI_CELL] THEN
  SUBGOAL_THEN `~(bs:real^N = b1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,bs,b1}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`; `b1:real^N`] MOI_FSA_TRI_EDGES) THEN
  MP_TAC(ISPECL [`m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FSA_TRI_EDGES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `segment[b1:real^N,m1] = segment[m1,b1] /\
                segment[m2:real^N,bs] = segment[bs,m2]`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`m1:real^N`; `b1:real^N`] ENDS_IN_SEGMENT) THEN
  SET_TAC[]);;


(* The corner triangle conv{a,p,q}, p = mid(a,b), q = mid(a,c), of a      *)
(* triangle conv{a,b,c}: its traces on the edges.                           *)

let MOI_FTC_CORNER_GEOM = prove
 (`!a b c:real^N.
     ~collinear {a,b,c}
     ==> ~collinear {a, midpoint(a,b), midpoint(a,c)} /\
         convex hull {a, midpoint(a,b), midpoint(a,c)} SUBSET convex hull {a,b,c} /\
         convex hull {a, midpoint(a,b), midpoint(a,c)} INTER segment[a,b] =
         segment[a,midpoint(a,b)] /\
         convex hull {a, midpoint(a,b), midpoint(a,c)} INTER segment[a,c] =
         segment[a,midpoint(a,c)] /\
         convex hull {a, midpoint(a,b), midpoint(a,c)} INTER segment[b,c] = {} /\
         segment[midpoint(a,b),midpoint(a,c)] INTER segment[a,b] = {midpoint(a,b)} /\
         segment[midpoint(a,b),midpoint(a,c)] INTER segment[a,c] = {midpoint(a,c)} /\
         segment[midpoint(a,b),midpoint(a,c)] INTER segment[b,c] = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~affine_dependent {a:real^N,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{a:real^N,b,c}`; `\x:real^N. x = a`] MOI_FTA_LEVEL_FN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->real) a = &1 /\ f b = &0 /\ f c = &0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      W(fun (_,w) -> MP_TAC(SPEC (rand(lhs w)) th))) THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `b:real^N`; `c:real^N`]
    MOI_FTC_LEVEL_TRI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  SUBGOAL_THEN
   `!x y:real^N s. f((&1 - s) % x + s % y) = (&1 - s) * f x + s * (f:real^N->real) y`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] SUBSET convex hull {a,b,c} /\
    segment[a:real^N,c] SUBSET convex hull {a,b,c} /\
    segment[b:real^N,c] SUBSET convex hull {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  (* the three edges in parametric form *)
  SUBGOAL_THEN
   `!z:real^N. z IN segment[a,b] <=> ?s. &0 <= s /\ s <= &1 /\ z = (&1 - s) % a + s % b`
  ASSUME_TAC THENL [REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN segment[a,c] <=> ?s. &0 <= s /\ s <= &1 /\ z = (&1 - s) % a + s % c`
  ASSUME_TAC THENL [REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN segment[a,midpoint(a,b)] <=>
               ?s. &0 <= s /\ s <= &1 / &2 /\ z = (&1 - s) % a + s % b`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT; midpoint] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `u / &2` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
      VECTOR_ARITH_TAC;
      EXISTS_TAC `&2 * s` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN segment[a,midpoint(a,c)] <=>
               ?s. &0 <= s /\ s <= &1 / &2 /\ z = (&1 - s) % a + s % c`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT; midpoint] THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `u / &2` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
      VECTOR_ARITH_TAC;
      EXISTS_TAC `&2 * s` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* noncollinear corner *)
    REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `w0:real^N` ASSUME_TAC)) THEN
    UNDISCH_TAC `~collinear {a:real^N,b,c}` THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`u0:real^N`; `w0:real^N`] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    UNDISCH_TAC `{a:real^N, midpoint(a,b), midpoint(a,c)} SUBSET affine hull {u0,w0}` THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `b:real^N = (&1 - &2) % a + &2 % midpoint(a,b) /\
                  c:real^N = (&1 - &2) % a + &2 % midpoint(a,c)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[midpoint] THEN CONJ_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    (* H SUBSET triangle *)
    SET_TAC[];
    (* H INTER [a,b] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `s:real` THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `segment[a:real^N,b] SUBSET convex hull {a,b,c}`)) THEN
        REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s:real` THEN REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        EXISTS_TAC `s:real` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    (* H INTER [a,c] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `s:real` THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `segment[a:real^N,c] SUBSET convex hull {a,b,c}`)) THEN
        REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s:real` THEN REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        EXISTS_TAC `s:real` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    (* H INTER [b,c] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_SEGMENT] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)
      (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    (* [p,q] INTER [a,b] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `s = &1 / &2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `midpoint(a:real^N,b) = (&1 - &1 / &2) % a + (&1 / &2) % b`
      SUBST1_TAC THENL [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `segment[a:real^N,b] SUBSET convex hull {a,b,c}`)) THEN
        REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 / &2` THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
        CONV_TAC REAL_RAT_REDUCE_CONV;
        EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    (* [p,q] INTER [a,c] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `s = &1 / &2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `midpoint(a:real^N,c) = (&1 - &1 / &2) % a + (&1 / &2) % c`
      SUBST1_TAC THENL [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `segment[a:real^N,c] SUBSET convex hull {a,b,c}`)) THEN
        REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 / &2` THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
        CONV_TAC REAL_RAT_REDUCE_CONV;
        EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    (* [p,q] INTER [b,c] *)
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_SEGMENT] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)
      (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Gluing along a two-segment arc: MOI_FRS_GLUE2 (pc_moi_fnd_rnsc).          *)


(* A PL 1-sphere is not convex (it is not simply connected).  The first  *)
(* step is the content of MOI_FSTR_PL_SPHERE1_HOMEO (pc_moi_fnd_sptrace,   *)
(* outside this closure).                                                   *)

let MOI_FTC_SPHERE1_NOT_CONVEX = prove
 (`!s:real^N->bool. pl_sphere 1 s ==> ~convex s`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) homeomorphic sphere(vec 0:real^2,&1)` MP_TAC THENL
   [MATCH_MP_TAC(ISPECL [`s:real^N->bool`; `relative_frontier(k:real^N->bool)`;
                         `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[RELATIVE_FRONTIER_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `&(1 + 1) simplex (k:real^N->bool)` THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ) THEN
    ASM_SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; SIMPLY_CONNECTED_SPHERE_EQ; DIMINDEX_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ========================================================================= *)
(* The abstract block.  A level region Y radial from v over                 *)
(* the link sphere L, with outer sphere X = Z UNION (Y INTER L); two link    *)
(* triangles conv{m_i,bs,b1} forming the wedge trace Q; the two dual disks  *)
(* G_i (rims R_i) meeting Q in the corner triangles; finger disks Fg off Q. *)
(* ========================================================================= *)

let moi_ftc_abl = new_definition
 `moi_ftc_abl (v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg <=>
    moi_ftc_rad v L X Y /\ X = Z UNION (Y INTER L) /\ Z SUBSET Y /\
    ~collinear {m1,bs,b1} /\ ~collinear {m2,bs,b1} /\
    convex hull {m1,bs,b1} INTER convex hull {m2,bs,b1} = segment[bs,b1] /\
    convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} SUBSET L /\
    pl_cell_with_boundary 2 G1 R1 /\ pl_cell_with_boundary 2 G2 R2 /\
    G1 INTER convex hull {m1,bs,b1} =
    convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} /\
    G1 INTER convex hull {m2,bs,b1} = {} /\
    G2 INTER convex hull {m2,bs,b1} =
    convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)} /\
    G2 INTER convex hull {m1,bs,b1} = {} /\
    R1 INTER convex hull {m1,bs,b1} = segment[midpoint(m1,bs), midpoint(m1,b1)] /\
    R2 INTER convex hull {m2,bs,b1} = segment[midpoint(m2,bs), midpoint(m2,b1)] /\
    Y INTER L = G1 UNION G2 UNION Fg /\
    Fg INTER (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) = {} /\
    Fg INTER (G1 UNION G2) = {} /\ G1 INTER G2 = {} /\
    Z INTER G1 = R1 /\ Z INTER G2 = R2`;;

(* Pure geometry of the two link triangles D1 = conv{m1,bs,b1} and          *)
(* D2 = conv{m2,bs,b1} sharing the edge [bs,b1].                            *)

let MOI_FTC_TWO_TRI = prove
 (`!m1 m2 bs b1:real^N.
     ~collinear {m1,bs,b1} /\ ~collinear {m2,bs,b1} /\
     convex hull {m1,bs,b1} INTER convex hull {m2,bs,b1} = segment[bs,b1]
     ==> ~(m1 = bs) /\ ~(m1 = b1) /\ ~(bs = b1) /\ ~(m2 = bs) /\ ~(m2 = b1) /\
         ~(m1 = m2) /\
         (segment[m1,bs] UNION segment[bs,m2]) INTER
         (segment[m1,b1] UNION segment[b1,m2]) = {m1,m2} /\
         segment[m1,bs] UNION segment[bs,m2] UNION segment[m1,b1] UNION segment[b1,m2]
         SUBSET convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
         segment[m1,bs] INTER segment[bs,m2] = {bs} /\
         segment[m1,b1] INTER segment[b1,m2] = {b1} /\
         convex hull {m1,bs,b1} INTER (segment[bs,m2] UNION segment[b1,m2]) SUBSET
         {bs,b1} /\
         convex hull {m2,bs,b1} INTER (segment[m1,bs] UNION segment[m1,b1]) SUBSET
         {bs,b1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m1:real^N = bs) /\ ~(m1 = b1) /\ ~(bs = b1) /\ ~(m2 = bs) /\ ~(m2 = b1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[m1:real^N,bs] INTER segment[bs,b1] = {bs} /\
    segment[bs:real^N,b1] INTER segment[m1,b1] = {b1} /\
    segment[m1:real^N,b1] INTER segment[m1,bs] = {m1} /\
    segment[bs:real^N,m2] INTER segment[bs,b1] = {bs} /\
    segment[bs:real^N,b1] INTER segment[b1,m2] = {b1} /\
    segment[b1:real^N,m2] INTER segment[bs,m2] = {m2}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`; `b1:real^N`] MOI_FSA_TRI_EDGES) THEN
    MP_TAC(ISPECL [`m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FSA_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[b1:real^N,m1] = segment[m1,b1] /\
                  segment[m2:real^N,bs] = segment[bs,m2]`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[m1:real^N,bs] SUBSET convex hull {m1,bs,b1} /\
    segment[m1:real^N,b1] SUBSET convex hull {m1,bs,b1} /\
    segment[bs:real^N,b1] SUBSET convex hull {m1,bs,b1} /\
    segment[bs:real^N,m2] SUBSET convex hull {m2,bs,b1} /\
    segment[b1:real^N,m2] SUBSET convex hull {m2,bs,b1}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(m1:real^N) IN segment[m1,bs] /\ bs IN segment[m1,bs] /\ m1 IN segment[m1,b1] /\
    b1 IN segment[m1,b1] /\ bs IN segment[bs,m2] /\ m2 IN segment[bs,m2] /\
    b1 IN segment[b1,m2] /\ m2 IN segment[b1,m2]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m1:real^N = m2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(m1:real^N) IN segment[bs,b1]` MP_TAC THENL
     [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `segment[bs:real^N,b1]`)) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
      ASM_REWRITE_TAC[IN_INSERT];
      DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,bs,b1}` THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SET_RULE `{a:real^N,b,c} = {b,c,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR; GSYM BETWEEN_IN_SEGMENT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The wedge trace Q on the link and its complement Q' are 2-cells with the *)
(* common boundary circle J = As UNION AF.                                   *)

let MOI_FTC_AB_Q = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 2
           (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})
           ((segment[m1,bs] UNION segment[bs,m2]) UNION
            (segment[m1,b1] UNION segment[b1,m2])) /\
         pl_cell_with_boundary 2
           ((L DIFF (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})) UNION
            ((segment[m1,bs] UNION segment[bs,m2]) UNION
             (segment[m1,b1] UNION segment[b1,m2])))
           ((segment[m1,bs] UNION segment[bs,m2]) UNION
            (segment[m1,b1] UNION segment[b1,m2])) /\
         pl_sphere 1 ((segment[m1,bs] UNION segment[bs,m2]) UNION
                      (segment[m1,b1] UNION segment[b1,m2]))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_abl; moi_ftc_rad] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2
      (convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1})
      ((segment[m1,bs] UNION segment[bs,m2]) UNION (segment[m1,b1] UNION segment[b1,m2]))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_Q_CELL) THEN
    ASM_REWRITE_TAC[UNION_ACI];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_DISK_COMPLEMENT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`1`; `convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}`;
                   `(segment[m1:real^N,bs] UNION segment[bs,m2]) UNION
                    (segment[m1,b1] UNION segment[b1,m2])`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let MOI_FTC_AB_SWAP = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> moi_ftc_abl v L X Y Z m2 m1 bs b1 G2 G1 R2 R1 Fg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_abl] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The corner of the dual disk G1 on the wedge trace. *)

let MOI_FTC_AB_G = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> ~collinear {m1, midpoint(m1,bs), midpoint(m1,b1)} /\
         convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} SUBSET G1 /\
         G1 INTER (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) =
         convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} /\
         R1 INTER (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) =
         segment[midpoint(m1,bs), midpoint(m1,b1)] /\
         G1 INTER (segment[m1,bs] UNION segment[bs,m2]) = segment[m1,midpoint(m1,bs)] /\
         G1 INTER (segment[m1,b1] UNION segment[b1,m2]) = segment[m1,midpoint(m1,b1)] /\
         R1 INTER (segment[m1,bs] UNION segment[bs,m2]) = {midpoint(m1,bs)} /\
         R1 INTER (segment[m1,b1] UNION segment[b1,m2]) = {midpoint(m1,b1)} /\
         m1 IN G1 /\ ~(m1 IN R1) /\ midpoint(m1,bs) IN R1 /\ midpoint(m1,b1) IN R1 /\
         ~(bs IN G1) /\ ~(b1 IN G1) /\ R1 SUBSET G1 /\ G1 SUBSET L /\ G1 SUBSET X`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_TWO_TRI o
    (fun th -> let c = CONJUNCTS (REWRITE_RULE[moi_ftc_abl] th) in
               end_itlist CONJ (map (fun i -> el i c) [3;4;5]))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_CORNER_GEOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p1 = midpoint(m1:real^N,bs)` THEN
  ABBREV_TAC `q1 = midpoint(m1:real^N,b1)` THEN
  SUBGOAL_THEN `R1 SUBSET (G1:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (G1:real^N->bool) R1`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN convex hull {m1,p1,q1} /\ p1 IN convex hull {m1,p1,q1} /\
                q1 IN convex hull {m1,p1,q1} /\ segment[p1,q1] SUBSET convex hull {m1,p1,q1}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(bs:real^N IN convex hull {m1,p1,q1}) /\ ~(b1 IN convex hull {m1,p1,q1})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`bs:real^N`; `b1:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {m1:real^N,p1,q1} INTER (segment[bs,m2] UNION segment[b1,m2]) = {}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN segment[m1,bs] /\ (p1:real^N) IN segment[p1,q1] /\
                (q1:real^N) IN segment[p1,q1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m1:real^N = p1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,p1,q1}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM SET_TAC[]) THEN
  UNDISCH_TAC `X:real^N->bool = Z UNION Y INTER L` THEN
  UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[]);;

(* The two 3-cells of the block: the level region over Q and over Q'. *)

let MOI_FTC_AB_W = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 3
           (Y INTER moi_ftc_cone v (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}))
           ((X INTER moi_ftc_cone v
               (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})) UNION
            (Y INTER moi_ftc_cone v ((segment[m1,bs] UNION segment[bs,m2]) UNION
                                     (segment[m1,b1] UNION segment[b1,m2])))) /\
         pl_cell_with_boundary 3
           (Y INTER moi_ftc_cone v
              ((L DIFF (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})) UNION
               ((segment[m1,bs] UNION segment[bs,m2]) UNION
                (segment[m1,b1] UNION segment[b1,m2]))))
           ((X INTER moi_ftc_cone v
              ((L DIFF (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1})) UNION
               ((segment[m1,bs] UNION segment[bs,m2]) UNION
                (segment[m1,b1] UNION segment[b1,m2])))) UNION
            (Y INTER moi_ftc_cone v ((segment[m1,bs] UNION segment[bs,m2]) UNION
                                     (segment[m1,b1] UNION segment[b1,m2]))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  ABBREV_TAC `Q = convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}` THEN
  ABBREV_TAC `J = (segment[m1:real^N,bs] UNION segment[bs,m2]) UNION
                  (segment[m1,b1] UNION segment[b1,m2])` THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_SECTOR3 THEN
  MAP_EVERY EXISTS_TAC [`L:real^N->bool`] THENL
   [EXISTS_TAC `(L DIFF Q) UNION (J:real^N->bool)`;
    EXISTS_TAC `Q:real^N->bool`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* The two fins of the block and the core arc. *)

let MOI_FTC_AB_R = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 1
           (X INTER moi_ftc_cone v (segment[m1,bs] UNION segment[bs,m2])) {m1,m2} /\
         pl_cell_with_boundary 2
           (Y INTER moi_ftc_cone v (segment[m1,bs] UNION segment[bs,m2]))
           ((X INTER moi_ftc_cone v (segment[m1,bs] UNION segment[bs,m2])) UNION
            segment[v,m1] UNION segment[v,m2]) /\
         pl_cell_with_boundary 1
           (X INTER moi_ftc_cone v (segment[m1,b1] UNION segment[b1,m2])) {m1,m2} /\
         pl_cell_with_boundary 2
           (Y INTER moi_ftc_cone v (segment[m1,b1] UNION segment[b1,m2]))
           ((X INTER moi_ftc_cone v (segment[m1,b1] UNION segment[b1,m2])) UNION
            segment[v,m1] UNION segment[v,m2]) /\
         pl_cell_with_boundary 1 (segment[v,m1] UNION segment[v,m2]) {m1,m2} /\
         Y INTER moi_ftc_cone v {m1,m2} = segment[v,m1] UNION segment[v,m2]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G o MATCH_MP MOI_FTC_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  MP_TAC(ISPECL [`m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_TWO_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_polyhedron (segment[m1:real^N,bs] UNION segment[bs,m2]) /\
    pl_polyhedron (segment[m1:real^N,b1] UNION segment[b1,m2])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(segment[m1:real^N,bs] UNION segment[bs,m2]) UNION
    (segment[m1,b1] UNION segment[b1,m2]) SUBSET L`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(bs:real^N) IN segment[m1,bs] /\ (b1:real^N) IN segment[m1,b1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN X /\ (m2:real^N) IN X /\ m1 IN L /\ m2 IN L`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `segment[m1:real^N,bs] UNION segment[bs,m2]`;
                 `segment[m1:real^N,b1] UNION segment[b1,m2]`; `m1:real^N`; `m2:real^N`]
    MOI_FTC_SECTOR2) THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `segment[m1:real^N,b1] UNION segment[b1,m2]`;
                 `segment[m1:real^N,bs] UNION segment[bs,m2]`; `m1:real^N`; `m2:real^N`]
    MOI_FTC_SECTOR2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN REWRITE_TAC[moi_ftc_cone] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    STRIP_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN ASM SET_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `UNIONS {segment[v:real^N,y] | y | y IN {m1,m2}} = segment[v,m1] UNION segment[v,m2]`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_FTC_CONE_PAIR]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET y ==> y INTER s = s`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `Y:real^N->bool`)) THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]] THEN
  (* the core arc from the boundary circle of the fin *)
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC
   [`(X INTER UNIONS {segment[v:real^N,y] | y | y IN segment[m1,bs] UNION segment[bs,m2]})
     UNION segment[v,m1] UNION segment[v,m2]`;
    `X INTER UNIONS {segment[v:real^N,y] | y | y IN segment[m1,bs] UNION segment[bs,m2]}`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`;
      `Y INTER UNIONS {segment[v:real^N,y] | y | y IN segment[m1,bs] UNION segment[bs,m2]}`;
      `(X INTER UNIONS {segment[v:real^N,y] | y | y IN segment[m1,bs] UNION segment[bs,m2]})
       UNION segment[v,m1] UNION segment[v,m2]`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SET_TAC[];
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`1`; `{m1:real^N,m2}`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSED_UNION THEN REWRITE_TAC[CLOSED_SEGMENT];
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `m1:real^N`]
      MOI_FTC_X_SEG) THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `m2:real^N`]
      MOI_FTC_X_SEG) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(m1:real^N) IN UNIONS {segment[v,y] | y | y IN segment[m1,bs] UNION
                                                             segment[bs,m2]} /\
                  (m2:real^N) IN UNIONS {segment[v,y] | y | y IN segment[m1,bs] UNION
                                                             segment[bs,m2]}`
    MP_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THENL
       [EXISTS_TAC `segment[v:real^N,m1]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        EXISTS_TAC `m1:real^N` THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
        EXISTS_TAC `segment[v:real^N,m2]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        EXISTS_TAC `m2:real^N` THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `m1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`v:real^N`; `m2:real^N`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `(m1:real^N) IN X` THEN UNDISCH_TAC `(m2:real^N) IN X` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_FTC_CELL_NOT_SUBSET THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `v:real^N` THEN
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]);;

let MOI_FTC_AB_X = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> X INTER moi_ftc_cone v (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) =
         (Z INTER moi_ftc_cone v (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}))
         UNION convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)}
         UNION convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)} /\
         X INTER moi_ftc_cone v ((segment[m1,bs] UNION segment[bs,m2]) UNION
                                 (segment[m1,b1] UNION segment[b1,m2])) =
         (Z INTER moi_ftc_cone v ((segment[m1,bs] UNION segment[bs,m2]) UNION
                                  (segment[m1,b1] UNION segment[b1,m2])))
         UNION (segment[m1,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)])
         UNION (segment[m2,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)]) /\
         Z INTER convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} =
         segment[midpoint(m1,bs), midpoint(m1,b1)] /\
         Z INTER convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)} =
         segment[midpoint(m2,bs), midpoint(m2,b1)] /\
         Z INTER (segment[m1,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)]) =
         {midpoint(m1,bs), midpoint(m1,b1)} /\
         Z INTER (segment[m2,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)]) =
         {midpoint(m2,bs), midpoint(m2,b1)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G o MATCH_MP MOI_FTC_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  MP_TAC(ISPECL [`m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_TWO_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_CORNER_GEOM) THEN
  MP_TAC(ISPECL [`m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_CORNER_GEOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}` THEN
  ABBREV_TAC `Q2 = convex hull {m2:real^N,bs,b1} UNION convex hull {m1,bs,b1}` THEN
  SUBGOAL_THEN `Q2:real^N->bool = Q` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "Q2"] THEN REWRITE_TAC[UNION_COMM]; ALL_TAC] THEN
  ABBREV_TAC `J = (segment[m1:real^N,bs] UNION segment[bs,m2]) UNION
                  (segment[m1,b1] UNION segment[b1,m2])` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q /\ Q SUBSET L` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) Q = Q /\ L INTER moi_ftc_cone v J = J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[midpoint(m1:real^N,bs),midpoint(m1,b1)] SUBSET
      convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} /\
    segment[midpoint(m2:real^N,bs),midpoint(m2,b1)] SUBSET
      convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)} /\
    segment[m1:real^N,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)] SUBSET
      convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} /\
    segment[m2:real^N,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)] SUBSET
      convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) INTER L INTER Q =
                convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)} UNION
                convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER Q = convex hull {m1, midpoint(m1,bs), midpoint(m1,b1)}` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER Q = convex hull {m2, midpoint(m2,bs), midpoint(m2,b1)}` THEN
    UNDISCH_TAC `(Fg:real^N->bool) INTER Q = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G1:real^N->bool) INTER J = segment[m1,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)] /\
    (G2:real^N->bool) INTER J = segment[m2,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)] /\
    (Fg:real^N->bool) INTER J = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[UNION_OVER_INTER] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `J:real^N->bool = (segment[m2,bs] UNION segment[bs,m1]) UNION
                                     (segment[m2,b1] UNION segment[b1,m1])`
      SUBST1_TAC THENL
       [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT1 SEGMENT_SYM] THEN
        REWRITE_TAC[UNION_ACI];
        ONCE_REWRITE_TAC[UNION_OVER_INTER] THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `(Fg:real^N->bool) INTER Q = {}` THEN
      UNDISCH_TAC `(J:real^N->bool) SUBSET Q` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) INTER L INTER J =
                (segment[m1,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)]) UNION
                (segment[m2,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)])`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTER_ASSOC] THEN
    UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER J =
                 segment[m1,midpoint(m1,bs)] UNION segment[m1,midpoint(m1,b1)]` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER J =
                 segment[m2,midpoint(m2,bs)] UNION segment[m2,midpoint(m2,b1)]` THEN
    UNDISCH_TAC `(Fg:real^N->bool) INTER J = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X Z Y L C Q H:real^N->bool.
      X = Z UNION (Y INTER L) /\ L INTER C = Q /\ Y INTER L INTER Q = H
      ==> X INTER C = (Z INTER C) UNION H`
  (LABEL_TAC "r1") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R Q H TT:real^N->bool.
      Z INTER G = R /\ R INTER Q = TT /\ G INTER Q = H /\ TT SUBSET H /\ R SUBSET G
      ==> Z INTER H = TT`
  (LABEL_TAC "r2") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R A B SA SB p q:real^N.
      Z INTER G = R /\ R SUBSET G /\ G INTER A = SA /\ G INTER B = SB /\
      R INTER A = {p} /\ R INTER B = {q}
      ==> Z INTER (SA UNION SB) = {p,q}`
  (LABEL_TAC "r3") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "r1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `J:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G1:real^N->bool`; `R1:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G2:real^N->bool`; `R2:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G1:real^N->bool`; `R1:real^N->bool`;
                          `segment[m1:real^N,bs] UNION segment[bs,m2]`;
                          `segment[m1:real^N,b1] UNION segment[b1,m2]`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G2:real^N->bool`; `R2:real^N->bool`;
                          `segment[m2:real^N,bs] UNION segment[bs,m1]`;
                          `segment[m2:real^N,b1] UNION segment[b1,m1]`] THEN
    ASM_REWRITE_TAC[]]);;



(* The set identities behind the frontier cell T (abstract). *)

let MOI_FTC_T_SETS = prove
 (`!X XQ XQ' XJ ZQ ZJ H1 H2 A1 A2 t1 t2 P1 P2:real^N->bool.
     X = XQ UNION XQ' /\ XQ INTER XQ' = XJ /\ XQ = ZQ UNION H1 UNION H2 /\
     XJ = ZJ UNION A1 UNION A2 /\
     ZQ INTER H1 = t1 /\ ZQ INTER H2 = t2 /\ ZQ INTER A1 = P1 /\ ZQ INTER A2 = P2 /\
     ZJ INTER A1 = P1 /\ ZJ INTER A2 = P2 /\ ZJ SUBSET ZQ /\
     t1 INTER A1 = P1 /\ t2 INTER A2 = P2 /\ P1 SUBSET t1 /\ P2 SUBSET t2 /\
     A1 SUBSET H1 /\ A2 SUBSET H2 /\ t1 SUBSET H1 /\ t2 SUBSET H2 /\ H1 INTER H2 = {}
     ==> (((XJ UNION A1 UNION t1) DIFF (A1 DIFF P1)) UNION A2 UNION t2) DIFF (A2 DIFF P2) =
         ZJ UNION t1 UNION t2 /\
         (X DIFF ((XQ' UNION H1) UNION H2)) UNION (ZJ UNION t1 UNION t2) = ZQ`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN ASM SET_TAC[]);;

(* The frontier part of the block inside the wedge: T = Z INTER cone(Q) is *)
(* the complement in X of XQ' with the two corner triangles glued on.      *)

let MOI_FTC_AB_T = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 2
           (Z INTER moi_ftc_cone v (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}))
           ((Z INTER moi_ftc_cone v ((segment[m1,bs] UNION segment[bs,m2]) UNION
                                     (segment[m1,b1] UNION segment[b1,m2]))) UNION
            segment[midpoint(m1,bs), midpoint(m1,b1)] UNION
            segment[midpoint(m2,bs), midpoint(m2,b1)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_X) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G o MATCH_MP MOI_FTC_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  MP_TAC(ISPECL [`m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_TWO_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_CORNER_GEOM) THEN
  MP_TAC(ISPECL [`m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_CORNER_GEOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `p1 = midpoint(m1:real^N,bs)` THEN ABBREV_TAC `q1 = midpoint(m1:real^N,b1)` THEN
  ABBREV_TAC `p2 = midpoint(m2:real^N,bs)` THEN ABBREV_TAC `q2 = midpoint(m2:real^N,b1)` THEN
  ABBREV_TAC `Q = convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}` THEN
  ABBREV_TAC `Q2 = convex hull {m2:real^N,bs,b1} UNION convex hull {m1,bs,b1}` THEN
  SUBGOAL_THEN `Q2:real^N->bool = Q` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "Q2"] THEN REWRITE_TAC[UNION_COMM]; ALL_TAC] THEN
  ABBREV_TAC `As = segment[m1:real^N,bs] UNION segment[bs,m2]` THEN
  ABBREV_TAC `AF = segment[m1:real^N,b1] UNION segment[b1,m2]` THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  ABBREV_TAC `Q' = (L DIFF Q) UNION (J:real^N->bool)` THEN
  ABBREV_TAC `H1 = convex hull {m1:real^N,p1,q1}` THEN
  ABBREV_TAC `H2 = convex hull {m2:real^N,p2,q2}` THEN
  ABBREV_TAC `A1 = segment[m1:real^N,p1] UNION segment[m1,q1]` THEN
  ABBREV_TAC `A2 = segment[m2:real^N,p2] UNION segment[m2,q2]` THEN
  FIRST_ASSUM(LABEL_TAC "A1def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `A1:real^N->bool`)) THEN
  FIRST_ASSUM(LABEL_TAC "A2def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `A2:real^N->bool`)) THEN
  (* the G2 facts with the triangle sets in the canonical order *)
  SUBGOAL_THEN
   `(G2:real^N->bool) INTER As = segment[m2,p2] /\ (G2:real^N->bool) INTER AF = segment[m2,q2]`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `As = segment[m2:real^N,bs] UNION segment[bs,m1] /\
                  AF = segment[m2:real^N,b1] UNION segment[b1,m1]`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["As"; "AF"] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN J` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["J"; "As"] THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q INTER Q' = (J:real^N->bool) /\ Q UNION Q' = L /\ ~(Q INTER Q' = {}) /\
                Q' SUBSET L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q'" THEN UNDISCH_TAC `(J:real^N->bool) SUBSET Q` THEN
    UNDISCH_TAC `(Q:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(m1:real^N) IN J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the radial pieces of X over Q' and the cover of X *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (X INTER moi_ftc_cone (v:real^N) Q') (X INTER moi_ftc_cone v J)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_RADIAL_PIECE THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Q INTER Q' = (J:real^N->bool)` THEN
    UNDISCH_TAC `Q UNION Q' = (L:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `X = (X INTER moi_ftc_cone (v:real^N) Q) UNION (X INTER moi_ftc_cone v Q') /\
    (X INTER moi_ftc_cone (v:real^N) Q) INTER (X INTER moi_ftc_cone v Q') =
    X INTER moi_ftc_cone v J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `X SUBSET moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q'`
      MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      SUBGOAL_THEN `moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q' = moi_ftc_cone v L`
      SUBST1_TAC THENL
       [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN
        UNDISCH_TAC `(Q:real^N->bool) UNION Q' = L` THEN DISCH_THEN SUBST1_TAC THEN
        REFL_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[SET_RULE `((x:real^N->bool) INTER a) INTER (x INTER b) = x INTER (a INTER b)`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[moi_ftc_cone] THEN
      MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `Q:real^N->bool`; `Q':real^N->bool`]
        MOI_FTC_CONE_INTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `Q INTER Q' = (J:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
        REFL_TAC]];
    ALL_TAC] THEN
  (* corner triangles: cells, arcs, traces *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 H1 (A1 UNION segment[p1:real^N,q1]) /\
    pl_cell_with_boundary 2 H2 (A2 UNION segment[p2:real^N,q2])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FTC_TRI_CELL) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      EXPAND_TAC "A1";
      MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`; `q2:real^N`] MOI_FTC_TRI_CELL) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      EXPAND_TAC "A2"] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,m1] INTER segment[m1,q1] = {m1} /\
    segment[p2:real^N,m2] INTER segment[m2,q2] = {m2} /\
    ~(p1:real^N = m1) /\ ~(m1:real^N = q1) /\ ~(p2:real^N = m2) /\ ~(m2:real^N = q2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FSA_TRI_EDGES) THEN
    MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`; `q2:real^N`] MOI_FSA_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[p1:real^N,m1] = segment[m1,p1] /\ segment[q1:real^N,m1] = segment[m1,q1] /\
                  segment[p2:real^N,m2] = segment[m2,p2] /\ segment[q2:real^N,m2] = segment[m2,q2]`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`] THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1:real^N,m1] UNION segment[m1,q1] = A1 /\
                segment[p2:real^N,m2] UNION segment[m2,q2] = A2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(A1:real^N->bool) SUBSET H1 /\ (A2:real^N->bool) SUBSET H2 /\
    segment[p1:real^N,q1] SUBSET H1 /\ segment[p2:real^N,q2] SUBSET H2 /\
    {p1:real^N,q1} SUBSET segment[p1,q1] /\ {p2:real^N,q2} SUBSET segment[p2,q2]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H1"; "H2"; "A1"; "A2"] THEN
    REWRITE_TAC[UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H1:real^N->bool) INTER H2 = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `G1 INTER G2:real^N->bool = {}` THEN
    UNDISCH_TAC `(H1:real^N->bool) SUBSET G1` THEN
    UNDISCH_TAC `(H2:real^N->bool) SUBSET G2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H1:real^N->bool) INTER J = A1 /\ (H2:real^N->bool) INTER J = A2`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!G1 G2 H1 H2 J As AF A1 A2 S1 F1 S2 F2:real^N->bool.
        J = As UNION AF /\ G1 INTER As = S1 /\ G1 INTER AF = F1 /\
        G2 INTER As = S2 /\ G2 INTER AF = F2 /\ A1 = S1 UNION F1 /\ A2 = S2 UNION F2 /\
        H1 SUBSET G1 /\ H2 SUBSET G2 /\ A1 SUBSET H1 /\ A2 SUBSET H2
        ==> H1 INTER J = A1 /\ H2 INTER J = A2`) THEN
    MAP_EVERY EXISTS_TAC
     [`G1:real^N->bool`; `G2:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`;
      `segment[m1:real^N,p1]`; `segment[m1:real^N,q1]`;
      `segment[m2:real^N,p2]`; `segment[m2:real^N,q2]`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
      (rhs(concl th) = `A1:real^N->bool` || rhs(concl th) = `A2:real^N->bool`) &&
      can (find_term ((=) `segment[m1:real^N,p1]`)) (concl th) =
      (rhs(concl th) = `A1:real^N->bool`) &&
      not (can (find_term ((=) `segment[p1:real^N,m1]`)) (concl th)) &&
      not (can (find_term ((=) `segment[p2:real^N,m2]`)) (concl th))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(H1:real^N->bool) SUBSET X /\ (H1:real^N->bool) SUBSET L /\ H1 SUBSET Q /\
    (H2:real^N->bool) SUBSET X /\ (H2:real^N->bool) SUBSET L /\ H2 SUBSET Q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(H1:real^N->bool) SUBSET G1` THEN UNDISCH_TAC `(H2:real^N->bool) SUBSET G2` THEN
    UNDISCH_TAC `(G1:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(G2:real^N->bool) SUBSET L` THEN
    UNDISCH_TAC `(G1:real^N->bool) SUBSET X` THEN UNDISCH_TAC `(G2:real^N->bool) SUBSET X` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER Q = H1` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER Q = H2` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `XQ' = X INTER moi_ftc_cone (v:real^N) Q'` THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) Q' = Q'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `XQ' INTER H1 = (A1:real^N->bool) /\ XQ' INTER H2 = (A2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!X C L Q Q' J H1 H2 A1 A2 XQ':real^N->bool.
        XQ' = X INTER C /\ L INTER C = Q' /\ Q' = (L DIFF Q) UNION J /\
        H1 SUBSET X /\ H1 SUBSET L /\ H1 SUBSET Q /\ H1 INTER J = A1 /\
        H2 SUBSET X /\ H2 SUBSET L /\ H2 SUBSET Q /\ H2 INTER J = A2
        ==> XQ' INTER H1 = A1 /\ XQ' INTER H2 = A2`) THEN
    MAP_EVERY EXISTS_TAC
     [`X:real^N->bool`; `moi_ftc_cone (v:real^N) Q'`; `L:real^N->bool`;
      `Q:real^N->bool`; `Q':real^N->bool`; `J:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (XQ':real^N->bool)
      ((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `pl_cell_with_boundary 2 (XQ':real^N->bool) (X INTER moi_ftc_cone v J)`)) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `X INTER moi_ftc_cone (v:real^N) J`));
    ALL_TAC] THEN
  (* glue H1, then H2 *)
  MP_TAC(ISPECL [`XQ':real^N->bool`; `((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`; `H1:real^N->bool`;
                 `A1 UNION segment[p1:real^N,q1]`; `p1:real^N`; `m1:real^N`; `q1:real^N`]
    MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`XQ' UNION H1:real^N->bool`;
                 `(((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2) UNION A1 UNION segment[p1:real^N,q1]) DIFF (A1 DIFF {p1,q1})`;
                 `H2:real^N->bool`; `A2 UNION segment[p2:real^N,q2]`;
                 `p2:real^N`; `m2:real^N`; `q2:real^N`] MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `XQ' INTER H2 = (A2:real^N->bool)` THEN
      UNDISCH_TAC `(H1:real^N->bool) INTER H2 = {}` THEN SET_TAC[];
      UNDISCH_TAC `(H1:real^N->bool) INTER H2 = {}` THEN
      UNDISCH_TAC `(A1:real^N->bool) SUBSET H1` THEN
      UNDISCH_TAC `(A2:real^N->bool) SUBSET H2` THEN SET_TAC[];
      SET_TAC[]];
    DISCH_TAC] THEN
  (* the complement in the sphere X *)
  MP_TAC(ISPECL [`X:real^N->bool`; `(XQ' UNION H1) UNION H2:real^N->bool`;
    `(((((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2) UNION A1 UNION segment[p1:real^N,q1]) DIFF (A1 DIFF {p1,q1})) UNION
      A2 UNION segment[p2,q2]) DIFF (A2 DIFF {p2,q2})`] MOI_FTC_DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "XQ'" THEN UNDISCH_TAC `(H1:real^N->bool) SUBSET X` THEN
      UNDISCH_TAC `(H2:real^N->bool) SUBSET X` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* identification *)
  SUBGOAL_THEN
   `(H1:real^N->bool) SUBSET moi_ftc_cone v Q /\ (H2:real^N->bool) SUBSET moi_ftc_cone v Q /\
    (A1:real^N->bool) SUBSET moi_ftc_cone v J /\ (A2:real^N->bool) SUBSET moi_ftc_cone v J /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!P:real^N->bool. P SUBSET moi_ftc_cone v P` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[moi_ftc_cone; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q` ASSUME_TAC THENL
     [REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(A1:real^N->bool) SUBSET J /\ (A2:real^N->bool) SUBSET J`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(H1:real^N->bool) INTER J = A1` THEN
      UNDISCH_TAC `(H2:real^N->bool) INTER J = A2` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,q1] INTER A1 = {p1,q1} /\ segment[p2:real^N,q2] INTER A2 = {p2,q2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `segment[m1:real^N,p1] SUBSET segment[m1,bs] /\ segment[m1:real^N,q1] SUBSET segment[m1,b1] /\
      segment[m2:real^N,p2] SUBSET segment[m2,bs] /\ segment[m2:real^N,q2] SUBSET segment[m2,b1]`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p1"; "q1"; "p2"; "q2"] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!TT S1 S2 B1 B2:real^N->bool p q.
        TT INTER B1 = {p} /\ TT INTER B2 = {q} /\ S1 SUBSET B1 /\ S2 SUBSET B2 /\
        p IN TT /\ q IN TT /\ p IN S1 /\ q IN S2
        ==> TT INTER (S1 UNION S2) = {p,q}`
    (LABEL_TAC "pq") THENL [SET_TAC[]; ALL_TAC] THEN
    USE_THEN "A1def" (SUBST1_TAC o SYM) THEN USE_THEN "A2def" (SUBST1_TAC o SYM) THEN
    CONJ_TAC THEN USE_THEN "pq" MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`segment[m1:real^N,bs]`; `segment[m1:real^N,b1]`];
      MAP_EVERY EXISTS_TAC [`segment[m2:real^N,bs]`; `segment[m2:real^N,b1]`]] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `X INTER moi_ftc_cone (v:real^N) Q`; `XQ':real^N->bool`;
    `((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`; `Z INTER moi_ftc_cone (v:real^N) Q`;
    `Z INTER moi_ftc_cone (v:real^N) J`; `H1:real^N->bool`; `H2:real^N->bool`;
    `A1:real^N->bool`; `A2:real^N->bool`; `segment[p1:real^N,q1]`;
    `segment[p2:real^N,q2]`; `{p1:real^N,q1}`; `{p2:real^N,q2}`] MOI_FTC_T_SETS) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!Z C S P:real^N->bool. Z INTER S = P /\ S SUBSET C ==> (Z INTER C) INTER S = P`
  (LABEL_TAC "zc") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(USE_THEN "zc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_ftc_cone (v:real^N) J` THEN
          ASM_REWRITE_TAC[]) THEN NO_TAC) THEN
  UNDISCH_TAC `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q` THEN SET_TAC[]);;

(* The set identities behind the frontier cell B outside the wedge. *)

let MOI_FTC_B_SETS = prove
 (`!X XQ XQ' T H1 H2 G1 G2 GQ1 GQ2 ZQ' Fg ZJ t1 t2 K1 K2 R1 R2 P1 P2:real^N->bool.
     X = XQ UNION XQ' /\ XQ = T UNION H1 UNION H2 /\
     XQ' = ZQ' UNION GQ1 UNION GQ2 UNION Fg /\
     H1 SUBSET G1 /\ H2 SUBSET G2 /\ GQ1 SUBSET G1 /\ GQ2 SUBSET G2 /\
     T INTER ZQ' = ZJ /\ ZQ' INTER G1 = K1 /\ ZQ' INTER G2 = K2 /\
     Fg INTER T = {} /\ Fg INTER G1 = {} /\ Fg INTER G2 = {} /\
     ZJ SUBSET ZQ' /\ K1 SUBSET ZQ' /\ K2 SUBSET ZQ' /\
     R1 = t1 UNION K1 /\ R2 = t2 UNION K2 /\ t1 INTER K1 = P1 /\ t2 INTER K2 = P2 /\
     ZJ INTER t1 = P1 /\ ZJ INTER t2 = P2 /\ t1 SUBSET G1 /\ t2 SUBSET G2 /\
     K1 SUBSET G1 /\ K2 SUBSET G2 /\ G1 INTER G2 = {}
     ==> ((((ZJ UNION t1 UNION t2) UNION R1) DIFF (t1 DIFF P1)) UNION R2) DIFF (t2 DIFF P2) =
         ZJ UNION K1 UNION K2 /\
         (X DIFF ((T UNION G1) UNION G2)) UNION (ZJ UNION K1 UNION K2) = ZQ' UNION Fg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The abstract block, part 2.  Set facts of the block under                 *)
(* explicit abbreviations (Q, As, AF, J, Q', p_i, q_i), the frontier arcs    *)
(* alpha = Z INTER cone As and beta = Z INTER cone AF, the frontier cell B   *)
(* outside the wedge, and the cells of the dual disk G1.                    *)
(* ========================================================================= *)

let MOI_FTC_AB_F1 = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> Q INTER Q' = J /\ Q UNION Q' = L /\ J SUBSET Q /\ J SUBSET Q' /\
         Q SUBSET L /\ Q' SUBSET L /\ J SUBSET L /\ As SUBSET J /\ AF SUBSET J /\
         As SUBSET L /\ AF SUBSET L /\
         As INTER AF = {m1,m2} /\ bs IN As /\ b1 IN AF /\ m1 IN J /\ m2 IN J /\
         compact Q /\ compact Q' /\ compact As /\ compact AF /\
         pl_polyhedron As /\ pl_polyhedron AF /\
         pl_cell_with_boundary 2 Q J /\ pl_cell_with_boundary 2 Q' J /\ pl_sphere 1 J /\
         L INTER moi_ftc_cone v Q = Q /\ L INTER moi_ftc_cone v Q' = Q' /\
         L INTER moi_ftc_cone v J = J /\ L INTER moi_ftc_cone v As = As /\
         L INTER moi_ftc_cone v AF = AF /\
         moi_ftc_cone v Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J /\
         moi_ftc_cone v As INTER moi_ftc_cone v AF = segment[v,m1] UNION segment[v,m2] /\
         moi_ftc_cone v As UNION moi_ftc_cone v AF = moi_ftc_cone v J /\
         moi_ftc_cone v J SUBSET moi_ftc_cone v Q /\
         moi_ftc_cone v J SUBSET moi_ftc_cone v Q' /\
         (X INTER moi_ftc_cone v Q) UNION (X INTER moi_ftc_cone v Q') = X /\
         X INTER moi_ftc_cone v Q =
         (Z INTER moi_ftc_cone v Q) UNION convex hull {m1,p1,q1} UNION
         convex hull {m2,p2,q2} /\
         X INTER moi_ftc_cone v Q' =
         (Z INTER moi_ftc_cone v Q') UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg /\
         G1 INTER Q = convex hull {m1,p1,q1} /\ G2 INTER Q = convex hull {m2,p2,q2} /\
         convex hull {m1,p1,q1} SUBSET G1 /\ convex hull {m2,p2,q2} SUBSET G2 /\
         G1 INTER As = segment[m1,p1] /\ G1 INTER AF = segment[m1,q1] /\
         G2 INTER As = segment[m2,p2] /\ G2 INTER AF = segment[m2,q2] /\
         R1 INTER Q = segment[p1,q1] /\ R2 INTER Q = segment[p2,q2] /\
         R1 INTER As = {p1} /\ R1 INTER AF = {q1} /\
         R2 INTER As = {p2} /\ R2 INTER AF = {q2} /\
         Fg INTER Q = {} /\ Fg SUBSET Q' /\ Fg SUBSET L /\
         Fg INTER G1 = {} /\ Fg INTER G2 = {} /\ G1 INTER G2 = {} /\
         ~(p1 = q1) /\ ~(p2 = q2) /\ ~(p1 = p2) /\ ~(q1 = q2) /\ ~(p1 = q2) /\
         ~(q1 = p2) /\ p1 IN R1 /\ q1 IN R1 /\ p2 IN R2 /\ q2 IN R2 /\
         segment[p1,q1] SUBSET R1 /\ segment[p2,q2] SUBSET R2 /\
         R1 SUBSET Z /\ R2 SUBSET Z /\ R1 SUBSET G1 /\ R2 SUBSET G2 /\
         G1 SUBSET L /\ G2 SUBSET L /\ G1 SUBSET X /\ G2 SUBSET X /\ Z SUBSET X /\
         pl_cell_with_boundary 2 G1 R1 /\ pl_cell_with_boundary 2 G2 R2 /\
         ~(bs IN G1) /\ ~(bs IN G2) /\ ~(b1 IN G1) /\ ~(b1 IN G2) /\
         bs IN L /\ b1 IN L /\ ~(bs IN Fg) /\ ~(b1 IN Fg) /\
         m1 IN G1 /\ m2 IN G2 /\ ~(m1 IN Z) /\ ~(m2 IN Z) /\ m1 IN L /\ m2 IN L /\
         m1 IN X /\ m2 IN X /\ ~collinear {m1,p1,q1} /\ ~collinear {m2,p2,q2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_X) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_G o MATCH_MP MOI_FTC_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `X:real^N->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Y:real^N->bool`)) THEN
  MP_TAC(ISPECL [`m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_TWO_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `p1 = midpoint(m1:real^N,bs)` THEN ABBREV_TAC `q1 = midpoint(m1:real^N,b1)` THEN
  ABBREV_TAC `p2 = midpoint(m2:real^N,bs)` THEN ABBREV_TAC `q2 = midpoint(m2:real^N,b1)` THEN
  ABBREV_TAC `Q = convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}` THEN
  ABBREV_TAC `Q2 = convex hull {m2:real^N,bs,b1} UNION convex hull {m1,bs,b1}` THEN
  SUBGOAL_THEN `Q2:real^N->bool = Q` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "Q2"] THEN REWRITE_TAC[UNION_COMM]; ALL_TAC] THEN
  ABBREV_TAC `As = segment[m1:real^N,bs] UNION segment[bs,m2]` THEN
  ABBREV_TAC `AF = segment[m1:real^N,b1] UNION segment[b1,m2]` THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  ABBREV_TAC `Q' = (L DIFF Q) UNION (J:real^N->bool)` THEN
  FIRST_ASSUM(LABEL_TAC "Q'def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `Q':real^N->bool`)) THEN
  SUBGOAL_THEN
   `(G2:real^N->bool) INTER As = segment[m2,p2] /\ (G2:real^N->bool) INTER AF = segment[m2,q2] /\
    (R2:real^N->bool) INTER As = {p2} /\ (R2:real^N->bool) INTER AF = {q2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `As = segment[m2:real^N,bs] UNION segment[bs,m1] /\
                  AF = segment[m2:real^N,b1] UNION segment[b1,m1]`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["As"; "AF"] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN J /\ (m2:real^N) IN J /\ (bs:real^N) IN As /\ (b1:real^N) IN AF /\
                As SUBSET (J:real^N->bool) /\ AF SUBSET (J:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN MAP_EVERY EXPAND_TAC ["As"; "AF"] THEN
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q INTER Q' = (J:real^N->bool) /\ Q UNION Q' = L /\ Q' SUBSET L /\ J SUBSET Q' /\
                (J:real^N->bool) SUBSET L /\ (As:real^N->bool) SUBSET L /\
                (AF:real^N->bool) SUBSET L`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Q'def" (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(J:real^N->bool) SUBSET Q`; `(Q:real^N->bool) SUBSET L`;
                           `(As:real^N->bool) SUBSET J`; `(AF:real^N->bool) SUBSET J`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (As:real^N->bool) /\ pl_polyhedron (AF:real^N->bool) /\
                compact (As:real^N->bool) /\ compact (AF:real^N->bool) /\
                compact (Q:real^N->bool) /\ compact (Q':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "As" THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
      EXPAND_TAC "AF" THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
      EXPAND_TAC "As" THEN MATCH_MP_TAC COMPACT_UNION THEN REWRITE_TAC[COMPACT_SEGMENT];
      EXPAND_TAC "AF" THEN MATCH_MP_TAC COMPACT_UNION THEN REWRITE_TAC[COMPACT_SEGMENT];
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC [`2`; `J:real^N->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC [`2`; `J:real^N->bool`] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `L INTER moi_ftc_cone (v:real^N) Q = Q /\ L INTER moi_ftc_cone v Q' = Q' /\
    L INTER moi_ftc_cone v J = J /\ L INTER moi_ftc_cone v As = As /\
    L INTER moi_ftc_cone v AF = AF`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `Q:real^N->bool`; `Q':real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `m1:real^N` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) As INTER moi_ftc_cone v AF = segment[v,m1] UNION segment[v,m2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[MOI_FTC_CONE_PAIR]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_ftc_cone; MOI_FTC_CONE_UNION];
      REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X INTER moi_ftc_cone (v:real^N) Q) UNION (X INTER moi_ftc_cone v Q') = X`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `X SUBSET moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q'`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN `moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q' = moi_ftc_cone v L`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN
      UNDISCH_TAC `(Q:real^N->bool) UNION Q' = L` THEN DISCH_THEN SUBST1_TAC THEN
      REFL_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fg:real^N->bool) SUBSET L /\ Fg SUBSET Q' /\ Fg INTER G1 = {} /\
                Fg INTER G2 = {}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Q'def" (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg`;
                           `(Fg:real^N->bool) INTER Q = {}`;
                           `(Fg:real^N->bool) INTER (G1 UNION G2) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `X INTER moi_ftc_cone (v:real^N) Q' =
    (Z INTER moi_ftc_cone v Q') UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!X Z Y L C Q' G1 G2 Fg:real^N->bool.
        Z UNION (Y INTER L) = X /\ L INTER C = Q' /\ Y INTER L = G1 UNION G2 UNION Fg /\
        Fg SUBSET Q'
        ==> X INTER C = (Z INTER C) UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg`) THEN
    EXISTS_TAC `Y:real^N->bool` THEN EXISTS_TAC `L:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:real^N = q1) /\ ~(p2:real^N = q2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`] THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:real^N = p2) /\ ~(q1:real^N = q2) /\ ~(p1:real^N = q2) /\
                ~(q1:real^N = p2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `(G1:real^N->bool) INTER G2 = {}`; `(p1:real^N) IN R1`; `(q1:real^N) IN R1`;
      `(p2:real^N) IN R2`; `(q2:real^N) IN R2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,q1] SUBSET R1 /\ segment[p2:real^N,q2] SUBSET R2 /\
    (R1:real^N->bool) SUBSET Z /\ (R2:real^N->bool) SUBSET Z /\ (Z:real^N->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`; `(Z:real^N->bool) INTER G1 = R1`;
      `(Z:real^N->bool) INTER G2 = R2`; `Z UNION Y INTER L = (X:real^N->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(bs:real^N) IN L /\ (b1:real^N) IN L /\ ~(bs IN Fg) /\ ~(b1 IN Fg)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(bs:real^N) IN As`; `(b1:real^N) IN AF`;
      `(As:real^N->bool) SUBSET J`; `(AF:real^N->bool) SUBSET J`;
      `(J:real^N->bool) SUBSET Q`; `(Q:real^N->bool) SUBSET L`;
      `(Fg:real^N->bool) INTER Q = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((m1:real^N) IN Z) /\ ~((m2:real^N) IN Z) /\ (m1:real^N) IN L /\ (m2:real^N) IN L /\
    (m1:real^N) IN X /\ (m2:real^N) IN X`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(m1:real^N) IN G1`; `(m2:real^N) IN G2`;
      `~((m1:real^N) IN R1)`; `~((m2:real^N) IN R2)`; `(Z:real^N->bool) INTER G1 = R1`;
      `(Z:real^N->bool) INTER G2 = R2`; `(G1:real^N->bool) SUBSET L`;
      `(G2:real^N->bool) SUBSET L`; `(G1:real^N->bool) SUBSET X`;
      `(G2:real^N->bool) SUBSET X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)));;

(* A point of the frontier set Z on the ray through a link point b off the  *)
(* two dual disks and the fingers.                                          *)

let MOI_FTC_ZRAY_POINT = prove
 (`!(v:real^N) L X Y Z G1 G2 Fg A b p1 p2.
     moi_ftc_rad v L X Y /\ X = Z UNION (Y INTER L) /\ Z SUBSET Y /\
     Y INTER L = G1 UNION G2 UNION Fg /\
     b IN A /\ b IN L /\ ~(b IN G1) /\ ~(b IN G2) /\ ~(b IN Fg) /\
     p1 IN G1 /\ p2 IN G2 /\ G1 SUBSET L /\ G2 SUBSET L
     ==> ~(Z INTER moi_ftc_cone v A SUBSET {p1,p2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_rad] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN `~(b:real^N IN X)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`Z UNION Y INTER L = (X:real^N->bool)`; `(Z:real^N->bool) SUBSET Y`;
      `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg`; `(b:real^N) IN L`;
      `~((b:real^N) IN G1)`; `~((b:real^N) IN G2)`; `~((b:real^N) IN Fg)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "?!" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
  SUBGOAL_THEN `(v + r % (b - v):real^N) IN segment[v,b]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `r:real` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v + r % (b - v):real^N) IN L)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `v + r % (b - v):real^N = b` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L:real^N->bool`)) (concl th) &&
        not(can (find_term ((=) `X:real^N->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`~(b:real^N IN X)`; `(v + r % (b - v):real^N) IN X`;
                           `v + r % (b - v):real^N = b`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v + r % (b - v):real^N) IN moi_ftc_cone v A` ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_IN_CONE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `v + r % (b - v):real^N` THEN
  MAP_EVERY UNDISCH_TAC [`(v + r % (b - v):real^N) IN X`; `~((v + r % (b - v):real^N) IN L)`;
    `(v + r % (b - v):real^N) IN moi_ftc_cone v A`;
    `Z UNION Y INTER L = (X:real^N->bool)`; `(p1:real^N) IN G1`; `(p2:real^N) IN G2`;
    `(G1:real^N->bool) SUBSET L`; `(G2:real^N->bool) SUBSET L`] THEN
  SPEC_TAC(`v + r % (b - v):real^N`,`x:real^N`) THEN SET_TAC[]);;

(* Facts about the frontier set Z in the block. *)

let MOI_FTC_AB_F2 = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> pl_cell_with_boundary 2 (Z INTER moi_ftc_cone v Q)
           ((Z INTER moi_ftc_cone v J) UNION segment[p1,q1] UNION segment[p2,q2]) /\
         segment[p1,q1] UNION (R1 INTER Q') = R1 /\
         segment[p2,q2] UNION (R2 INTER Q') = R2 /\
         segment[p1,q1] INTER (R1 INTER Q') = {p1,q1} /\
         segment[p2,q2] INTER (R2 INTER Q') = {p2,q2} /\
         segment[p1,q1] INTER J = {p1,q1} /\ segment[p2,q2] INTER J = {p2,q2} /\
         segment[p1,q1] INTER As = {p1} /\ segment[p1,q1] INTER AF = {q1} /\
         segment[p2,q2] INTER As = {p2} /\ segment[p2,q2] INTER AF = {q2} /\
         p1 IN G1 /\ q1 IN G1 /\ p2 IN G2 /\ q2 IN G2 /\
         segment[p1,q1] SUBSET Z /\ segment[p2,q2] SUBSET Z /\
         segment[p1,q1] SUBSET L /\ segment[p2,q2] SUBSET L /\
         R1 SUBSET L /\ R2 SUBSET L /\
         (Z INTER moi_ftc_cone v Q) INTER G1 = segment[p1,q1] /\
         (Z INTER moi_ftc_cone v Q) INTER G2 = segment[p2,q2] /\
         (Z INTER moi_ftc_cone v Q') INTER G1 = R1 INTER Q' /\
         (Z INTER moi_ftc_cone v Q') INTER G2 = R2 INTER Q' /\
         (Z INTER moi_ftc_cone v J) INTER segment[p1,q1] = {p1,q1} /\
         (Z INTER moi_ftc_cone v J) INTER segment[p2,q2] = {p2,q2} /\
         segment[p1,q1] INTER (Z INTER moi_ftc_cone v As) = {p1} /\
         segment[p1,q1] INTER (Z INTER moi_ftc_cone v AF) = {q1} /\
         segment[p2,q2] INTER (Z INTER moi_ftc_cone v As) = {p2} /\
         segment[p2,q2] INTER (Z INTER moi_ftc_cone v AF) = {q2} /\
         (Z INTER moi_ftc_cone v As) INTER (Z INTER moi_ftc_cone v AF) = {} /\
         ~(Z INTER moi_ftc_cone v As SUBSET {p1,p2}) /\
         ~(Z INTER moi_ftc_cone v AF SUBSET {q1,q2}) /\
         Fg INTER (Z INTER moi_ftc_cone v Q) = {} /\
         Z INTER moi_ftc_cone v J SUBSET Z INTER moi_ftc_cone v Q /\
         Z INTER moi_ftc_cone v J SUBSET Z INTER moi_ftc_cone v Q' /\
         (Z INTER moi_ftc_cone v Q) INTER (Z INTER moi_ftc_cone v Q') =
         Z INTER moi_ftc_cone v J /\
         (Z INTER moi_ftc_cone v As) UNION (Z INTER moi_ftc_cone v AF) =
         Z INTER moi_ftc_cone v J /\
         closed (Z INTER moi_ftc_cone v As) /\ closed (Z INTER moi_ftc_cone v AF)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c and defs = tl c in
    ASSUME_TAC abl THEN STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th) THEN
    ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTC_AB_T abl)) THEN
    ASSUME_TAC(SYM(el 3 defs))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN `(R1:real^N->bool) SUBSET L /\ (R2:real^N->bool) SUBSET L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `G1:real^N->bool`; EXISTS_TAC `G2:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] UNION (R1 INTER Q') = (R1:real^N->bool) /\
                segment[p2,q2] UNION (R2 INTER Q') = (R2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) SUBSET L`; `(R2:real^N->bool) SUBSET L`;
      `Q UNION Q' = (L:real^N->bool)`;
      `(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1,q1] INTER As = {p1:real^N} /\ segment[p1,q1] INTER AF = {q1:real^N} /\
    segment[p2,q2] INTER As = {p2:real^N} /\ segment[p2,q2] INTER AF = {q2:real^N}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`p2:real^N`; `q2:real^N`] ENDS_IN_SEGMENT) THEN
    MAP_EVERY UNDISCH_TAC [`segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) INTER As = {p1}`; `(R1:real^N->bool) INTER AF = {q1}`;
      `(R2:real^N->bool) INTER As = {p2}`; `(R2:real^N->bool) INTER AF = {q2}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER J = {p1:real^N,q1} /\ segment[p2,q2] INTER J = {p2:real^N,q2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`As UNION AF = (J:real^N->bool)`;
      `segment[p1,q1] INTER As = {p1:real^N}`; `segment[p1,q1] INTER AF = {q1:real^N}`;
      `segment[p2,q2] INTER As = {p2:real^N}`; `segment[p2,q2] INTER AF = {q2:real^N}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER (R1 INTER Q') = {p1:real^N,q1} /\
                segment[p2,q2] INTER (R2 INTER Q') = {p2:real^N,q2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`; `Q INTER Q' = (J:real^N->bool)`;
      `segment[p1,q1] INTER J = {p1:real^N,q1}`; `segment[p2,q2] INTER J = {p2:real^N,q2}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p1:real^N) IN G1 /\ (q1:real^N) IN G1 /\ (p2:real^N) IN G2 /\ (q2:real^N) IN G2 /\
    segment[p1:real^N,q1] SUBSET Z /\ segment[p2:real^N,q2] SUBSET Z /\
    segment[p1:real^N,q1] SUBSET L /\ segment[p2:real^N,q2] SUBSET L`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(p1:real^N) IN R1`; `(q1:real^N) IN R1`; `(p2:real^N) IN R2`;
      `(q2:real^N) IN R2`; `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) SUBSET Z`; `(R2:real^N->bool) SUBSET Z`;
      `(R1:real^N->bool) SUBSET L`; `(R2:real^N->bool) SUBSET L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R L C Q S:real^N->bool.
      Z INTER G = R /\ R SUBSET L /\ L INTER C = Q /\ R INTER Q = S ==> (Z INTER C) INTER G = S`
  (LABEL_TAC "zg") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Z INTER moi_ftc_cone (v:real^N) Q) INTER G1 = segment[p1,q1] /\
    (Z INTER moi_ftc_cone (v:real^N) Q) INTER G2 = segment[p2,q2] /\
    (Z INTER moi_ftc_cone (v:real^N) Q') INTER G1 = R1 INTER Q' /\
    (Z INTER moi_ftc_cone (v:real^N) Q') INTER G2 = R2 INTER Q'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "zg" MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R2:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `L:real^N->bool`; `Q':real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R2:real^N->bool`; `L:real^N->bool`; `Q':real^N->bool`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z C L A S P:real^N->bool.
      S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
      ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`
  (LABEL_TAC "zs") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Z INTER moi_ftc_cone (v:real^N) J) INTER segment[p1,q1] = {p1,q1} /\
    (Z INTER moi_ftc_cone (v:real^N) J) INTER segment[p2,q2] = {p2,q2} /\
    segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p1} /\
    segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q1} /\
    segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p2} /\
    segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) J`; `L:real^N->bool`;
                     `J:real^N->bool`; `segment[p1:real^N,q1]`; `{p1:real^N,q1}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) J`; `L:real^N->bool`;
                     `J:real^N->bool`; `segment[p2:real^N,q2]`; `{p2:real^N,q2}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) As`; `L:real^N->bool`;
                     `As:real^N->bool`; `segment[p1:real^N,q1]`; `{p1:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) AF`; `L:real^N->bool`;
                     `AF:real^N->bool`; `segment[p1:real^N,q1]`; `{q1:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) As`; `L:real^N->bool`;
                     `As:real^N->bool`; `segment[p2:real^N,q2]`; `{p2:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) AF`; `L:real^N->bool`;
                     `AF:real^N->bool`; `segment[p2:real^N,q2]`; `{q2:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`))] THEN
    ANTS_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X INTER segment[v:real^N,m1] = {m1} /\ X INTER segment[v:real^N,m2] = {m2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_X_SEG THEN EXISTS_TAC `L:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`moi_ftc_cone (v:real^N) As INTER moi_ftc_cone v AF =
                            segment[v,m1] UNION segment[v,m2]`;
      `X INTER segment[v:real^N,m1] = {m1}`; `X INTER segment[v:real^N,m2] = {m2}`;
      `(Z:real^N->bool) SUBSET X`; `~((m1:real^N) IN Z)`; `~((m2:real^N) IN Z)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z INTER moi_ftc_cone (v:real^N) As SUBSET {p1,p2}) /\
                ~(Z INTER moi_ftc_cone (v:real^N) AF SUBSET {q1,q2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_ZRAY_POINT THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THENL
     [EXISTS_TAC `bs:real^N`; EXISTS_TAC `b1:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Fg INTER (Z INTER moi_ftc_cone (v:real^N) Q) = {} /\
    Z INTER moi_ftc_cone (v:real^N) J SUBSET Z INTER moi_ftc_cone v Q /\
    Z INTER moi_ftc_cone (v:real^N) J SUBSET Z INTER moi_ftc_cone v Q' /\
    (Z INTER moi_ftc_cone (v:real^N) Q) INTER (Z INTER moi_ftc_cone v Q') =
    Z INTER moi_ftc_cone v J /\
    (Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
    Z INTER moi_ftc_cone v J`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Fg:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) Q = Q`; `(Fg:real^N->bool) INTER Q = {}`;
      `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`;
      `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q'`;
      `moi_ftc_cone (v:real^N) Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J`;
      `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (Z INTER moi_ftc_cone (v:real^N) As) /\
                closed (Z INTER moi_ftc_cone (v:real^N) AF)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (Z INTER moi_ftc_cone (v:real^N) Q)` ASSUME_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION segment[p2,q2]`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `closed (moi_ftc_cone (v:real^N) As) /\ closed (moi_ftc_cone (v:real^N) AF)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_FTC_CONE_POLYHEDRON THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Z INTER moi_ftc_cone (v:real^N) As = (Z INTER moi_ftc_cone v Q) INTER moi_ftc_cone v As /\
      Z INTER moi_ftc_cone (v:real^N) AF = (Z INTER moi_ftc_cone v Q) INTER moi_ftc_cone v AF`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J`;
        `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`] THEN SET_TAC[];
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC));;

(* The two frontier arcs of the block: alpha over As and beta over AF. *)

let MOI_FTC_AB_ALPHA = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> pl_cell_with_boundary 1 (Z INTER moi_ftc_cone v As) {p1,p2} /\
         pl_cell_with_boundary 1 (Z INTER moi_ftc_cone v AF) {q1,q2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F2 th)) THEN
  SUBGOAL_THEN
   `pl_sphere 1 ((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                 segment[p2,q2])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `Z INTER moi_ftc_cone (v:real^N) Q`;
      `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION segment[p2,q2]`]
      MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THENL
   [EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) AF) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
                   Z INTER moi_ftc_cone v J` THEN SET_TAC[];
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`;
        `segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p1}`;
        `segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p2}`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `q1:real^N` THEN
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(p1:real^N = q1)` THEN UNDISCH_TAC `~(q1:real^N = p2)` THEN MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
                   Z INTER moi_ftc_cone v J` THEN SET_TAC[];
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`;
        `segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q1}`;
        `segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q2}`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `p1:real^N` THEN
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(p1:real^N = q1)` THEN UNDISCH_TAC `~(p1:real^N = q2)` THEN MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC]]);;

(* The frontier cell of the block outside the wedge: B = (Z INTER cone Q')  *)
(* UNION Fg is the complement in X of T UNION G1 UNION G2.                  *)

let MOI_FTC_AB_B = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> pl_cell_with_boundary 2 ((Z INTER moi_ftc_cone v Q') UNION Fg)
           ((Z INTER moi_ftc_cone v J) UNION (R1 INTER Q') UNION (R2 INTER Q'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F2 th)) THEN
  SUBGOAL_THEN `pl_sphere 2 (X:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
    SIMP_TAC[moi_ftc_rad];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Z INTER moi_ftc_cone (v:real^N) Q`;
                 `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
                  segment[p2,q2]`;
                 `G1:real^N->bool`; `R1:real^N->bool`; `p1:real^N`; `q1:real^N`]
    MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(Z INTER moi_ftc_cone (v:real^N) Q) UNION G1`;
                 `(((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
                    segment[p2,q2]) UNION R1) DIFF (segment[p1,q1] DIFF {p1,q1})`;
                 `G2:real^N->bool`; `R2:real^N->bool`; `p2:real^N`; `q2:real^N`]
    MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) Q) INTER G2 = segment[p2,q2]`;
        `(G1:real^N->bool) INTER G2 = {}`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
        `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
        `(G1:real^N->bool) INTER G2 = {}`] THEN
      SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `((Z INTER moi_ftc_cone (v:real^N) Q) UNION G1) UNION G2`;
    `((((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
        segment[p2,q2]) UNION R1) DIFF (segment[p1,q1] DIFF {p1,q1}) UNION R2) DIFF
     (segment[p2,q2] DIFF {p2,q2})`] MOI_FTC_DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) SUBSET X`; `(G1:real^N->bool) SUBSET X`;
                           `(G2:real^N->bool) SUBSET X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `X INTER moi_ftc_cone (v:real^N) Q`; `X INTER moi_ftc_cone (v:real^N) Q'`;
    `Z INTER moi_ftc_cone (v:real^N) Q`; `convex hull {m1:real^N,p1,q1}`;
    `convex hull {m2:real^N,p2,q2}`; `G1:real^N->bool`; `G2:real^N->bool`;
    `G1 INTER Q':real^N->bool`; `G2 INTER Q':real^N->bool`;
    `Z INTER moi_ftc_cone (v:real^N) Q'`; `Fg:real^N->bool`;
    `Z INTER moi_ftc_cone (v:real^N) J`; `segment[p1:real^N,q1]`; `segment[p2:real^N,q2]`;
    `R1 INTER Q':real^N->bool`; `R2 INTER Q':real^N->bool`; `R1:real^N->bool`;
    `R2:real^N->bool`; `{p1:real^N,q1}`; `{p2:real^N,q2}`] MOI_FTC_B_SETS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`(Z INTER moi_ftc_cone (v:real^N) Q') INTER G1 = R1 INTER Q'`;
      `(Z INTER moi_ftc_cone (v:real^N) Q') INTER G2 = R2 INTER Q'`;
      `segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `Fg INTER (Z INTER moi_ftc_cone (v:real^N) Q) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]]);;

(* The set identities behind the outer part G1 INTER Q' of the dual disk. *)

let MOI_FTC_D_SETS = prove
 (`!L G1 R1 H1 Q Q' J A1 t1 P1 K1:real^N->bool.
     G1 SUBSET L /\ R1 SUBSET G1 /\ H1 = G1 INTER Q /\ G1 INTER J = A1 /\
     Q UNION Q' = L /\ Q INTER Q' = J /\ K1 = R1 INTER Q' /\ R1 INTER Q = t1 /\
     t1 INTER A1 = P1 /\ P1 SUBSET t1 /\ t1 INTER K1 = P1
     ==> (R1 UNION (A1 UNION t1)) DIFF (t1 DIFF P1) = A1 UNION K1 /\
         (L DIFF (((L DIFF G1) UNION R1) UNION H1)) UNION (A1 UNION K1) = G1 INTER Q' /\
         ((L DIFF G1) UNION R1) INTER H1 = t1 /\
         ((L DIFF G1) UNION R1) UNION H1 SUBSET L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The cells of the dual disk G1: the corner triangle, the outer part       *)
(* G1 INTER Q' (complement in L of the complement of G1 with the corner     *)
(* glued on), the three edges of the corner and the outer arc of the rim.   *)

let MOI_FTC_AB_DISK = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> pl_cell_with_boundary 2 (convex hull {m1,p1,q1})
           ((segment[m1,p1] UNION segment[m1,q1]) UNION segment[p1,q1]) /\
         pl_cell_with_boundary 2 (G1 INTER Q')
           ((segment[m1,p1] UNION segment[m1,q1]) UNION (R1 INTER Q')) /\
         pl_cell_with_boundary 1 (segment[m1,p1]) {m1,p1} /\
         pl_cell_with_boundary 1 (segment[m1,q1]) {m1,q1} /\
         pl_cell_with_boundary 1 (segment[p1,q1]) {p1,q1} /\
         pl_cell_with_boundary 1 (R1 INTER Q') {p1,q1} /\
         G1 INTER J = segment[m1,p1] UNION segment[m1,q1] /\
         segment[p1,q1] INTER (segment[m1,p1] UNION segment[m1,q1]) = {p1,q1} /\
         ~(m1 = p1) /\ ~(m1 = q1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F2 th) THEN
    ASSUME_TAC(SYM(el 3 (tl(CONJUNCTS th))))) THEN
  SUBGOAL_THEN `pl_sphere 2 (L:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_ftc_abl]) THEN
    SIMP_TAC[moi_ftc_rad];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m1:real^N = p1) /\ ~(m1:real^N = q1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,p1,q1}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->bool) INTER J = segment[m1,p1] UNION segment[m1,q1]`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`As UNION AF = (J:real^N->bool)`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER (segment[m1,p1] UNION segment[m1,q1]) = {p1:real^N,q1}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`segment[p1:real^N,q1] SUBSET R1`; `(R1:real^N->bool) SUBSET G1`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `segment[p1,q1] INTER As = {p1:real^N}`; `segment[p1,q1] INTER AF = {q1:real^N}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (convex hull {m1:real^N,p1,q1})
                  ((segment[m1,p1] UNION segment[m1,q1]) UNION segment[p1,q1])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FTC_TRI_CELL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((L DIFF G1) UNION R1) (R1:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_DISK_COMPLEMENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->bool`; `G1:real^N->bool`; `R1:real^N->bool`;
                 `convex hull {m1:real^N,p1,q1}`; `Q:real^N->bool`; `Q':real^N->bool`;
                 `J:real^N->bool`; `segment[m1:real^N,p1] UNION segment[m1,q1]`;
                 `segment[p1:real^N,q1]`; `{p1:real^N,q1}`; `R1 INTER Q':real^N->bool`]
    MOI_FTC_D_SETS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN TRY REFL_TAC THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(L DIFF G1) UNION R1:real^N->bool`; `R1:real^N->bool`;
                 `convex hull {m1:real^N,p1,q1}`;
                 `(segment[m1:real^N,p1] UNION segment[m1,q1]) UNION segment[p1,q1]`;
                 `p1:real^N`; `q1:real^N`] MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((G1:real^N->bool) INTER Q')
                  ((segment[m1,p1] UNION segment[m1,q1]) UNION (R1 INTER Q'))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:real^N->bool`;
                   `((L DIFF G1) UNION R1) UNION convex hull {m1:real^N,p1,q1}`;
                   `(R1 UNION (segment[m1:real^N,p1] UNION segment[m1,q1]) UNION
                     segment[p1,q1]) DIFF (segment[p1,q1] DIFF {p1,q1})`]
      MOI_FTC_DISK_COMPLEMENT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (R1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `G1:real^N->bool`; `R1:real^N->bool`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (R1 INTER Q') {p1:real^N,q1}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
    MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `segment[p1:real^N,q1]`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[CLOSED_SEGMENT];
      MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
        MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `midpoint(p1:real^N,q1)` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY; MIDPOINT_EQ_ENDPOINT];
      DISCH_TAC THEN
      MP_TAC(ISPEC `R1:real^N->bool` MOI_FTC_SPHERE1_NOT_CONVEX) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `R1 = segment[p1:real^N,q1]` (fun th -> REWRITE_TAC[th; CONVEX_SEGMENT]) THEN
      MP_TAC(ISPECL [`p1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
      MAP_EVERY UNDISCH_TAC [`R1 INTER Q' SUBSET {p1:real^N,q1}`;
        `segment[p1,q1] UNION (R1 INTER Q') = (R1:real^N->bool)`;
        `segment[p1:real^N,q1] SUBSET R1`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC MOI_FCL_SEGMENT_CELL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The eighteen cells of the abstract block in the form used                *)
(* by the product assembly: W j = moi_ftc_zd (Y INTER cone Q) (Y INTER cone *)
(* Q') (Y INTER cone As) (Y INTER cone AF) (Z UNION Fg) ([v,m1] UNION        *)
(* [v,m2]) j are the block cells, G1 INTER W j the cells of the dual disk.   *)
(* ========================================================================= *)

let MOI_FTC_AB_F3 = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1)
     ==> Z SUBSET Y /\ G1 SUBSET Y /\ G2 SUBSET Y /\ Fg SUBSET Y /\
         segment[v,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v As /\
         segment[v,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v AF /\
         Y INTER moi_ftc_cone v J =
         (Y INTER moi_ftc_cone v As) UNION (Y INTER moi_ftc_cone v AF) /\
         X INTER moi_ftc_cone v As =
         (Z INTER moi_ftc_cone v As) UNION segment[m1,p1] UNION segment[m2,p2] /\
         X INTER moi_ftc_cone v AF =
         (Z INTER moi_ftc_cone v AF) UNION segment[m1,q1] UNION segment[m2,q2] /\
         (Z UNION Fg) INTER (Y INTER moi_ftc_cone v Q) = Z INTER moi_ftc_cone v Q /\
         (Z UNION Fg) INTER (Y INTER moi_ftc_cone v Q') = (Z INTER moi_ftc_cone v Q') UNION Fg /\
         (Y INTER moi_ftc_cone v As) INTER (Z UNION Fg) = Z INTER moi_ftc_cone v As /\
         (Y INTER moi_ftc_cone v AF) INTER (Z UNION Fg) = Z INTER moi_ftc_cone v AF /\
         G1 INTER (Y INTER moi_ftc_cone v Q) = convex hull {m1,p1,q1} /\
         G1 INTER (Y INTER moi_ftc_cone v Q') = G1 INTER Q' /\
         G1 INTER (Y INTER moi_ftc_cone v As) = segment[m1,p1] /\
         G1 INTER (Y INTER moi_ftc_cone v AF) = segment[m1,q1] /\
         G1 INTER (Z UNION Fg) = R1 /\
         G1 INTER (segment[v,m1] UNION segment[v,m2]) = {m1} /\
         G2 INTER (Y INTER moi_ftc_cone v Q) = convex hull {m2,p2,q2} /\
         G2 INTER (Y INTER moi_ftc_cone v Q') = G2 INTER Q' /\
         G2 INTER (Y INTER moi_ftc_cone v As) = segment[m2,p2] /\
         G2 INTER (Y INTER moi_ftc_cone v AF) = segment[m2,q2] /\
         G2 INTER (Z UNION Fg) = R2 /\
         G2 INTER (segment[v,m1] UNION segment[v,m2]) = {m2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c in
    ASSUME_TAC abl THEN STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F2 th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_R o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_abl" with Failure _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_abl] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_abl" with Failure _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_rad" with Failure _ -> false))
        (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN `(G1:real^N->bool) SUBSET Y /\ (G2:real^N->bool) SUBSET Y /\
                (Fg:real^N->bool) SUBSET Y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v As /\
    moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v AF`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN
    UNDISCH_TAC `As INTER AF = {m1:real^N,m2}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`
  ASSUME_TAC THENL [REWRITE_TAC[moi_ftc_cone; MOI_FTC_CONE_PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fg:real^N->bool) INTER As = {} /\ (Fg:real^N->bool) INTER AF = {} /\
                (Q':real^N->bool) SUBSET moi_ftc_cone v Q'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Fg:real^N->bool) INTER Q = {}`; `(As:real^N->bool) SUBSET J`;
      `(AF:real^N->bool) SUBSET J`; `(J:real^N->bool) SUBSET Q`;
      `L INTER moi_ftc_cone (v:real^N) Q' = Q'`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X Z Y L C A G1 G2 Fg S1 S2:real^N->bool.
      Z UNION Y INTER L = X /\ L INTER C = A /\ Y INTER L = G1 UNION G2 UNION Fg /\
      G1 INTER A = S1 /\ G2 INTER A = S2 /\ Fg INTER A = {}
      ==> X INTER C = (Z INTER C) UNION S1 UNION S2`
  (LABEL_TAC "xc") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z Y Fg L C P:real^N->bool.
      Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
      ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
          (Y INTER C) INTER (Z UNION Fg) = Z INTER C`
  (LABEL_TAC "zf") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!G Y L C P H:real^N->bool.
      G SUBSET Y /\ G SUBSET L /\ L INTER C = P /\ G INTER P = H
      ==> G INTER (Y INTER C) = H`
  (LABEL_TAC "gc") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY UNDISCH_TAC
     [`Y INTER moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v As`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`Y INTER moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v AF`] THEN SET_TAC[];
    UNDISCH_TAC `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J` THEN
    SET_TAC[];
    USE_THEN "xc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `As:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "xc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `AF:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) Q`; `Q:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) SUBSET Y`; `(Fg:real^N->bool) SUBSET Y`;
      `(Fg:real^N->bool) SUBSET Q'`; `(Q':real^N->bool) SUBSET moi_ftc_cone v Q'`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) As`; `As:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) AF`; `AF:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q':real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `As:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `AF:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER G1 = R1`; `(Fg:real^N->bool) INTER G1 = {}`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(G1:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}`;
      `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `(m1:real^N) IN G1`; `(m2:real^N) IN G2`; `(G1:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q':real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `As:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `AF:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER G2 = R2`; `(Fg:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(G2:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}`;
      `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `(m1:real^N) IN G1`; `(m2:real^N) IN G2`; `(G1:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[]]);;

let MOI_FTC_CELL_EQ = prove
 (`!n (c:real^N->bool) b c' b'.
     pl_cell_with_boundary n c' b' /\ c = c' /\ b = b' ==> pl_cell_with_boundary n c b`,
  MESON_TAC[]);;

(* The eighteen cells of the abstract block (block v and dual disk G1). *)

let MOI_FTC_AB_CELLS = prove
 (`!(v:real^N) L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q' p1 q1 p2 q2 W.
     moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     p1 = midpoint(m1,bs) /\ q1 = midpoint(m1,b1) /\
     p2 = midpoint(m2,bs) /\ q2 = midpoint(m2,b1) /\
     W = moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v Q')
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                    (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])
     ==> !j. j < 9
             ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (W j)
                   (UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                    ((G1 UNION G2) INTER W j)) /\
                 pl_cell_with_boundary (moi_ftc_dd j) (G1 INTER W j)
                   (G1 INTER UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c and wdef = last c in
    let th10 = end_itlist CONJ (butlast c) in
    let defs = tl (butlast c) in
    SUBST1_TAC wdef THEN ASSUME_TAC abl THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F1 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F2 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_F3 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_ALPHA th10) THEN
    ASSUME_TAC(MATCH_MP MOI_FTC_AB_B th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTC_AB_DISK th10) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTC_AB_W abl)) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTC_AB_R abl))) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN
   `segment[m1:real^N,p1] INTER R1 = {p1} /\ segment[m1:real^N,q1] INTER R1 = {q1} /\
    segment[m2:real^N,p2] INTER R2 = {p2} /\ segment[m2:real^N,q2] INTER R2 = {q2} /\
    R1 INTER convex hull {m1:real^N,p1,q1} = segment[p1,q1] /\
    R2 INTER convex hull {m2:real^N,p2,q2} = segment[p2,q2] /\
    R1 INTER (G1 INTER Q') = R1 INTER (Q':real^N->bool) /\
    R2 INTER (G2 INTER Q') = R2 INTER (Q':real^N->bool) /\
    (m1:real^N) IN segment[m1,p1] /\ (p1:real^N) IN segment[m1,p1] /\
    (m1:real^N) IN segment[m1,q1] /\ (q1:real^N) IN segment[m1,q1] /\
    (m2:real^N) IN segment[m2,p2] /\ (p2:real^N) IN segment[m2,p2] /\
    (m2:real^N) IN segment[m2,q2] /\ (q2:real^N) IN segment[m2,q2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m2:real^N`; `q2:real^N`] ENDS_IN_SEGMENT) THEN
    MAP_EVERY UNDISCH_TAC
     [`(R1:real^N->bool) INTER As = {p1}`; `(R1:real^N->bool) INTER AF = {q1}`;
      `(R2:real^N->bool) INTER As = {p2}`; `(R2:real^N->bool) INTER AF = {q2}`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `(G2:real^N->bool) INTER As = segment[m2,p2]`;
      `(G2:real^N->bool) INTER AF = segment[m2,q2]`;
      `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `(G1:real^N->bool) INTER Q = convex hull {m1,p1,q1}`;
      `(G2:real^N->bool) INTER Q = convex hull {m2,p2,q2}`;
      `(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `YQ = Y INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `YQ' = Y INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `YS = Y INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `YF = Y INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `YJ = Y INTER moi_ftc_cone (v:real^N) J` THEN
  ABBREV_TAC `XQ = X INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `XQ' = X INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `XS = X INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `XF = X INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `TT = Z INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `ZQ' = Z INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `AL = Z INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `BE = Z INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `ZJ = Z INTER moi_ftc_cone (v:real^N) J` THEN
  ABBREV_TAC `ZF = Z UNION (Fg:real^N->bool)` THEN
  ABBREV_TAC `KK = segment[v:real^N,m1] UNION segment[v,m2]` THEN
  ABBREV_TAC `H1 = convex hull {m1:real^N,p1,q1}` THEN
  ABBREV_TAC `H2 = convex hull {m2:real^N,p2,q2}` THEN
  ABBREV_TAC `s1p = segment[m1:real^N,p1]` THEN
  ABBREV_TAC `s1q = segment[m1:real^N,q1]` THEN
  ABBREV_TAC `s2p = segment[m2:real^N,p2]` THEN
  ABBREV_TAC `s2q = segment[m2:real^N,q2]` THEN
  ABBREV_TAC `t1 = segment[p1:real^N,q1]` THEN
  ABBREV_TAC `t2 = segment[p2:real^N,q2]` THEN
  ABBREV_TAC `GQ1 = G1 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `GQ2 = G2 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `K1 = R1 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `K2 = R2 INTER (Q':real^N->bool)` THEN
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT9]) THEN
  REWRITE_TAC[MOI_FTC_ZD_BD] THEN REWRITE_TAC[moi_ftc_zd; moi_ftc_dd] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[UNION_EMPTY; INTER_EMPTY] THENL
   [CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YQ:real^N->bool`; `XQ UNION YJ:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XQ = TT UNION H1 UNION (H2:real^N->bool)`; `YJ = YS UNION (YF:real^N->bool)`; `ZF INTER YQ = (TT:real^N->bool)`; `KK SUBSET (YS:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `G2 INTER YQ = (H2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`H1:real^N->bool`; `(s1p UNION s1q) UNION t1:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `R1 INTER H1 = (t1:real^N->bool)`; `G1 INTER KK = {m1:real^N}`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`; `(m1:real^N) IN s1p`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YQ':real^N->bool`; `XQ' UNION YJ:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XQ' = ZQ' UNION GQ1 UNION GQ2 UNION (Fg:real^N->bool)`; `YJ = YS UNION (YF:real^N->bool)`; `ZF INTER YQ' = ZQ' UNION (Fg:real^N->bool)`; `KK SUBSET (YS:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `G2 INTER YQ' = (GQ2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`GQ1:real^N->bool`; `(s1p UNION s1q) UNION K1:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `R1 INTER GQ1 = (K1:real^N->bool)`; `G1 INTER KK = {m1:real^N}`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`; `(m1:real^N) IN s1p`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YS:real^N->bool`; `XS UNION KK:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XS = AL UNION s1p UNION (s2p:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G2 INTER YS = (s2p:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`s1p:real^N->bool`; `{m1:real^N,p1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YF:real^N->bool`; `XF UNION KK:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XF = BE UNION s1q UNION (s2q:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G2 INTER YF = (s2q:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`s1q:real^N->bool`; `{m1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`TT:real^N->bool`; `ZJ UNION t1 UNION t2:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`ZF INTER YQ = (TT:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `AL UNION BE = (ZJ:real^N->bool)`; `TT INTER G1 = (t1:real^N->bool)`; `TT INTER G2 = (t2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`t1:real^N->bool`; `{p1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `R1 INTER H1 = (t1:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`ZQ' UNION Fg:real^N->bool`; `ZJ UNION K1 UNION K2:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`ZF INTER YQ' = ZQ' UNION (Fg:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `AL UNION BE = (ZJ:real^N->bool)`; `ZQ' INTER G1 = (K1:real^N->bool)`; `ZQ' INTER G2 = (K2:real^N->bool)`; `Fg INTER G1 = {}:real^N->bool`; `Fg INTER G2 = {}:real^N->bool`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`K1:real^N->bool`; `{p1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `R1 INTER GQ1 = (K1:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`KK:real^N->bool`; `{m1:real^N,m2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G2 INTER KK = {m2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{m1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`AL:real^N->bool`; `{p1:real^N,p2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`YS INTER ZF = (AL:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `G2 INTER YS = (s2p:real^N->bool)`; `G2 INTER ZF = (R2:real^N->bool)`; `s2p INTER R2 = {p2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{p1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`BE:real^N->bool`; `{q1:real^N,q2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`YF INTER ZF = (BE:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`; `G2 INTER YF = (s2q:real^N->bool)`; `G2 INTER ZF = (R2:real^N->bool)`; `s2q INTER R2 = {q2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{q1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* The level picture of block v as an abstract block.  With                 *)
(* the level homeomorphism h of the stars of V (moi_ftc_lev), Y = h(C_v),   *)
(* Z = h(C_v INTER Fr), G1 = h(C_v INTER C_u), G2 = h(C_v INTER C_u'),      *)
(* Fg = h(fingers at v) form a moi_ftc_abl configuration at v; the six      *)
(* basic sets of the cell structure have images Y INTER cone Q etc.          *)
(* ========================================================================= *)

(* The simplices of sd t at the wedge of block v. *)

let MOI_FTC_BLK_SD = prove
 (`!(t:(real^N->bool)->bool) v u u' x m1 m2 bs b1.
     moi_ftc_blk t v u u' x /\
     m1 = midpoint(v,u) /\ m2 = midpoint(v,u') /\
     bs = simplex_barycentre(convex hull {v,u,u'}) /\
     b1 = simplex_barycentre(convex hull {v,u,u',x})
     ==> convex hull {v,m1,bs,b1} IN barycentric_subdivision t /\
         convex hull {v,m2,bs,b1} IN barycentric_subdivision t /\
         ~affine_dependent {v,m1,bs,b1} /\ ~affine_dependent {v,m2,bs,b1} /\
         convex hull {m1,bs,b1} IN simplicial_link (barycentric_subdivision t) v /\
         convex hull {m2,bs,b1} IN simplicial_link (barycentric_subdivision t) v /\
         convex hull {m1,bs,b1} INTER convex hull {m2,bs,b1} = segment[bs,b1] /\
         ~collinear {m1,bs,b1} /\ ~collinear {m2,bs,b1} /\
         (!c. c SUBSET {v,m1,bs,b1} ==> convex hull c face_of convex hull {v,m1,bs,b1}) /\
         (!c. c SUBSET {v,m2,bs,b1} ==> convex hull c face_of convex hull {v,m2,bs,b1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) &&
    mem (fst(dest_var(lhs(concl th)))) ["m1"; "m2"; "bs"; "b1"]))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_DIMS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `simplex_barycentre (convex hull {v:real^N,u,u'})` &&
    not(is_var(rhs(concl th))))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `simplex_barycentre (convex hull {v:real^N,u,u',x})` &&
    not(is_var(rhs(concl th))))) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `C3 = convex hull {v:real^N,u,u'}` THEN
  ABBREV_TAC `C4 = convex hull {v:real^N,u,u',x}` THEN
  SUBGOAL_THEN
   `~(segment[v:real^N,u] = segment[v,u']) /\ ~(segment[v:real^N,u] = C3) /\
    ~(segment[v:real^N,u] = C4) /\ ~(segment[v:real^N,u'] = C3) /\
    ~(segment[v:real^N,u'] = C4) /\ ~(C3:real^N->bool = C4) /\
    ~({v:real^N} = segment[v,u]) /\ ~({v:real^N} = segment[v,u']) /\
    ~({v:real^N} = C3) /\ ~({v:real^N} = C4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ] THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THEN
    TRY(FIRST_ASSUM(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`)) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT; AFF_DIM_SING] THEN
    TRY INT_ARITH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE simplex_barycentre {{v}, segment[v,u], C3, C4} = {v:real^N,m1,bs,b1} /\
    IMAGE simplex_barycentre {{v}, segment[v,u'], C3, C4} = {v:real^N,m2,bs,b1} /\
    IMAGE simplex_barycentre {segment[v,u], C3, C4} = {m1:real^N,bs,b1} /\
    IMAGE simplex_barycentre {segment[v,u'], C3, C4} = {m2:real^N,bs,b1} /\
    IMAGE simplex_barycentre {C3, C4} = {bs:real^N,b1}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain t {segment[v:real^N,u], C3, C4} /\
    moi_bar_chain t {segment[v:real^N,u'], C3, C4}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THENL
     [EXISTS_TAC `{{v:real^N}, segment[v,u], C3, C4}`;
      EXISTS_TAC `{{v:real^N}, segment[v,u'], C3, C4}`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,m1,bs,b1} /\ ~affine_dependent {v:real^N,m2,bs,b1} /\
                ~affine_dependent {m1:real^N,bs,b1} /\ ~affine_dependent {m2:real^N,bs,b1}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{v:real^N,m1,bs,b1}`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{v:real^N,m2,bs,b1}`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{m1:real^N,bs,b1}`));
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `{m2:real^N,bs,b1}`))] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m1:real^N = bs) /\ ~(m1:real^N = b1) /\ ~(bs:real^N = b1) /\
                ~(m2:real^N = bs) /\ ~(m2:real^N = b1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u], C3, C4}`;
                     `segment[v:real^N,u]`; `C3:real^N->bool`] MOI_BAR_CHAIN_BARYCENTRE_INJ);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u], C3, C4}`;
                     `segment[v:real^N,u]`; `C4:real^N->bool`] MOI_BAR_CHAIN_BARYCENTRE_INJ);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u], C3, C4}`;
                     `C3:real^N->bool`; `C4:real^N->bool`] MOI_BAR_CHAIN_BARYCENTRE_INJ);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u'], C3, C4}`;
                     `segment[v:real^N,u']`; `C3:real^N->bool`] MOI_BAR_CHAIN_BARYCENTRE_INJ);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u'], C3, C4}`;
                     `segment[v:real^N,u']`; `C4:real^N->bool`] MOI_BAR_CHAIN_BARYCENTRE_INJ)] THEN
    ASM_REWRITE_TAC[IN_INSERT; MOI_FTA_BARY_SEGMENT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{{v:real^N}, segment[v,u], C3, C4}` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{{v:real^N}, segment[v,u'], C3, C4}` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{segment[v:real^N,u], C3, C4}` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u], C3, C4}`; `v:real^N`]
        MOI_FTA_VERTEX_IN_HULL) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull {v:real^N,m1,bs,b1}` THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{{v:real^N}, segment[v,u], C3, C4}` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{m1:real^N,bs,b1}` THEN REWRITE_TAC[] THEN SET_TAC[]];
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{segment[v:real^N,u'], C3, C4}` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u'], C3, C4}`; `v:real^N`]
        MOI_FTA_VERTEX_IN_HULL) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull {v:real^N,m2,bs,b1}` THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{{v:real^N}, segment[v,u'], C3, C4}` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{m2:real^N,bs,b1}` THEN REWRITE_TAC[] THEN SET_TAC[]];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,u], C3, C4}`;
                   `{segment[v:real^N,u'], C3, C4}`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `{segment[v:real^N,u], C3, C4} INTER {segment[v,u'], C3, C4} = {C3, C4}`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(segment[v:real^N,u] = segment[v,u'])`;
        `~(segment[v:real^N,u] = C3)`; `~(segment[v:real^N,u] = C4)`;
        `~(segment[v:real^N,u'] = C3)`; `~(segment[v:real^N,u'] = C4)`] THEN SET_TAC[];
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]];
    ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT];
    ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Basic facts about the level homeomorphism h of the stars of V. *)

let MOI_FTC_LEV_BASICS = prove
 (`!(t:(real^N->bool)->bool) l V h k w.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ w IN V /\ {w} IN l
     ==> pl_homeomorphism (UNIONS (moi_ftc_cs (barycentric_subdivision t) V),
                           UNIONS (moi_ftc_cs (barycentric_subdivision t) V)) (h,k) /\
         (!y. y IN UNIONS (moi_ftc_cs (barycentric_subdivision t) V) ==> k (h y) = y) /\
         UNIONS {s | s IN barycentric_subdivision t /\ w IN s} SUBSET
         UNIONS (moi_ftc_cs (barycentric_subdivision t) V) /\
         derived_dual_cell t l w SUBSET UNIONS {s | s IN barycentric_subdivision t /\ w IN s} /\
         (!r s. r IN barycentric_subdivision t /\ w IN r /\ s face_of r ==> IMAGE h s = s) /\
         UNIONS (simplicial_link (barycentric_subdivision t) w) SUBSET
         UNIONS {s | s IN barycentric_subdivision t /\ w IN s} /\
         IMAGE h (UNIONS (simplicial_link (barycentric_subdivision t) w)) =
         UNIONS (simplicial_link (barycentric_subdivision t) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_lev]) THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_BS_FACTS; graph_in_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s:real^N->bool. r IN barycentric_subdivision t /\ w IN r /\ s face_of r
                       ==> s IN moi_ftc_cs (barycentric_subdivision t) V`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cs; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN barycentric_subdivision t ==> r face_of r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC FACE_OF_REFL THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o
      GEN_REWRITE_RULE I [lf_simplicial_complex] o check (fun th ->
        concl th = `lf_simplicial_complex
                      (barycentric_subdivision (t:(real^N->bool)->bool))`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
      try fst(dest_const t) = "pl_homeomorphism" with Failure _ -> false)) (concl th))) THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[derived_dual_cell; INTER_SUBSET];
    ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* The level region of v is a radial configuration at v. *)

let MOI_FTC_HRAD = prove
 (`!(t:(real^N->bool)->bool) l V h k v.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ {v} IN l
     ==> moi_ftc_rad v (UNIONS (simplicial_link (barycentric_subdivision t) v))
           (IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) UNION
            (IMAGE h (derived_dual_cell t l v) INTER
             UNIONS (simplicial_link (barycentric_subdivision t) v)))
           (IMAGE h (derived_dual_cell t l v)) /\
         UNIONS {s | s IN barycentric_subdivision t /\ v IN s} =
         moi_ftc_cone v (UNIONS (simplicial_link (barycentric_subdivision t) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_LEV_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_LEV_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (derived_dual_cell t l (v:real^N)) /\
    pl_polyhedron (derived_dual_cell t l (v:real^N) INTER derived_frontier t l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `v:real^N`] MOI_FTA_CELL_CHAINS);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `v:real^N`] MOI_FTA_CELL_FRONTIER_CHAINS)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `v:real^N`;
                 `IMAGE (h:real^N->real^N) (derived_dual_cell t l v)`;
                 `IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_frontier t l)`]
    MOI_FTC_RAD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
      MP_TAC(ISPECL [`UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`;
                     `h:real^N->real^N`; `k:real^N->real^N`;
                     `derived_dual_cell t l (v:real^N)`] MOI_FTA_PLH_IMAGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      MP_TAC(ISPECL [`UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`;
                     `h:real^N->real^N`; `k:real^N->real^N`;
                     `derived_dual_cell t l (v:real^N) INTER derived_frontier t l`]
        MOI_FTA_PLH_IMAGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `derived_dual_cell t l (v:real^N)` THEN REWRITE_TAC[INTER_SUBSET] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_ftc_lev] o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_lev"
                                 with Failure _ -> false)) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `m:real^N->bool`] o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_ftc_rad; moi_ftc_cone] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^N->real^N) (derived_dual_cell t l v)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(z:real^N->bool) SUBSET y ==> z UNION (y INTER l) SUBSET y`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o check (fun th ->
      is_eq(concl th) &&
      aconv (lhs(concl th)) `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}`)) THEN
    REWRITE_TAC[SUBSET_REFL]]);;

(* Images of intersections under a map injective on U. *)

let MOI_FTC_IMAGE_INTER_EQ = prove
 (`!(h:real^N->real^N) k U A B C.
     (!x. x IN U ==> k (h x) = x) /\ A SUBSET U /\ B SUBSET U /\ A INTER B = C
     ==> IMAGE h A INTER IMAGE h B = IMAGE h C`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
  EXISTS_TAC `k:real^N->real^N` THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* The level picture of block v is an abstract block configuration. *)

let MOI_FTC_HPIC_ABL = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' x L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ u IN V /\ u' IN V /\
     moi_ftc_blk t v u u' x /\ segment[v,u] IN l /\ segment[v,u'] IN l /\
     L = UNIONS (simplicial_link (barycentric_subdivision t) v) /\
     Y = IMAGE h (derived_dual_cell t l v) /\
     Z = IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) /\
     X = Z UNION (Y INTER L) /\
     m1 = midpoint(v,u) /\ m2 = midpoint(v,u') /\
     bs = simplex_barycentre(convex hull {v,u,u'}) /\
     b1 = simplex_barycentre(convex hull {v,u,u',x}) /\
     G1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u) /\
     G2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u') /\
     R1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                   derived_frontier t l) /\
     R2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                   derived_frontier t l) /\
     Fg = IMAGE h (UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                           ~(w IN {v,u,u'}) /\ segment[v,w] IN l})
     ==> moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) &&
    mem (fst(dest_var(lhs(concl th))))
        ["L"; "Y"; "Z"; "X"; "m1"; "m2"; "bs"; "b1"; "G1"; "G2"; "R1"; "R2"; "Fg"]))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`]
    MOI_FTA_SEG_VERTS) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`; `u':real^N`]
    MOI_FTA_SEG_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_blk" with Failure _ -> false))
        (concl th))) THEN
  MAP_EVERY (fun w ->
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; w] MOI_FTC_LEV_BASICS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC])
   [`v:real^N`; `u:real^N`; `u':real^N`] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_HRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`; `x:real^N`;
                 `m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_BLK_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `midpoint(u,v) = m1:real^N /\ midpoint(u',v) = m2:real^N /\
    simplex_barycentre(convex hull {u,v,u'}) = bs:real^N /\
    simplex_barycentre(convex hull {u',v,u}) = bs:real^N /\
    simplex_barycentre(convex hull {v,u',u}) = bs:real^N /\
    simplex_barycentre(convex hull {u,v,u',x}) = b1:real^N /\
    simplex_barycentre(convex hull {u',v,u,x}) = b1:real^N /\
    simplex_barycentre(convex hull {v,u',u,x}) = b1:real^N /\
    segment[u,v] IN l /\ segment[u',v] IN l`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MIDPOINT_SYM; SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{u,v,u'} = {v:real^N,u,u'} /\ {u',v,u} = {v:real^N,u,u'} /\
                  {v,u',u} = {v:real^N,u,u'} /\ {u,v,u',x} = {v:real^N,u,u',x} /\
                  {u',v,u,x} = {v:real^N,u,u',x} /\ {v,u',u,x} = {v:real^N,u,u',x}`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_PERM o check (fun th ->
    concl th = `moi_ftc_blk t (v:real^N) u u' x`)) THEN
  MAP_EVERY (fun (a,b,c) ->
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; a; b; c; `x:real^N`]
      MOI_FTC_LEV_CORNER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC])
   [(`v:real^N`,`u:real^N`,`u':real^N`); (`u:real^N`,`v:real^N`,`u':real^N`);
    (`v:real^N`,`u':real^N`,`u:real^N`); (`u':real^N`,`v:real^N`,`u:real^N`)] THEN
  MAP_EVERY (fun (a,b,c) ->
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; a; b; c; `x:real^N`]
      MOI_FTC_LEV_FAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC])
   [(`v:real^N`,`u:real^N`,`u':real^N`); (`v:real^N`,`u':real^N`,`u:real^N`)] THEN
  ABBREV_TAC `U = UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))` THEN
  ABBREV_TAC `Fr = derived_frontier t (l:(real^N->bool)->bool)` THEN
  ABBREV_TAC `Cv = derived_dual_cell t l (v:real^N)` THEN
  ABBREV_TAC `Cu = derived_dual_cell t l (u:real^N)` THEN
  ABBREV_TAC `Cu' = derived_dual_cell t l (u':real^N)` THEN
  ABBREV_TAC `Fing = UNIONS {Cv INTER derived_dual_cell t l w | w |
                             ~(w IN {v:real^N,u,u'}) /\ segment[v,w] IN l}` THEN
  SUBGOAL_THEN
   `!A B:real^N->bool. A SUBSET U /\ B SUBSET U
                       ==> IMAGE (h:real^N->real^N) (A INTER B) = IMAGE h A INTER IMAGE h B`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
    EXISTS_TAC `k:real^N->real^N` THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cv:real^N->bool) SUBSET U /\ (Cu:real^N->bool) SUBSET U /\ (Cu':real^N->bool) SUBSET U /\
    (L:real^N->bool) SUBSET U /\ Cv INTER (Fr:real^N->bool) SUBSET U /\
    (Fing:real^N->bool) SUBSET Cv /\ (Fing:real^N->bool) SUBSET U /\
    convex hull {m1:real^N,bs,b1} SUBSET L /\ convex hull {m2:real^N,bs,b1} SUBSET L`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (u':real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Cv:real^N->bool` THEN
        REWRITE_TAC[INTER_SUBSET] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(EXPAND_TAC "Fing" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; INTER_SUBSET] THEN
        NO_TAC) THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Cv:real^N->bool` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "Fing" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; INTER_SUBSET];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
          ASM_REWRITE_TAC[]] THEN NO_TAC) THEN
    (MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `UNIONS (simplicial_link (barycentric_subdivision t) (v:real^N))` THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s SUBSET UNIONS f`) THEN
       ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[SUBSET_REFL]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `Cv INTER (Cu:real^N->bool) SUBSET U /\ Cv INTER (Cu':real^N->bool) SUBSET U /\
                convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1} SUBSET U`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Cv:real^N->bool) SUBSET U`; `(L:real^N->bool) SUBSET U`;
      `convex hull {m1:real^N,bs,b1} SUBSET L`; `convex hull {m2:real^N,bs,b1} SUBSET L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1} SUBSET
    convex hull {v,u,u',b1}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`; `x:real^N`]
      MOI_FTC_STAR_OM) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(A:real^N->bool) SUBSET A' /\ B SUBSET B'
      ==> s INTER t = A' UNION B' ==> (A UNION B) SUBSET t`) THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cv INTER Cu INTER (Cu':real^N->bool) = {} /\ Fing INTER (Cu:real^N->bool) = {} /\
    Fing INTER (Cu':real^N->bool) = {} /\
    Fing INTER (convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}) = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                   `u:real^N`; `u':real^N`] MOI_FTC_TRIPLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Fing" THEN
    REWRITE_TAC[SET_RULE `UNIONS s INTER t = {} <=> !x:real^N->bool. x IN s ==> x INTER t = {}`;
                FORALL_IN_GSPEC] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    (MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`] MOI_FTA_SEG_VERTS) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM]) THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `w:real^N`; `u:real^N`] MOI_FTC_TRIPLE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `w:real^N`; `u':real^N`] MOI_FTC_TRIPLE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u:real^N`; `u':real^N`; `x:real^N`; `w:real^N`] MOI_FTC_FING_OM) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REWRITE_TAC[moi_ftc_om] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1} SUBSET
                   convex hull {v,u,u',b1}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `u:real^N`;
                 `u':real^N`; `x:real^N`] MOI_FTC_CV_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) =
    convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "face_of" with Failure _ -> false))
          (concl th) &&
      can (find_term ((=) `v:real^N`)) (concl th))) THENL
     [EXISTS_TAC `convex hull {v:real^N,m1,bs,b1}`; EXISTS_TAC `convex hull {v:real^N,m2,bs,b1}`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 G1 (R1:real^N->bool) /\
                pl_cell_with_boundary 2 G2 (R2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u:real^N`] MOI_FTA_CELL2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u:real^N`] MOI_FTA_DISK_POLY);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u':real^N`] MOI_FTA_CELL2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u':real^N`] MOI_FTA_DISK_POLY)] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu) = G1`)) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu INTER Fr) = R1`));
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu') = G2`)) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu' INTER Fr) = R2`))] THEN
    (MATCH_MP_TAC MOI_FTA_CELL_PLH THEN EXISTS_TAC `k:real^N->real^N` THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
     EXISTS_TAC `U:real^N->bool` THEN EXISTS_TAC `U:real^N->bool` THEN
     ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `G1 = Y INTER IMAGE (h:real^N->real^N) Cu /\ G2 = Y INTER IMAGE h Cu' /\
    R1 = Z INTER IMAGE h Cu /\ R2 = Z INTER IMAGE h Cu' /\
    Y INTER L = G1 UNION G2 UNION Fg /\
    Fg INTER (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) = {} /\
    Fg INTER (G1 UNION G2) = {} /\ G1 INTER G2 = {} /\
    Z INTER G1 = R1 /\ Z INTER G2 = R2 /\ Z SUBSET Y`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun c -> FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = c)))
     [`IMAGE (h:real^N->real^N) Cv = Y`; `IMAGE (h:real^N->real^N) (Cv INTER Fr) = Z`;
      `IMAGE (h:real^N->real^N) (Cv INTER Cu) = G1`;
      `IMAGE (h:real^N->real^N) (Cv INTER Cu') = G2`;
      `IMAGE (h:real^N->real^N) (Cv INTER Cu INTER Fr) = R1`;
      `IMAGE (h:real^N->real^N) (Cv INTER Cu' INTER Fr) = R2`;
      `IMAGE (h:real^N->real^N) Fing = Fg`] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) {} = {}` (LABEL_TAC "e0") THENL
     [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
        check (fun th -> concl th = `IMAGE (h:real^N->real^N) L = L`)) THEN
      SUBGOAL_THEN
       `IMAGE (h:real^N->real^N) (Cv INTER Cu) UNION IMAGE h (Cv INTER Cu') UNION IMAGE h Fing =
        IMAGE h (Cv INTER L)`
      SUBST1_TAC THENL
       [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> concl th =
          `Cv INTER L = Cv INTER Cu UNION Cv INTER Cu' UNION (Fing:real^N->bool)`)) THEN
        REWRITE_TAC[IMAGE_UNION];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o
        check (fun th -> concl th =
          `IMAGE (h:real^N->real^N) (convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}) =
           convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1}`)) THEN
      USE_THEN "e0" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[UNION_OVER_INTER; EMPTY_UNION] THEN CONJ_TAC THEN
      USE_THEN "e0" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`Fing INTER (Cu:real^N->bool) = {}`;
                             `Fing INTER (Cu':real^N->bool) = {}`] THEN SET_TAC[];
      USE_THEN "e0" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Cv INTER Cu INTER (Cu':real^N->bool) = {}` THEN SET_TAC[];
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[midpoint(m1,bs),midpoint(m1,b1)] SUBSET
    convex hull {m1:real^N,midpoint(m1,bs),midpoint(m1,b1)} /\
    segment[midpoint(m2,bs),midpoint(m2,b1)] SUBSET
    convex hull {m2:real^N,midpoint(m2,bs),midpoint(m2,b1)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_abl] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`G1 = Y INTER IMAGE (h:real^N->real^N) Cu`;
      `Y INTER convex hull {m1,bs,b1} =
       convex hull {m1:real^N,midpoint(m1,bs),midpoint(m1,b1)}`;
      `IMAGE (h:real^N->real^N) Cu INTER convex hull {m1,bs,b1} =
       convex hull {m1:real^N,midpoint(m1,bs),midpoint(m1,b1)}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`G1 = Y INTER IMAGE (h:real^N->real^N) Cu`;
      `IMAGE (h:real^N->real^N) Cu INTER convex hull {m2,bs,b1} = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`G2 = Y INTER IMAGE (h:real^N->real^N) Cu'`;
      `Y INTER convex hull {m2,bs,b1} =
       convex hull {m2:real^N,midpoint(m2,bs),midpoint(m2,b1)}`;
      `IMAGE (h:real^N->real^N) Cu' INTER convex hull {m2,bs,b1} =
       convex hull {m2:real^N,midpoint(m2,bs),midpoint(m2,b1)}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`G2 = Y INTER IMAGE (h:real^N->real^N) Cu'`;
      `IMAGE (h:real^N->real^N) Cu' INTER convex hull {m1,bs,b1} = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`R1 = Z INTER IMAGE (h:real^N->real^N) Cu`;
      `Z INTER convex hull {m1,bs,b1} =
       segment[midpoint(m1,bs),midpoint(m1:real^N,b1)]`;
      `IMAGE (h:real^N->real^N) Cu INTER convex hull {m1,bs,b1} =
       convex hull {m1:real^N,midpoint(m1,bs),midpoint(m1,b1)}`;
      `segment[midpoint(m1,bs),midpoint(m1,b1)] SUBSET
       convex hull {m1:real^N,midpoint(m1,bs),midpoint(m1,b1)}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`R2 = Z INTER IMAGE (h:real^N->real^N) Cu'`;
      `Z INTER convex hull {m2,bs,b1} =
       segment[midpoint(m2,bs),midpoint(m2:real^N,b1)]`;
      `IMAGE (h:real^N->real^N) Cu' INTER convex hull {m2,bs,b1} =
       convex hull {m2:real^N,midpoint(m2,bs),midpoint(m2,b1)}`;
      `segment[midpoint(m2,bs),midpoint(m2,b1)] SUBSET
       convex hull {m2:real^N,midpoint(m2,bs),midpoint(m2,b1)}`] THEN SET_TAC[]]);;

(* Helpers for the images of the cells under the level homeomorphism. *)

let MOI_FTC_HULL_CONE = prove
 (`!(v:real^N) s. ~(s = {}) ==> convex hull (v INSERT s) = moi_ftc_cone v (convex hull s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  REWRITE_TAC[moi_ftc_cone; EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `segment[v:real^N,y]` THEN
    CONJ_TAC THENL [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a = &1 - b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REFL_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`&1 - w`; `w:real`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_FTC_IMAGE_DIFF_EQ = prove
 (`!(h:real^N->real^N) k U A B.
     (!x. x IN U ==> k (h x) = x) /\ A SUBSET U /\ B SUBSET U
     ==> IMAGE h (A DIFF B) = IMAGE h A DIFF IMAGE h B`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

let MOI_FTC_IMAGE_INTER_UNIONS = prove
 (`!(h:real^N->real^N) C (f:num->real^N->bool) P.
     IMAGE h (C INTER UNIONS {f j | j | P j}) = UNIONS {IMAGE h (C INTER f j) | j | P j}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; MOI_FTC_IN_UNIONS_GSPEC] THEN MESON_TAC[]);;

let MOI_FTC_ZD_IMAGE = prove
 (`!(h:real^N->real^N) k U C Om Op S Fn Xs Kc B0 B1 B2 B3 B4 B5.
     (!x. x IN U ==> k (h x) = x) /\ C SUBSET U /\
     IMAGE h (C INTER Om) = B0 /\ IMAGE h (C INTER Op) = B1 /\ IMAGE h (C INTER S) = B2 /\
     IMAGE h (C INTER Fn) = B3 /\ IMAGE h (C INTER Xs) = B4 /\ IMAGE h (C INTER Kc) = B5
     ==> !j. j < 9
             ==> IMAGE h (C INTER moi_ftc_zd Om Op S Fn Xs Kc j) =
                 moi_ftc_zd B0 B1 B2 B3 B4 B5 j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P Q:real^N->bool.
      IMAGE (h:real^N->real^N) (C INTER P INTER Q) = IMAGE h (C INTER P) INTER IMAGE h (C INTER Q)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(C:real^N->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT9]) THEN
  REWRITE_TAC[moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* The images of the six basic traces on C_v. *)

let MOI_FTC_HPIC_IMG = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' x L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg Q As AF J Q'.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ u IN V /\ u' IN V /\
     moi_ftc_blk t v u u' x /\ segment[v,u] IN l /\ segment[v,u'] IN l /\
     L = UNIONS (simplicial_link (barycentric_subdivision t) v) /\
     Y = IMAGE h (derived_dual_cell t l v) /\
     Z = IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) /\
     X = Z UNION (Y INTER L) /\
     m1 = midpoint(v,u) /\ m2 = midpoint(v,u') /\
     bs = simplex_barycentre(convex hull {v,u,u'}) /\
     b1 = simplex_barycentre(convex hull {v,u,u',x}) /\
     G1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u) /\
     G2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u') /\
     R1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                   derived_frontier t l) /\
     R2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                   derived_frontier t l) /\
     Fg = IMAGE h (UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                           ~(w IN {v,u,u'}) /\ segment[v,w] IN l}) /\
     Q = convex hull {m1,bs,b1} UNION convex hull {m2,bs,b1} /\
     As = segment[m1,bs] UNION segment[bs,m2] /\
     AF = segment[m1,b1] UNION segment[b1,m2] /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> moi_ftc_abl v L X Y Z m1 m2 bs b1 G1 G2 R1 R2 Fg /\
         pl_homeomorphism (UNIONS (moi_ftc_cs (barycentric_subdivision t) V),
                           UNIONS (moi_ftc_cs (barycentric_subdivision t) V)) (h,k) /\
         derived_dual_cell t l v SUBSET UNIONS (moi_ftc_cs (barycentric_subdivision t) V) /\
         (!y. y IN UNIONS (moi_ftc_cs (barycentric_subdivision t) V) ==> k (h y) = y) /\
         IMAGE h (derived_dual_cell t l v INTER moi_ftc_om v u u' x) =
         Y INTER moi_ftc_cone v Q /\
         IMAGE h (derived_dual_cell t l v INTER
                  ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x))) =
         Y INTER moi_ftc_cone v Q' /\
         IMAGE h (derived_dual_cell t l v INTER convex hull {v,u,u'}) =
         Y INTER moi_ftc_cone v As /\
         IMAGE h (derived_dual_cell t l v INTER moi_ftc_fin v u u' x) =
         Y INTER moi_ftc_cone v AF /\
         IMAGE h (derived_dual_cell t l v INTER moi_ftc_xs t l v u u') = Z UNION Fg /\
         IMAGE h (derived_dual_cell t l v INTER moi_ftc_core v u u') =
         segment[v,m1] UNION segment[v,m2]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let ablh = end_itlist CONJ (butlast(butlast(butlast(butlast(butlast c))))) in
    ASSUME_TAC (MATCH_MP MOI_FTC_HPIC_ABL ablh) THEN STRIP_ASSUME_TAC th) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) &&
    mem (fst(dest_var(lhs(concl th))))
        ["L"; "Y"; "Z"; "X"; "m1"; "m2"; "bs"; "b1"; "G1"; "G2"; "R1"; "R2"; "Fg";
         "Q"; "As"; "AF"; "J"; "Q'"]))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "graph_in_complex"
                             with Failure _ -> false)) (concl th))) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`]
    MOI_FTA_SEG_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_LEV_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_HRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_LEV_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`; `x:real^N`;
                 `m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`] MOI_FTC_BLK_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun th ->
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`; `x:real^N`]
      th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC])
   [MOI_FTC_STAR_OM; MOI_FTC_STAR_S; MOI_FTC_STAR_F; MOI_FTC_STAR_K] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `u:real^N`;
                 `u':real^N`; `x:real^N`] MOI_FTC_CV_XS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `u':real^N`; `x:real^N`]
    MOI_FTC_R1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`;
                 `G1:real^N->bool`; `G2:real^N->bool`; `R1:real^N->bool`; `R2:real^N->bool`;
                 `Fg:real^N->bool`; `Q:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`;
                 `J:real^N->bool`; `Q':real^N->bool`; `midpoint(m1:real^N,bs)`;
                 `midpoint(m1:real^N,b1)`; `midpoint(m2:real^N,bs)`; `midpoint(m2:real^N,b1)`]
    MOI_FTC_AB_F1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_AB_R o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_abl" with Failure _ -> false))
        (concl th))) THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) L SUBSET UNIONS (moi_ftc_cs (barycentric_subdivision t) V) /\
    derived_dual_cell t l (v:real^N) SUBSET moi_ftc_cone v L`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> aconv (concl th)
      `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s} = moi_ftc_cone v L`)) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P:real^N->bool. P SUBSET moi_ftc_cone v L /\ IMAGE (h:real^N->real^N) P = P
                     ==> IMAGE h (derived_dual_cell t l v INTER P) = Y INTER P`
  (LABEL_TAC "tr") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) o check (fun th ->
      concl th = `IMAGE (h:real^N->real^N) (derived_dual_cell t l v) = Y`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`k:real^N->real^N`; `UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_ftc_cone (v:real^N) L` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A:real^N->bool. derived_dual_cell t l v INTER A =
                     derived_dual_cell t l v INTER (moi_ftc_cone v L INTER A)`
  (LABEL_TAC "st") THENL
   [GEN_TAC THEN UNDISCH_TAC `derived_dual_cell t l (v:real^N) SUBSET moi_ftc_cone v L` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!c. c SUBSET {v:real^N,m1,bs,b1} ==> IMAGE (h:real^N->real^N) (convex hull c) = convex hull c) /\
    (!c. c SUBSET {v:real^N,m2,bs,b1} ==> IMAGE (h:real^N->real^N) (convex hull c) = convex hull c)`
  (CONJUNCTS_THEN2 (LABEL_TAC "fx1") (LABEL_TAC "fx2")) THENL
   [CONJ_TAC THEN X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "face_of" with Failure _ -> false))
          (concl th))) THENL
     [EXISTS_TAC `convex hull {v:real^N,m1,bs,b1}`; EXISTS_TAC `convex hull {v:real^N,m2,bs,b1}`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v:real^N,m1,bs,b1} UNION convex hull {v,m2,bs,b1} = moi_ftc_cone v Q /\
    convex hull {v:real^N,m1,bs} UNION convex hull {v,m2,bs} = moi_ftc_cone v As /\
    convex hull {v:real^N,m1,b1} UNION convex hull {v,m2,b1} = moi_ftc_cone v AF /\
    segment[v:real^N,m1] UNION segment[v,m2] = moi_ftc_cone v {m1,m2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun th -> FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th' -> concl th' = th)))
     [`convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1} = Q`;
      `segment[m1:real^N,bs] UNION segment[bs,m2] = As`;
      `segment[m1:real^N,b1] UNION segment[b1,m2] = AF`] THEN
    SIMP_TAC[MOI_FTC_HULL_CONE; NOT_INSERT_EMPTY; GSYM SEGMENT_CONVEX_HULL] THEN
    REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION; MOI_FTC_CONE_PAIR] THEN
    REWRITE_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (convex hull {v,m1,bs,b1} UNION convex hull {v,m2,bs,b1}) =
    convex hull {v,m1,bs,b1} UNION convex hull {v,m2,bs,b1} /\
    IMAGE (h:real^N->real^N) (convex hull {v,m1,bs} UNION convex hull {v,m2,bs}) =
    convex hull {v,m1,bs} UNION convex hull {v,m2,bs} /\
    IMAGE (h:real^N->real^N) (convex hull {v,m1,b1} UNION convex hull {v,m2,b1}) =
    convex hull {v,m1,b1} UNION convex hull {v,m2,b1} /\
    IMAGE (h:real^N->real^N) (segment[v,m1] UNION segment[v,m2]) =
    segment[v,m1] UNION segment[v,m2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION; SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN BINOP_TAC THENL
     [USE_THEN "fx1" MATCH_MP_TAC; USE_THEN "fx2" MATCH_MP_TAC;
      USE_THEN "fx1" MATCH_MP_TAC; USE_THEN "fx2" MATCH_MP_TAC;
      USE_THEN "fx1" MATCH_MP_TAC; USE_THEN "fx2" MATCH_MP_TAC;
      USE_THEN "fx1" MATCH_MP_TAC; USE_THEN "fx2" MATCH_MP_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER moi_ftc_om v u u' x) =
    Y INTER moi_ftc_cone v Q /\
    IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER convex hull {v,u,u'}) =
    Y INTER moi_ftc_cone v As /\
    IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER moi_ftc_fin v u u' x) =
    Y INTER moi_ftc_cone v AF /\
    IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER moi_ftc_core v u u') =
    segment[v,m1] UNION segment[v,m2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_om; moi_ftc_fin; moi_ftc_core] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> concl th =
      `simplex_barycentre (convex hull {v:real^N,u,u',x}) = b1`)) THEN
    USE_THEN "st" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        aconv (lhs(concl th)) `moi_ftc_cone (v:real^N) L INTER convex hull {v,u,u',b1}`));
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        aconv (lhs(concl th)) `moi_ftc_cone (v:real^N) L INTER convex hull {v,u,u'}`));
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        aconv (lhs(concl th))
          `moi_ftc_cone (v:real^N) L INTER
           (convex hull {v,u,b1} UNION convex hull {u,u',b1} UNION convex hull {v,u',b1})`));
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        aconv (lhs(concl th))
          `moi_ftc_cone (v:real^N) L INTER (segment[v,u] UNION segment[u,u'] UNION segment[v,u'])`))] THEN
    W(fun (_,w) -> let p = rand(rand(lhs w)) in
      SUBGOAL_THEN (mk_eq(lhs w, mk_comb(mk_comb(`(INTER):(real^N->bool)->(real^N->bool)->real^N->bool`,
                                                `Y:real^N->bool`), p)))
      SUBST1_TAC THENL
       [USE_THEN "tr" MATCH_MP_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
            aconv (rhs(concl th)) p &&
            can (find_term ((=) `moi_ftc_cone (v:real^N) L`)) (lhs(concl th)))) THEN
          REWRITE_TAC[INTER_SUBSET];
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "st" (K ALL_TAC) THEN REMOVE_THEN "tr" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `derived_dual_cell t l (v:real^N) SUBSET UNIONS (moi_ftc_cs (barycentric_subdivision t) V)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_ftc_cone (v:real^N) L` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) L = moi_ftc_cone v Q UNION moi_ftc_cone v Q' /\
    moi_ftc_cone (v:real^N) Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J /\
    moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J`
  (LABEL_TAC "cq") THENL
   [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `Q:real^N->bool`; `Q':real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad] o
        check (fun th -> concl th = `moi_ftc_rad (v:real^N) L X Y`)) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `segment[m1:real^N,bs] UNION segment[bs,m2] = As` THEN
      UNDISCH_TAC `As UNION AF = (J:real^N->bool)` THEN
      UNDISCH_TAC `Q INTER Q' = (J:real^N->bool)` THEN
      MP_TAC(ISPECL [`m1:real^N`; `bs:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N)
      (derived_dual_cell t l v INTER ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x))) =
    Y INTER moi_ftc_cone v Q'`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `derived_dual_cell t l (v:real^N) INTER
      ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x)) =
      (derived_dual_cell t l v DIFF (derived_dual_cell t l v INTER moi_ftc_om v u u' x)) UNION
      (derived_dual_cell t l v INTER convex hull {v,u,u'}) UNION
      (derived_dual_cell t l v INTER moi_ftc_fin v u u' x)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `moi_ftc_om (v:real^N) u u' x` RELATIVE_INTERIOR_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        aconv (lhs(concl th))
          `moi_ftc_om (v:real^N) u u' x INTER
           ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x))`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`;
                   `UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`;
                   `derived_dual_cell t l (v:real^N)`;
                   `derived_dual_cell t l (v:real^N) INTER moi_ftc_om v u u' x`]
      MOI_FTC_IMAGE_DIFF_EQ) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `derived_dual_cell t l (v:real^N)` THEN
      REWRITE_TAC[INTER_SUBSET] THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Y SUBSET moi_ftc_cone (v:real^N) L` THEN
    USE_THEN "cq" MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Pulling the eighteen abstract block cells back through the                *)
(* level homeomorphism h; the cells of block v in the original space.       *)
(* ========================================================================= *)

(* A generic pullback: if h maps C INTER ZA j onto W j and D1, D2 onto G1,   *)
(* G2, the cells of the W-picture pull back to cells of the ZA-picture.      *)

let MOI_FTC_PULL_CELLS = prove
 (`!(h:real^N->real^N) k U C D1 D2 (ZA:num->real^N->bool) (W:num->real^N->bool) G1 G2.
     pl_homeomorphism (U,U) (h,k) /\ C SUBSET U /\ D1 SUBSET C /\ D2 SUBSET C /\
     IMAGE h D1 = G1 /\ IMAGE h D2 = G2 /\
     (!j. j < 9 ==> IMAGE h (C INTER ZA j) = W j) /\
     (!j. j < 9
          ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (W j)
                (UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                 ((G1 UNION G2) INTER W j)) /\
              pl_cell_with_boundary (moi_ftc_dd j) (G1 INTER W j)
                (G1 INTER UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}))
     ==> !j. j < 9
             ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (C INTER ZA j)
                   ((C INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})
                    UNION ((D1 UNION D2) INTER ZA j)) /\
                 pl_cell_with_boundary (moi_ftc_dd j) (D1 INTER ZA j)
                   (D1 INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "im") (LABEL_TAC "cl")))))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `IMAGE (h:real^N->real^N) D1 = G1`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `IMAGE (h:real^N->real^N) D2 = G2`)) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!A B:real^N->bool. A SUBSET U /\ B SUBSET U
                       ==> IMAGE (h:real^N->real^N) (A INTER B) = IMAGE h A INTER IMAGE h B`
  (LABEL_TAC "ii") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. IMAGE (h:real^N->real^N) (C INTER UNIONS {(ZA:num->real^N->bool) j' | j' | j' < 9 /\ P j'}) =
        UNIONS {(W:num->real^N->bool) j' | j' | j' < 9 /\ P j'}`
  (LABEL_TAC "iu") THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_FTC_IMAGE_INTER_UNIONS] THEN
    REWRITE_TAC[EXTENSION; MOI_FTC_IN_UNIONS_GSPEC] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THEN
    (DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `i:num` THEN
     USE_THEN "im" (MP_TAC o SPEC `i:num`) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
     DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
     ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D1 UNION D2) INTER (ZA:num->real^N->bool) j = (D1 UNION D2) INTER (C INTER ZA j) /\
    D1 INTER ZA j = D1 INTER (C INTER ZA j) /\
    D1 INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} =
    D1 INTER (C INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(D1:real^N->bool) SUBSET C` THEN UNDISCH_TAC `(D2:real^N->bool) SUBSET C` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "cl" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `C INTER (ZA:num->real^N->bool) j SUBSET U /\ D1 UNION D2 SUBSET (U:real^N->bool) /\
    D1 SUBSET U`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (C INTER ZA j) = W j /\
    IMAGE (h:real^N->real^N)
      ((C INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
       ((D1 UNION D2) INTER (C INTER ZA j))) =
    UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
    ((IMAGE h D1 UNION IMAGE h D2) INTER W j) /\
    IMAGE (h:real^N->real^N) (D1 INTER (C INTER ZA j)) = IMAGE h D1 INTER W j /\
    IMAGE (h:real^N->real^N)
      (D1 INTER (C INTER UNIONS {ZA j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})) =
    IMAGE h D1 INTER UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "im" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    USE_THEN "iu" (MP_TAC o SPEC `\j'. moi_ftc_dface j j' /\ ~(j' = j)`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    USE_THEN "ii" (fun th ->
      MP_TAC(SPECL [`D1 UNION D2:real^N->bool`; `C INTER (ZA:num->real^N->bool) j`] th) THEN
      MP_TAC(SPECL [`D1:real^N->bool`; `C INTER (ZA:num->real^N->bool) j`] th) THEN
      MP_TAC(SPECL [`D1:real^N->bool`;
                    `C INTER UNIONS {(ZA:num->real^N->bool) j' | j' |
                                     j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}`] th)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_UNION];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S4O_CELL_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h:real^N->real^N`; `k:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The nine dual-disk traces of the triangle conv{v,u,u'} (x the far vertex *)
(* of the 3-simplex): a global labelling, symmetric in v, u, u'.            *)

let moi_ftc_za = new_definition
 `moi_ftc_za (t:(real^N->bool)->bool) l (v:real^N) u u' x =
    moi_ftc_zd (moi_ftc_om v u u' x)
               ((:real^N) DIFF relative_interior (moi_ftc_om v u u' x))
               (convex hull {v,u,u'}) (moi_ftc_fin v u u' x) (moi_ftc_xs t l v u u')
               (moi_ftc_core v u u')`;;

let MOI_FTC_ZA_SYM = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     moi_ftc_za t l v u u' x = moi_ftc_za t l u v u' x /\
     moi_ftc_za t l v u u' x = moi_ftc_za t l v u' u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_za] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `u:real^N`;
                 `u':real^N`; `x:real^N`] MOI_FTC_SETS_SYM) THEN
  DISCH_THEN(fun th -> let c = CONJUNCTS th in
    CONJ_TAC THENL
     [REWRITE_TAC[el 0 c; el 2 c; el 4 c; el 8 c; el 10 c];
      REWRITE_TAC[el 1 c; el 3 c; el 5 c; el 9 c; el 11 c]]));;

let MOI_FTC_ZA_CYC = prove
 (`!(t:(real^N->bool)->bool) l a b c x.
     moi_ftc_za t l b c a x = moi_ftc_za t l a b c x /\
     moi_ftc_za t l c a b x = moi_ftc_za t l a b c x`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `moi_ftc_za (t:(real^N->bool)->bool) l b a c x`;
    EXISTS_TAC `moi_ftc_za (t:(real^N->bool)->bool) l a c b x`] THEN
  MESON_TAC[MOI_FTC_ZA_SYM]);;

(* The cells of block v: C_v INTER za j (dimension 1 + dd j) and the dual   *)
(* disk traces (C_v INTER C_u) INTER za j (dimension dd j).                  *)

let MOI_FTC_BLOCK_CELLS = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' x.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ u IN V /\ u' IN V /\
     moi_ftc_blk t v u u' x /\ segment[v,u] IN l /\ segment[v,u'] IN l
     ==> !j. j < 9
             ==> pl_cell_with_boundary (1 + moi_ftc_dd j)
                   (derived_dual_cell t l v INTER moi_ftc_za t l v u u' x j)
                   ((derived_dual_cell t l v INTER
                     UNIONS {moi_ftc_za t l v u u' x j' | j' |
                             j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                    (((derived_dual_cell t l v INTER derived_dual_cell t l u) UNION
                      (derived_dual_cell t l v INTER derived_dual_cell t l u')) INTER
                     moi_ftc_za t l v u u' x j)) /\
                 pl_cell_with_boundary (moi_ftc_dd j)
                   ((derived_dual_cell t l v INTER derived_dual_cell t l u) INTER
                    moi_ftc_za t l v u u' x j)
                   ((derived_dual_cell t l v INTER derived_dual_cell t l u) INTER
                    UNIONS {moi_ftc_za t l v u u' x j' | j' |
                            j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision t) (v:real^N))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (derived_dual_cell t l v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_frontier t l)` THEN
  ABBREV_TAC `X = (Z:real^N->bool) UNION (Y INTER L)` THEN
  ABBREV_TAC `m1 = midpoint(v:real^N,u)` THEN
  ABBREV_TAC `m2 = midpoint(v:real^N,u')` THEN
  ABBREV_TAC `bs = simplex_barycentre(convex hull {v:real^N,u,u'})` THEN
  ABBREV_TAC `b1 = simplex_barycentre(convex hull {v:real^N,u,u',x})` THEN
  ABBREV_TAC `G1 = IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_dual_cell t l u)` THEN
  ABBREV_TAC `G2 = IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_dual_cell t l u')` THEN
  ABBREV_TAC `R1 = IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                                             derived_frontier t l)` THEN
  ABBREV_TAC `R2 = IMAGE (h:real^N->real^N) (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                                             derived_frontier t l)` THEN
  ABBREV_TAC `Fg = IMAGE (h:real^N->real^N)
                     (UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                              ~(w IN {v,u,u'}) /\ segment[v,w] IN l})` THEN
  ABBREV_TAC `Q = convex hull {m1:real^N,bs,b1} UNION convex hull {m2,bs,b1}` THEN
  ABBREV_TAC `As = segment[m1:real^N,bs] UNION segment[bs,m2]` THEN
  ABBREV_TAC `AF = segment[m1:real^N,b1] UNION segment[b1,m2]` THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  ABBREV_TAC `Q' = ((L:real^N->bool) DIFF Q) UNION J` THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`; `u:real^N`; `u':real^N`;
                 `x:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`;
                 `G1:real^N->bool`; `G2:real^N->bool`; `R1:real^N->bool`; `R2:real^N->bool`;
                 `Fg:real^N->bool`; `Q:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`;
                 `J:real^N->bool`; `Q':real^N->bool`] MOI_FTC_HPIC_IMG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `bs:real^N`; `b1:real^N`;
                 `G1:real^N->bool`; `G2:real^N->bool`; `R1:real^N->bool`; `R2:real^N->bool`;
                 `Fg:real^N->bool`; `Q:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`;
                 `J:real^N->bool`; `Q':real^N->bool`;
                 `midpoint(m1:real^N,bs)`; `midpoint(m1:real^N,b1)`;
                 `midpoint(m2:real^N,bs)`; `midpoint(m2:real^N,b1)`;
                 `moi_ftc_zd (Y INTER moi_ftc_cone (v:real^N) Q) (Y INTER moi_ftc_cone v Q')
                             (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                             (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])`]
    MOI_FTC_AB_CELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC MOI_FTC_PULL_CELLS THEN
  MAP_EVERY EXISTS_TAC
   [`h:real^N->real^N`; `k:real^N->real^N`;
    `UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`;
    `moi_ftc_zd (Y INTER moi_ftc_cone (v:real^N) Q) (Y INTER moi_ftc_cone v Q')
                (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])`;
    `G1:real^N->bool`; `G2:real^N->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  REWRITE_TAC[moi_ftc_za] THEN MATCH_MP_TAC MOI_FTC_ZD_IMAGE THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->real^N`; `UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The original-space product structure of the three blocks:               *)
(* labels, the global trace intersections, all 54 cells, and the assembly   *)
(* map onto the model (relative frontier of a triangle) PCROSS square.      *)
(* ========================================================================= *)

let MOI_FTC_LABELS = prove
 (`FINITE {i:num | i < 6} /\ FINITE {j:num | j < 9} /\
   (!i. i < 6 ==> moi_ftc_bface i i) /\ (!j. j < 9 ==> moi_ftc_dface j j) /\
   (!i j. i < 6 /\ j < 9 ==> moi_ftc_bd i + moi_ftc_dd j <= 3) /\
   (!i i'. i < 6 /\ moi_ftc_bface i i'
           ==> i' < 6 /\ (i' = i \/ moi_ftc_bd i' < moi_ftc_bd i)) /\
   (!j j'. j < 9 /\ moi_ftc_dface j j'
           ==> j' < 9 /\ (j' = j \/ moi_ftc_dd j' < moi_ftc_dd j))`,
  REWRITE_TAC[FINITE_NUMSEG_LT; moi_ftc_bface; moi_ftc_dface] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ftc_bd; moi_ftc_dd] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT COND_CASES_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_ftc_bd] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_ftc_dd] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_FTC_ZA_INTER = prove
 (`!(t:(real^N->bool)->bool) l v u u' x.
     graph_in_complex t l /\ moi_ftc_blk t v u u' x /\
     segment[v,u] IN l /\ segment[u,u'] IN l /\ segment[v,u'] IN l
     ==> !j j'. j < 9 /\ j' < 9
                ==> moi_ftc_za t l v u u' x j INTER moi_ftc_za t l v u u' x j' =
                    UNIONS {moi_ftc_za t l v u u' x j'' | j'' |
                            j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftc_za] THEN
  MATCH_MP_TAC MOI_FTC_ZD_INTER THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_R1 THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FTC_R3 THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FTC_R4 THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_FTC_TRI_UNION = prove
 (`!(t:(real^N->bool)->bool) l v u u' x (Ca:real^N->bool) Cb Cc.
     UNIONS {moi_ftc_cb Ca Cb Cc i INTER moi_ftc_za t l v u u' x j | i < 6 /\ j < 9} =
     Ca UNION Cb UNION Cc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_za] THEN
  MP_TAC(ISPEC `moi_ftc_om (v:real^N) u u' x` RELATIVE_INTERIOR_SUBSET) THEN
  ABBREV_TAC `Om = moi_ftc_om (v:real^N) u u' x` THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "IN" (concl th))) THEN
    UNDISCH_TAC `i < 6` THEN REWRITE_TAC[MOI_FTC_LT6] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[moi_ftc_cb] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN SET_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?j. j < 9 /\
          (y:real^N) IN moi_ftc_zd Om ((:real^N) DIFF relative_interior Om)
                         (convex hull {v,u,u'}) (moi_ftc_fin v u u' x) (moi_ftc_xs t l v u u')
                         (moi_ftc_core v u u') j`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `(y:real^N) IN Om` THENL
       [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV;
        EXISTS_TAC `1` THEN REWRITE_TAC[moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?i. i < 6 /\ (y:real^N) IN moi_ftc_cb Ca Cb Cc i` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN Ca UNION Cb UNION Cc` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THENL [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`] THEN
      REWRITE_TAC[moi_ftc_cb] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[IN_INTER]]);;

let MOI_FTC_EDGE_IN_CELLS = prove
 (`!(t:(real^N->bool)->bool) l a b.
     graph_in_complex t l /\ {a} IN l /\ {b} IN l /\ ~(a = b) /\ segment[a,b] IN l
     ==> segment[a,b] SUBSET derived_dual_cell t l a UNION derived_dual_cell t l b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[b:real^N,a] IN l` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`]
    MOI_FTA_HALF_EDGE) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `b:real^N`; `a:real^N`]
    MOI_FTA_HALF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] = segment[a,midpoint(a,b)] UNION segment[midpoint(a,b),b]`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC UNION_SEGMENT THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[MIDPOINT_SYM; SEGMENT_SYM] THEN SET_TAC[]);;

(* All 54 cells of the three blocks, in the product-assembly form.          *)

let MOI_FTC_ORIG_CELLS = prove
 (`!(t:(real^N->bool)->bool) l h k a b c x.
     graph_in_complex t l /\ moi_ftc_lev t l {a,b,c} h k /\ moi_ftc_blk t a b c x /\
     segment[a,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l
     ==> !i j. i < 6 /\ j < 9
               ==> pl_cell_with_boundary (moi_ftc_bd i + moi_ftc_dd j)
                     (moi_ftc_cb (derived_dual_cell t l a) (derived_dual_cell t l b)
                                 (derived_dual_cell t l c) i INTER moi_ftc_za t l a b c x j)
                     ((moi_ftc_cb (derived_dual_cell t l a) (derived_dual_cell t l b)
                                  (derived_dual_cell t l c) i INTER
                       UNIONS {moi_ftc_za t l a b c x j' | j' |
                               j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                      (UNIONS {moi_ftc_cb (derived_dual_cell t l a) (derived_dual_cell t l b)
                                          (derived_dual_cell t l c) i' | i' |
                               i' < 6 /\ moi_ftc_bface i i' /\ ~(i' = i)} INTER
                       moi_ftc_za t l a b c x j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTC_BLK_PERM) THEN
  SUBGOAL_THEN `segment[b:real^N,a] IN l /\ segment[c,a] IN l /\ segment[c,b] IN l`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `c:real^N`; `x:real^N`] MOI_FTC_ZA_CYC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{a:real^N,b,c}`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `a:real^N`; `b:real^N`;
                   `c:real^N`; `x:real^N`] MOI_FTC_BLOCK_CELLS) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{a:real^N,b,c}`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `b:real^N`; `c:real^N`;
                   `a:real^N`; `x:real^N`] MOI_FTC_BLOCK_CELLS) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{a:real^N,b,c}`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `c:real^N`; `a:real^N`;
                   `b:real^N`; `x:real^N`] MOI_FTC_BLOCK_CELLS) THEN
    REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(LABEL_TAC "cc") THEN DISCH_THEN(LABEL_TAC "cb") THEN DISCH_THEN(LABEL_TAC "ca") THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  USE_THEN "ca" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `j < 9`))) THEN
  USE_THEN "cb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `j < 9`))) THEN
  USE_THEN "cc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `j < 9`))) THEN
  ABBREV_TAC `Ca = derived_dual_cell t l (a:real^N)` THEN
  ABBREV_TAC `Cb = derived_dual_cell t l (b:real^N)` THEN
  ABBREV_TAC `Cc = derived_dual_cell t l (c:real^N)` THEN
  UNDISCH_TAC `i < 6` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[MOI_FTC_LT6]) THEN
  REWRITE_TAC[MOI_FTC_CB_BD] THEN REWRITE_TAC[moi_ftc_cb; moi_ftc_bd] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[INTER_EMPTY; UNION_EMPTY; ADD_CLAUSES] THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(Ca:real^N->bool) INTER Cb UNION Cb INTER Cc = Cb INTER Cc UNION Cb INTER Ca`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(Cb:real^N->bool) INTER Cc UNION Ca INTER Cc = Cc INTER Ca UNION Cc INTER Cb`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(Ca:real^N->bool) INTER Cc = Cc INTER Ca` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* The assembly map from the three blocks onto the model, cell by cell.     *)

let MOI_FTC_TRI_ASSEMBLY = prove
 (`!(t:(real^N->bool)->bool) l h k a b c x (a':real^2) b' c'.
     graph_in_complex t l /\ moi_ftc_lev t l {a,b,c} h k /\ moi_ftc_blk t a b c x /\
     segment[a,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l /\
     {a} IN l /\ {b} IN l /\ {c} IN l /\ ~collinear {a',b',c'}
     ==> ?f. pl_map_on (derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                        derived_dual_cell t l c) f /\
             (!y z. y IN derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                         derived_dual_cell t l c /\
                    z IN derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                         derived_dual_cell t l c /\ f y = f z
                    ==> y = z) /\
             (!i j. i < 6 /\ j < 9
                    ==> IMAGE f (moi_ftc_cb (derived_dual_cell t l a) (derived_dual_cell t l b)
                                            (derived_dual_cell t l c) i INTER
                                 moi_ftc_za t l a b c x j) =
                        moi_ftc_mcb a' b' c' i INTER moi_ftc_mzd a' b' c' j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_blk]) THEN
  MP_TAC(ISPECL [`a':real^2`; `b':real^2`; `c':real^2`] MOI_FTC_MODEL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`derived_dual_cell t l (a:real^N)`; `derived_dual_cell t l (b:real^N)`;
                 `derived_dual_cell t l (c:real^N)`] MOI_FTC_CB_INTER) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_FTC_TRIPLE THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `c:real^N`; `x:real^N`] MOI_FTC_ZA_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`]
    MOI_FTC_ORIG_CELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`{i:num | i < 6}`; `moi_ftc_bface`; `moi_ftc_bd`; `{j:num | j < 9}`;
                 `moi_ftc_dface`; `moi_ftc_dd`;
                 `moi_ftc_cb (derived_dual_cell t l (a:real^N)) (derived_dual_cell t l b)
                             (derived_dual_cell t l c)`;
                 `moi_ftc_za (t:(real^N->bool)->bool) l a b c x`;
                 `moi_ftc_mcb (a':real^2) b' c'`; `moi_ftc_mzd (a':real^2) b' c'`]
    MOI_FTC_PROD_ASSEMBLY) THEN
  REWRITE_TAC[IN_ELIM_THM; MOI_FTC_TRI_UNION] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_FTC_LABELS] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    TRY CONJ_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The solid torus of a 2-simplex s of t with edges in l: the union of the   *)
(* dual cells of its vertices is PL homeomorphic to the model Bd(triangle)   *)
(* PCROSS square, with Bd s the core: the main theorem                       *)
(* GRAPH_TUBE_TRIANGLE_SOLID_TORUS = MOI_FND_SOLID_TORUS_TRIANGLE.           *)
(* ========================================================================= *)

let MOI_FTC_IMAGE_UNIONS1 = prove
 (`!(f:A->B) (X:num->A->bool) (Y:num->B->bool) P.
     (!i. P i ==> IMAGE f (X i) = Y i)
     ==> IMAGE f (UNIONS {X i | P i}) = UNIONS {Y i | P i}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{(Y:num->B->bool) i | P i} = {IMAGE (f:A->B) (X i) | P i}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_IMAGE_UNIONS2 = prove
 (`!(f:A->B) (X:num->num->A->bool) (Y:num->num->B->bool) P.
     (!i j. P i j ==> IMAGE f (X i j) = Y i j)
     ==> IMAGE f (UNIONS {X i j | P i j}) = UNIONS {Y i j | P i j}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{(Y:num->num->B->bool) i j | P i j} = {IMAGE (f:A->B) (X i j) | P i j}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTC_FINITE_GSPEC2 = prove
 (`!(f:num->num->A) m n. FINITE {f i j | i < m /\ j < n}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->num->A`; `{i:num | i < m}`; `\i:num. {j:num | j < n}`]
    FINITE_PRODUCT_DEPENDENT) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]);;

let MOI_FTC_SPINE_SET = prove
 (`!(t:(real^N->bool)->bool) l v u u' x (Ca:real^N->bool) Cb Cc.
     UNIONS {moi_ftc_cb Ca Cb Cc i INTER moi_ftc_za t l v u u' x 6 | i | i < 6} =
     (Ca UNION Cb UNION Cc) INTER moi_ftc_core v u u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_za; moi_ftc_zd] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; MOI_FTC_IN_UNIONS_GSPEC; MOI_FTC_EX6] THEN
  REWRITE_TAC[moi_ftc_cb] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_FTC_TRI_VERTS = prove
 (`!(t:(real^N->bool)->bool) l a b c.
     graph_in_complex t l /\ convex hull {a,b,c} IN t /\ ~affine_dependent {a,b,c} /\
     {a} IN l /\ {b} IN l /\ {c} IN l
     ==> UNIONS {derived_dual_cell t l v | v | v IN convex hull {a,b,c} /\ {v} IN l} =
         derived_dual_cell t l a UNION derived_dual_cell t l b UNION
         derived_dual_cell t l c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex]) THEN
  SUBGOAL_THEN
   `!v:real^N. v IN convex hull {a,b,c} /\ {v} IN l <=> v = a \/ v = b \/ v = c`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(v:real^N) extreme_point_of convex hull {a,b,c}` MP_TAC THENL
       [MATCH_MP_TAC MOI_FTC_VERTEX_OF THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(l:(real^N->bool)->bool) SUBSET t` THEN
        UNDISCH_TAC `{v:real^N} IN l` THEN SET_TAC[];
        ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; MOI_FTC_IN_UNIONS_GSPEC; IN_UNION] THEN MESON_TAC[]);;

(* The PL homeomorphism from the model onto N_s; the core goes to the core. *)

let MOI_FTC_TRI_HOMEO = prove
 (`!(t:(real^N->bool)->bool) l h k a b c x.
     graph_in_complex t l /\ moi_ftc_lev t l {a,b,c} h k /\ moi_ftc_blk t a b c x /\
     segment[a,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l /\
     {a} IN l /\ {b} IN l /\ {c} IN l
     ==> ?g f. pl_homeomorphism
                 (relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}) PCROSS
                  interval[--vec 1:real^2,vec 1],
                  derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                  derived_dual_cell t l c) (g,f) /\
               IMAGE g (relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}) PCROSS
                        {vec 0:real^2}) =
               (derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                derived_dual_cell t l c) INTER moi_ftc_core a b c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0:real^2,basis 1,basis 2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_STD_NONCOLLINEAR THEN REWRITE_TAC[DIMINDEX_2; LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`;
                 `vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] MOI_FTC_TRI_ASSEMBLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^(2,2)finite_sum`
    (CONJUNCTS_THEN2 (LABEL_TAC "pl") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "im")))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] MOI_FTC_MODEL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "mu") (LABEL_TAC "m6"))))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`]
    MOI_FTC_ORIG_CELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "oc")] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `c:real^N`; `x:real^N`; `derived_dual_cell t l (a:real^N)`;
                 `derived_dual_cell t l (b:real^N)`; `derived_dual_cell t l (c:real^N)`]
    MOI_FTC_TRI_UNION) THEN
  DISCH_THEN(LABEL_TAC "tu") THEN
  SUBGOAL_THEN
   `compact (derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b UNION
             derived_dual_cell t l c)`
  ASSUME_TAC THENL
   [USE_THEN "tu" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    REWRITE_TAC[MOI_FTC_FINITE_GSPEC2; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "oc" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o MATCH_MP MOI_CEL_CELL_COMPACT)] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^(2,2)finite_sum)
      (derived_dual_cell t l a UNION derived_dual_cell t l b UNION derived_dual_cell t l c) =
    relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}) PCROSS
    interval[--vec 1:real^2,vec 1]`
  ASSUME_TAC THENL
   [USE_THEN "tu" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    USE_THEN "mu" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC MOI_FTC_IMAGE_UNIONS2 THEN REWRITE_TAC[] THEN USE_THEN "im" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b UNION
                  derived_dual_cell t l c`;
                 `f:real^N->real^(2,2)finite_sum`;
                 `relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2}) PCROSS
                  interval[--vec 1:real^2,vec 1]`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN USE_THEN "pl" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "inj" ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `g:real^(2,2)finite_sum->real^N`)] THEN
  MAP_EVERY EXISTS_TAC [`g:real^(2,2)finite_sum->real^N`; `f:real^N->real^(2,2)finite_sum`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN REWRITE_TAC[pl_homeomorphism] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "pl" ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    EXISTS_TAC `derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b UNION
                derived_dual_cell t l c` THEN
    EXISTS_TAC `f:real^N->real^(2,2)finite_sum` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; USE_THEN "pl" ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  USE_THEN "m6" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `c:real^N`; `x:real^N`; `derived_dual_cell t l (a:real^N)`;
                 `derived_dual_cell t l (b:real^N)`; `derived_dual_cell t l (c:real^N)`]
    MOI_FTC_SPINE_SET) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_FTC_IMAGE_UNIONS1 THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_ftc_cb (derived_dual_cell t l (a:real^N)) (derived_dual_cell t l b)
               (derived_dual_cell t l c) i INTER moi_ftc_za t l a b c x 6 SUBSET
    derived_dual_cell t l a UNION derived_dual_cell t l b UNION derived_dual_cell t l c`
  ASSUME_TAC THENL
   [USE_THEN "tu" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `6`] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "im" (MP_TAC o SPECL [`i:num`; `6`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC
   `moi_ftc_cb (derived_dual_cell t l (a:real^N)) (derived_dual_cell t l b)
               (derived_dual_cell t l c) i INTER moi_ftc_za t l a b c x 6 SUBSET
    derived_dual_cell t l a UNION derived_dual_cell t l b UNION derived_dual_cell t l c` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `g:real^(2,2)finite_sum->real^N`)) (concl th) &&
    can (find_term ((=) `f:real^N->real^(2,2)finite_sum`)) (concl th) &&
    not (can (find_term ((=) `relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2})`))
             (concl th)))) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

let MOI_FTC_TRI_TORUS = prove
 (`!(t:(real^N->bool)->bool) l a b c x.
     graph_in_complex t l /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     ~(x = a) /\ ~(x = b) /\ ~(x = c) /\ ~affine_dependent {a,b,c,x} /\
     convex hull {a,b,c,x} IN t /\
     segment[a,b] IN l /\ segment[b,c] IN l /\ segment[a,c] IN l /\
     {a} IN l /\ {b} IN l /\ {c} IN l
     ==> pl_solid_torus (derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                         derived_dual_cell t l c) /\
         spine (relative_frontier (convex hull {a,b,c}))
               (derived_dual_cell t l a UNION derived_dual_cell t l b UNION
                derived_dual_cell t l c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_ftc_blk t a b c (x:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_blk] THEN ASM_MESON_TAC[graph_in_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{a:real^N,b,c}`]
    MOI_FTC_LEV_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                    NOT_INSERT_EMPTY];
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_TAC `k:real^N->real^N`))] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`]
    MOI_FTC_TRI_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(2,2)finite_sum->real^N`
    (X_CHOOSE_THEN `f:real^N->real^(2,2)finite_sum` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`relative_frontier(convex hull {vec 0:real^2,basis 1,basis 2})`;
                 `derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b UNION
                  derived_dual_cell t l c`;
                 `g:real^(2,2)finite_sum->real^N`; `f:real^N->real^(2,2)finite_sum`]
    MOI_FTC_TORUS_SPINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[ARITH] (SPEC `1` PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX)) THEN
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SS2_STD_NONCOLLINEAR THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `g:real^(2,2)finite_sum->real^N`)) (lhs(concl th)))) THEN
  SUBGOAL_THEN
   `(derived_dual_cell t l (a:real^N) UNION derived_dual_cell t l b UNION
     derived_dual_cell t l c) INTER moi_ftc_core a b c =
    relative_frontier(convex hull {a,b,c})`
  (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~collinear {a:real^N,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `{a:real^N,b,c,x}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; moi_ftc_core] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`]
    MOI_FTC_EDGE_IN_CELLS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `b:real^N`; `c:real^N`]
    MOI_FTC_EDGE_IN_CELLS) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `c:real^N`]
    MOI_FTC_EDGE_IN_CELLS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

(* The main theorem (Moise p.240, N_sigma is a solid torus with spine       *)
(* Bd sigma).                                                                *)

let GRAPH_TUBE_TRIANGLE_SOLID_TORUS = prove
 (MOI_FND_SOLID_TORUS_TRIANGLE,
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FTC_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = convex hull {a:real^N,b,c}`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `c:real^N`] MOI_FTC_TRI_VERTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{a:real^N,b,c,x}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_FTC_TRI_TORUS THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]);;

