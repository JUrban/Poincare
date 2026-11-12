needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_s35_triple.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_recoga: the target cells of the Sec 34 cell diagram (Moise,   *)
(* Geometric Topology in Dimensions 2 and 3, GTM 47, Sec 34, pp.244-246,    *)
(* stages (1)-(7), target side).  Main theorem (pc_moi_s34_stmt.ml):         *)
(*   RECOG_A = MOI_S34_RECOG_A                                              *)
(* i.e. for b = moi_s34_tgt tt kk f1 dd rr every target b l of a source     *)
(* cell l is a PL cell of the dimension of l whose boundary is the union of *)
(* the targets of the source cells properly contained in l.                 *)
(* Route.                                                                    *)
(* (1) Source side.  Each source cell has a witness point: the vertex v for *)
(* the vertex ball, the midpoint for a splitting disk, and for the cells    *)
(* inside a simplex q of kk a relative interior point of q with prescribed  *)
(* flat barycentric coordinates (2/5 on the vertex or on the edge, equal    *)
(* smaller coordinates elsewhere; the flat retriangulation of               *)
(* MOI_S4A_FLAT_KK); the outer cells use a point of a boundary arc or a     *)
(* marked point, a point off |kk| and MOI_S4O_FR.  Membership of the        *)
(* witnesses decides all inclusions between source cells; hence a source    *)
(* cell determines its kind and index, and b is evaluated by kinds.         *)
(* (2) Target side.  The hypotheses (frame, fdisk, resid, outer) give each  *)
(* target as a PL cell whose boundary is written with other targets; this   *)
(* boundary is the union of the targets of the proper faces.                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Labels of source cells and the face relation by kinds.                   *)
(* A label is a kind k (1-10, the ten families of moi_s34_scells, in order) *)
(* with a simplex q and a second set x: vertex balls ({v},{}), splitting    *)
(* disks (g,{}), face disks (s,{}), tetra balls (r,{}), patches (r,{v}),    *)
(* face arcs (s,{v}), edge arcs (r,g), marked points (s,g), outer patches   *)
(* ({v},{}) and outer arcs (g,{}).                                           *)
(* ------------------------------------------------------------------------- *)

let moi_s4g_lab = new_definition
 `moi_s4g_lab (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (l:real^N->bool) (k:num) (q:real^N->bool) (x:real^N->bool) <=>
   (k = 1 /\ x = {} /\ ?v. {v} IN kk /\ q = {v} /\ l = moi_s34_vb tt kk v) \/
   (k = 2 /\ x = {} /\ q IN moi_s34_simp kk (&1) /\ l = moi_s34_sd tt kk q) \/
   (k = 3 /\ x = {} /\ q IN moi_s34_simp kk (&2) /\
    l = closure (q DIFF moi_s34_nb tt kk)) \/
   (k = 4 /\ x = {} /\ q IN moi_s34_simp kk (&3) /\
    l = closure (q DIFF moi_s34_nb tt kk)) \/
   (k = 5 /\ q IN moi_s34_simp kk (&3) /\
    ?v. v IN q /\ {v} IN kk /\ x = {v} /\
        l = q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) \/
   (k = 6 /\ q IN moi_s34_simp kk (&2) /\
    ?v. v IN q /\ {v} IN kk /\ x = {v} /\
        l = q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) \/
   (k = 7 /\ q IN moi_s34_simp kk (&3) /\ x IN moi_s34_simp kk (&1) /\ x SUBSET q /\
    l = q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) \/
   (k = 8 /\ q IN moi_s34_simp kk (&2) /\ x IN moi_s34_simp kk (&1) /\ x SUBSET q /\
    l = q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk) \/
   (k = 9 /\ x = {} /\
    ?v. {v} IN kk /\ v IN complex_boundary kk /\ q = {v} /\
        l = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)) \/
   (k = 10 /\ x = {} /\ q IN moi_s34_simp kk (&1) /\ q SUBSET complex_boundary kk /\
    l = closure ((moi_s34_sd tt kk q INTER moi_s34_bd tt kk) DIFF UNIONS kk))`;;

(* The face relation between labels: (k',q',x') is (k,q,x) or a proper face  *)
(* of it.  Kind dimensions: 3 for kinds 1, 4; 2 for 2, 3, 5, 9; 1 for 6, 7, *)
(* 10; 0 for 8.                                                               *)

let moi_s4g_face = new_definition
 `moi_s4g_face (kk:(real^N->bool)->bool) (k':num) (q':real^N->bool) (x':real^N->bool)
               (k:num) (q:real^N->bool) (x:real^N->bool) <=>
   (k' = k /\ q' = q /\ x' = x) \/
   (k = 1 /\ (k' = 2 /\ q SUBSET q' \/ (k' = 5 \/ k' = 6) /\ x' = q \/
              (k' = 7 \/ k' = 8) /\ q SUBSET x' \/ k' = 9 /\ q' = q \/
              k' = 10 /\ q SUBSET q')) \/
   (k = 2 /\ ((k' = 7 \/ k' = 8) /\ x' = q \/ k' = 10 /\ q' = q)) \/
   (k = 3 /\ (k' = 6 \/ k' = 8) /\ q' = q) \/
   (k = 4 /\ ((k' = 3 \/ k' = 6 \/ k' = 8) /\ q' SUBSET q \/
              (k' = 5 \/ k' = 7) /\ q' = q)) \/
   (k = 5 /\ (k' = 6 /\ q' SUBSET q /\ x' = x \/ k' = 7 /\ q' = q /\ x SUBSET x' \/
              k' = 8 /\ q' SUBSET q /\ x SUBSET x')) \/
   (k = 6 /\ k' = 8 /\ q' = q /\ x SUBSET x') \/
   (k = 7 /\ k' = 8 /\ q' SUBSET q /\ x' = x) \/
   (k = 9 /\ (k' = 6 /\ x' = q /\ q' SUBSET complex_boundary kk \/
              k' = 8 /\ q SUBSET x' /\ q' SUBSET complex_boundary kk \/
              k' = 10 /\ q SUBSET q')) \/
   (k = 10 /\ k' = 8 /\ x' = q /\ q' SUBSET complex_boundary kk)`;;

(* Source cells are exactly the sets with a label. *)

let MOI_S4G_SCELLS_LAB = prove
 (`!(tt:(real^N->bool)->bool) kk l.
     l IN moi_s34_scells tt kk <=> ?k q x. moi_s4g_lab tt kk l k q x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_scells; moi_s4g_lab; IN_UNION; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `{v:real^N}`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`2`; `g:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`3`; `s:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`4`; `r:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`5`; `r:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`6`; `s:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`7`; `r:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`8`; `s:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`9`; `{v:real^N}`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`10`; `g:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic facts about simplices, vertex balls and relative                   *)
(* interiors.                                                                *)
(* ------------------------------------------------------------------------- *)

(* A vertex of a locally finite complex lying in a simplex is a vertex of   *)
(* that simplex.                                                             *)

let MOI_S4G_VTX_C = prove
 (`!(c:(real^N->bool)->bool) V v.
     lf_simplicial_complex c /\ convex hull V IN c /\ ~affine_dependent V /\
     {v} IN c /\ v IN convex hull V
     ==> v IN V`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `({v:real^N} INTER convex hull V) face_of convex hull V` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N} INTER convex hull V = {v}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N->bool) SUBSET {v}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull (E:real^N->bool)` THEN
    REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(E:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `{v:real^N} INTER convex hull V = convex hull E` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Points in the relative interior of a simplex of a complex: any simplex   *)
(* of the complex containing such a point contains the whole simplex.        *)

let MOI_S4G_RELINT_SUB = prove
 (`!(c:(real^N->bool)->bool) V q' w.
     lf_simplicial_complex c /\ convex hull V IN c /\ ~affine_dependent V /\
     w IN convex hull V /\ (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
     q' IN c /\ w IN q'
     ==> convex hull V SUBSET q'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(convex hull V INTER q':real^N->bool) face_of convex hull V` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `E:real^N->bool = V` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]);;

(* Injectivity transfer: membership is detected by the image. *)

let MOI_S4G_INJ_IN = prove
 (`!(h:real^N->real^N) k Q A w.
     (!x. x IN Q ==> k(h x) = x) /\ A SUBSET Q /\ w IN Q /\ h w IN IMAGE h A
     ==> w IN A`,
  REWRITE_TAC[IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

(* The vertex ball of a vertex u of kk misses every simplex of kk not      *)
(* containing u (first-derived stars: the coordinate of u is maximal).      *)

let MOI_S4G_VB_OUT = prove
 (`!(tt:(real^N->bool)->bool) kk u q.
     moi_s34_tube tt kk /\ {u} IN kk /\ q IN kk /\ ~(u IN q)
     ==> moi_s34_vb tt kk u INTER q = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN skeleton 1 kk` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN tt` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN tt /\ u IN sg /\ x IN sg` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_vb tt kk u SUBSET UNIONS {s | s IN tt /\ (u:real^N) IN s}` THEN
    UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Vs:real^N->bool. ~affine_dependent Vs /\ sg = convex hull Vs`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; simplex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN Vs` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^N) IN UNIONS {s | s IN barycentric_subdivision tt /\ (u:real^N) IN s}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u` THEN
    REWRITE_TAC[moi_s34_vb; derived_dual_cell; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN Vs ==> moi_s4a_bc Vs a x <= moi_s4a_bc Vs u x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sg:real^N->bool`; `u:real^N`]
                  MOI_S4A_STAR_IN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sg:real^N->bool = convex hull Vs` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[MOI_S4A_BC_STAR] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q INTER sg:real^N->bool) face_of sg` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  UNDISCH_TAC `sg:real^N->bool = convex hull Vs` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull E` ASSUME_TAC THENL
   [UNDISCH_TAC `q INTER convex hull Vs:real^N->bool = convex hull E` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N) IN E)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N) IN convex hull E` MP_TAC THENL
     [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
    UNDISCH_TAC `q INTER convex hull Vs:real^N->bool = convex hull E` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4a_bc Vs (u:real^N) x = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Vs:real^N->bool`; `E:real^N->bool`] MOI_S4A_BC_SUBHULL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Vs:real^N->bool`; `x:real^N`] MOI_S4A_BC_HULL_EXPAND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `Vs:real^N->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &0 ==> s = &1 ==> F`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum (Vs:real^N->bool) (\a. &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `moi_s4a_bc Vs (u:real^N) x` THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    REWRITE_TAC[SUM_0; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The flat picture of a simplex q = convex hull V of kk (from               *)
(* MOI_S4A_FLAT_KK) as membership tests in barycentric coordinates of h x,  *)
(* and witness points with prescribed flat coordinates.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_TRANSFER = prove
 (`!(h:real^N->real^N) k Q A B x.
     (!y. y IN Q ==> k(h y) = y) /\ A SUBSET Q /\ IMAGE h A = B /\ x IN Q
     ==> (x IN A <=> h x IN B)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

let MOI_S4G_FLAT_MEM = prove
 (`!(tt:(real^N->bool)->bool) kk V.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V
     ==> ?h:real^N->real^N.
           (!x. x IN convex hull V ==> h x IN convex hull V) /\
           (!y. y IN convex hull V ==> ?x. x IN convex hull V /\ h x = y) /\
           (!E x. E SUBSET V /\ x IN convex hull V
                  ==> (h x IN convex hull E <=> x IN convex hull E)) /\
           (!u x. u IN V /\ x IN convex hull V
                  ==> (x IN moi_s34_vb tt kk u <=>
                       (?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a (h x)) /\
                       (!a. a IN V ==> moi_s4a_bc V a (h x) <= moi_s4a_bc V u (h x)))) /\
           (!x. x IN convex hull V
                ==> (x IN moi_s34_nb tt kk <=>
                     ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a (h x))) /\
           (!x. x IN convex hull V
                ==> (x IN moi_s34_bd tt kk <=>
                     (!a. a IN V ==> moi_s4a_bc V a (h x) <= &2 / &5) /\
                     (?a. a IN V /\ moi_s4a_bc V a (h x) = &2 / &5))) /\
           (!x. x IN convex hull V
                ==> (x IN closure (convex hull V DIFF moi_s34_nb tt kk) <=>
                     !a. a IN V ==> moi_s4a_bc V a (h x) <= &2 / &5))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4A_FLAT_KK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `h:real^N->real^N` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  SUBGOAL_THEN `closed(convex hull V:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN convex hull V ==> k((h:real^N->real^N) x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (convex hull V DIFF moi_s34_nb tt kk) SUBSET
                (convex hull V:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN convex hull V ==> (h:real^N->real^N) x IN convex hull V`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_S4G_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `convex hull V:real^N->bool`] THEN
    ASM_SIMP_TAC[HULL_MONO];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `x:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(x:real^N) IN moi_s34_vb tt kk u <=> x IN moi_s34_vb tt kk u INTER convex hull V`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> (a /\ b <=> a' /\ b')`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `convex hull V:real^N->bool`;
                     `moi_s34_nb tt kk INTER convex hull V:real^N->bool`;
                     `{x:real^N | x IN convex hull V /\
                                  ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a x}`;
                     `x:real^N`] MOI_S4G_TRANSFER) THEN
      ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `convex hull V:real^N->bool`;
                     `{x:real^N | x IN convex hull V /\
                                  !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V u x}`;
                     `{x:real^N | x IN convex hull V /\
                                  !a. a IN V ==> moi_s4a_bc V a x <= moi_s4a_bc V u x}`;
                     `x:real^N`] MOI_S4G_TRANSFER) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `convex hull V:real^N->bool`;
                   `moi_s34_nb tt kk INTER convex hull V:real^N->bool`;
                   `{x:real^N | x IN convex hull V /\
                                ?a. a IN V /\ &2 / &5 <= moi_s4a_bc V a x}`;
                   `x:real^N`] MOI_S4G_TRANSFER) THEN
    ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `convex hull V:real^N->bool`;
                   `moi_s34_bd tt kk INTER convex hull V:real^N->bool`;
                   `{x:real^N | x IN convex hull V /\
                                (!a. a IN V ==> moi_s4a_bc V a x <= &2 / &5) /\
                                ?a. a IN V /\ moi_s4a_bc V a x = &2 / &5}`;
                   `x:real^N`] MOI_S4G_TRANSFER) THEN
    ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `convex hull V:real^N->bool`;
                   `closure (convex hull V DIFF moi_s34_nb tt kk):real^N->bool`;
                   `{x:real^N | x IN convex hull V /\
                                !a. a IN V ==> moi_s4a_bc V a x <= &2 / &5}`;
                   `x:real^N`] MOI_S4G_TRANSFER) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]]);;

(* Witness points: inside a triangle or tetrahedron q = convex hull V of kk, *)
(* a relative interior point of q with flat coordinates 2/5 exactly on a     *)
(* nonempty set U0 of at most two vertices and equal smaller coordinates     *)
(* elsewhere; it lies in the vertex balls of the vertices of U0 only, on     *)
(* Bd N, and in the closure of q minus N.                                    *)

let MOI_S4G_WITNESS = prove
 (`!(tt:(real^N->bool)->bool) kk V U0.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     (CARD V = 3 \/ CARD V = 4) /\ U0 SUBSET V /\ ~(U0 = {}) /\ CARD U0 <= 2
     ==> ?w. w IN convex hull V /\
             (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
             (!u. u IN V ==> (w IN moi_s34_vb tt kk u <=> u IN U0)) /\
             w IN moi_s34_bd tt kk /\
             w IN closure (convex hull V DIFF moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (U0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(U0:real^N->bool) = 1 \/ CARD U0 = 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(CARD(U0:real^N->bool) = 0)` MP_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V DIFF U0:real^N->bool) = CARD V - CARD U0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `~(V DIFF U0:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `CARD(V DIFF U0:real^N->bool) = CARD V - CARD U0` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `U0:real^N->bool`] MOI_S4A_X0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `c0 = (&1 - &2 / &5 * &(CARD(U0:real^N->bool))) /
                   &(CARD(V DIFF U0:real^N->bool))` THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 < &2 / &5` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN
    UNDISCH_TAC `CARD(V DIFF U0:real^N->bool) = CARD V - CARD U0` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `CARD(U0:real^N->bool) = 1 \/ CARD U0 = 2` THEN
    UNDISCH_TAC `CARD(V:real^N->bool) = 3 \/ CARD V = 4` THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. a IN V
               ==> &0 < moi_s4a_bc V a x0 /\ moi_s4a_bc V a x0 <= &2 / &5 /\
                   (moi_s4a_bc V a x0 = &2 / &5 <=> a IN U0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `(a:real^N) IN U0` THENL
     [SUBGOAL_THEN `moi_s4a_bc V (a:real^N) x0 = &2 / &5` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `moi_s4a_bc V (a:real^N) x0 = c0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_var t && fst(dest_var t) = "c0")) (concl th))) THEN
        ASM_REWRITE_TAC[IN_DIFF];
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN convex hull V` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4A_BC_CONVEX_HULL] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w:real^N. w IN convex hull V /\ (h:real^N->real^N) w = x0`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x0:real^N) IN convex hull E` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_BC_SUBHULL; IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s4a_bc V (a:real^N) x0 = &0` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x = &0 ==> F`) THEN ASM_MESON_TAC[];
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `~(U0:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
      DISCH_THEN(MP_TAC o SPEC `b:real^N`) THEN
      SUBGOAL_THEN `(b:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_s4a_bc V (b:real^N) x0 = &2 / &5` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `moi_s4a_bc V (u:real^N) x0 = &2 / &5` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y /\ y <= x ==> y = x`) THEN ASM_MESON_TAC[];
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `moi_s4a_bc V (u:real^N) x0 = &2 / &5` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; REAL_ARITH_TAC];
        X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `moi_s4a_bc V (u:real^N) x0 = &2 / &5` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]];
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `~(U0:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN EXISTS_TAC `b:real^N` THEN
    SUBGOAL_THEN `(b:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Witness points of the face disks and tetra balls (the flat               *)
(* barycentre), of the vertex balls (the vertex) and of the splitting disks  *)
(* (the midpoint of the edge).                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_WITNESS_BARY = prove
 (`!(tt:(real^N->bool)->bool) kk V.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     (CARD V = 3 \/ CARD V = 4)
     ==> ?w. w IN convex hull V /\
             (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
             ~(w IN moi_s34_nb tt kk) /\
             w IN closure (convex hull V DIFF moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(V:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(V:real^N->bool) = 3 \/ CARD V = 4` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^N->bool` MOI_S4A_BARY_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x0 = simplex_barycentre(convex hull V:real^N->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(&(CARD(V:real^N->bool))) /\ inv(&(CARD V)) < &2 / &5`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(V:real^N->bool) = 3 \/ CARD V = 4` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w:real^N. w IN convex hull V /\ (h:real^N->real^N) w = x0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x0:real^N) IN convex hull E` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S4A_BC_SUBHULL; IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s4a_bc V (a:real^N) x0 = &0` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN (ASM_REAL_ARITH_TAC ORELSE ASM_MESON_TAC[REAL_LT_IMP_NZ]);
    SUBGOAL_THEN `!a:real^N. a IN V ==> moi_s4a_bc V a ((h:real^N->real^N) w) < &2 / &5`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The vertex v of a vertex ball. *)

let MOI_S4G_VERTEX_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> v IN moi_s34_vb tt kk v /\
         ~(v IN moi_s34_bd tt kk) /\
         (!u. {u} IN kk /\ v IN moi_s34_vb tt kk u ==> u = v) /\
         (!q. q IN kk ==> ~(v IN closure (q DIFF moi_s34_nb tt kk)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. {w} IN kk ==> {w} IN skeleton 1 kk /\ {w} IN tt`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(LABEL_TAC "gt" o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!w:real^N. {w} IN kk
               ==> w IN moi_s34_vb tt kk w /\
                   {w' | {w'} IN tt /\ w' IN moi_s34_vb tt kk w} = {w}`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "gt" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `UNIONS (skeleton 1 (kk:(real^N->bool)->bool))`))
          (lhand(concl th)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(V:real^N->bool) a. convex hull V IN kk /\ ~affine_dependent V /\
                                      a IN V
                  ==> ~(a IN moi_s34_bd tt kk) /\
                      ~(a IN closure (convex hull V DIFF moi_s34_nb tt kk))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:real^N) IN convex hull V` ASSUME_TAC THENL
     [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) a = a` ASSUME_TAC THENL
     [SUBGOAL_THEN `(h:real^N->real^N) a IN convex hull {a}` MP_TAC THENL
       [UNDISCH_TAC `!E x. E SUBSET V /\ x IN convex hull V
                           ==> ((h:real^N->real^N) x IN convex hull E <=>
                                x IN convex hull E)` THEN
        DISCH_THEN(MP_TAC o SPECL [`{a:real^N}`; `a:real^N`]) THEN
        ASM_REWRITE_TAC[SING_SUBSET; CONVEX_HULL_SING; IN_SING];
        REWRITE_TAC[CONVEX_HULL_SING; IN_SING]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s4a_bc V (a:real^N) a = &1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`] MOI_S4A_BC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s4a_bc V (a:real^N) ((h:real^N->real^N) a) <= &2 / &5` MP_TAC THEN
    ((ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC) ORELSE ASM_MESON_TAC[]);
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; AFFINE_INDEPENDENT_1; IN_SING] THEN MESON_TAC[];
    X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "w'")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `{w' | {w'} IN tt /\ w' IN moi_s34_vb tt kk u} = {u:real^N}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?V:real^N->bool. ~affine_dependent V /\ q = convex hull V`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(q:real^N->bool) IN tt` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex; simplex] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(v:real^N) IN q` THENL
     [SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`V:real^N->bool`; `v:real^N`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "closure")) (concl th))) THEN
      ASM_MESON_TAC[];
      SUBGOAL_THEN `closure (q DIFF moi_s34_nb tt kk) SUBSET (q:real^N->bool)`
      (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]]]);;

(* Tactic: introduce the flat map h of MOI_S4G_FLAT_MEM with its seven      *)
(* clauses labelled fin, fonto, fface, fvb, fnb, fbd, fcl.                     *)

let MOI_S4G_FLAT_THEN (hn:string) =
  DISCH_THEN(X_CHOOSE_THEN (mk_var(hn,`:real^N->real^N`)) (fun th ->
    match CONJUNCTS th with
      [c1;c2;c3;c4;c5;c6;c7] ->
        LABEL_TAC "fin" c1 THEN LABEL_TAC "fonto" c2 THEN LABEL_TAC "fface" c3 THEN
        LABEL_TAC "fvb" c4 THEN LABEL_TAC "fnb" c5 THEN LABEL_TAC "fbd" c6 THEN
        LABEL_TAC "fcl" c7
    | _ -> failwith "MOI_S4G_FLAT_THEN"));;

(* Tactic: rewrite the goal with the consequent of a labelled implication   *)
(* instantiated at tms, its antecedent proved from the assumptions (avoids  *)
(* the collapse of an instance of an assumption under ASM_REWRITE_TAC).      *)

let MOI_S4G_USE_IFF (lab:string) (tms:term list) : tactic =
  USE_THEN lab (MP_TAC o SPECL tms) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])];;

(* Two maximal coordinates at the level 2/5: a point of the closure of q    *)
(* minus N in the vertex balls of two vertices of q lies on Bd N.           *)

let MOI_S4G_TWO_MAX_BD = prove
 (`!(tt:(real^N->bool)->bool) kk W u1 u2 x.
     moi_s34_tube tt kk /\ convex hull W IN kk /\ ~affine_dependent W /\
     u1 IN W /\ u2 IN W /\ x IN convex hull W /\
     x IN moi_s34_vb tt kk u1 /\ x IN moi_s34_vb tt kk u2 /\
     x IN closure (convex hull W DIFF moi_s34_nb tt kk)
     ==> x IN moi_s34_bd tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `W:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MOI_S4G_FLAT_THEN "h"] THEN
  SUBGOAL_THEN `&2 / &5 <= moi_s4a_bc W (u1:real^N) ((h:real^N->real^N) x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u1` THEN
    MOI_S4G_USE_IFF "fvb" [`u1:real^N`; `x:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)
                               (MP_TAC o SPEC `b:real^N`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN W ==> moi_s4a_bc W a ((h:real^N->real^N) x) <= &2 / &5`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN closure (convex hull W DIFF moi_s34_nb tt kk)` THEN
    MOI_S4G_USE_IFF "fcl" [`x:real^N`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MOI_S4G_USE_IFF "fbd" [`x:real^N`] THEN ASM_SIMP_TAC[] THEN EXISTS_TAC `u1:real^N` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y /\ y <= x ==> x = y`) THEN ASM_SIMP_TAC[]);;

(* On an edge, a point in both end vertex balls is off Bd N (its flat       *)
(* coordinates are 1/2, 1/2).                                                *)

let MOI_S4G_EDGE_MID_NOT_BD = prove
 (`!(tt:(real^N->bool)->bool) kk u1 u2 x.
     moi_s34_tube tt kk /\ ~(u1 = u2) /\ convex hull {u1,u2} IN kk /\
     x IN convex hull {u1,u2} /\
     x IN moi_s34_vb tt kk u1 /\ x IN moi_s34_vb tt kk u2
     ==> ~(x IN moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `{u1:real^N,u2}`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2]; MOI_S4G_FLAT_THEN "h"] THEN
  SUBGOAL_THEN `(u1:real^N) IN {u1,u2} /\ u2 IN {u1,u2}` STRIP_ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s4a_bc {u1,u2} u2 ((h:real^N->real^N) x) <= moi_s4a_bc {u1,u2} u1 (h x) /\
    moi_s4a_bc {u1,u2} u1 (h x) <= moi_s4a_bc {u1,u2} (u2:real^N) (h x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u1` THEN
      MOI_S4G_USE_IFF "fvb" [`u1:real^N`; `x:real^N`] THEN
      DISCH_THEN(MP_TAC o SPEC `u2:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk u2` THEN
      MOI_S4G_USE_IFF "fvb" [`u2:real^N`; `x:real^N`] THEN
      DISCH_THEN(MP_TAC o SPEC `u1:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s4a_bc {u1,u2} u1 ((h:real^N->real^N) x) +
    moi_s4a_bc {u1,u2} (u2:real^N) (h x) = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{u1:real^N,u2}`; `(h:real^N->real^N) x`] MOI_S4A_BC_HULL_EXPAND) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
      MP_TAC(ISPEC `{u1:real^N,u2}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_s34_bd tt kk` THEN
  MOI_S4G_USE_IFF "fbd" [`x:real^N`] THEN
  DISCH_THEN(MP_TAC o SPEC `u1:real^N` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The midpoint of an edge of kk: it lies on the splitting disk, in the     *)
(* relative interior of the edge, in exactly the two vertex balls of the     *)
(* ends, off Bd N, and in no closure of a simplex minus N.                   *)

let MOI_S4G_MIDPOINT_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk u1 u2.
     moi_s34_tube tt kk /\ ~(u1 = u2) /\ convex hull {u1,u2} IN kk
     ==> midpoint(u1,u2) IN moi_s34_sd tt kk (convex hull {u1,u2}) /\
         midpoint(u1,u2) IN convex hull {u1,u2} /\
         (!E. E SUBSET {u1,u2} /\ midpoint(u1,u2) IN convex hull E ==> E = {u1,u2}) /\
         ~(midpoint(u1,u2) IN moi_s34_bd tt kk) /\
         (!u. {u} IN kk
              ==> (midpoint(u1,u2) IN moi_s34_vb tt kk u <=> u = u1 \/ u = u2)) /\
         (!q. q IN kk ==> ~(midpoint(u1,u2) IN closure (q DIFF moi_s34_nb tt kk)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `{u1:real^N} IN kk /\ {u2:real^N} IN kk` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4A_VTX_KK; AFFINE_INDEPENDENT_2; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (convex hull {u1,u2}) =
                moi_s34_vb tt kk u1 INTER moi_s34_vb tt kk (u2:real^N)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_SD_EDGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m:real^N = midpoint(u1,u2)` THEN
  SUBGOAL_THEN `(m:real^N) IN moi_s34_vb tt kk u1 /\ m IN moi_s34_vb tt kk u2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                  GRAPH_TUBE_DUAL_CELLS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
    REWRITE_TAC[GSYM moi_s34_vb] THEN
    DISCH_THEN(MP_TAC o SPECL [`u1:real^N`; `u2:real^N`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; skeleton; IN_ELIM_THM;
                      AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN convex hull {u1,u2}` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!E. E SUBSET {u1,u2} /\ (m:real^N) IN convex hull E ==> E = {u1,u2}`
  ASSUME_TAC THENL
   [X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(u1:real^N) IN E` THEN ASM_CASES_TAC `(u2:real^N) IN E` THENL
     [ASM SET_TAC[];
      SUBGOAL_THEN `convex hull E SUBSET convex hull {u1:real^N}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_HULL_SING; SUBSET; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `m:real^N`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "m" THEN ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT];
      SUBGOAL_THEN `convex hull E SUBSET convex hull {u2:real^N}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_HULL_SING; SUBSET; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `m:real^N`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "m" THEN ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT];
      SUBGOAL_THEN `E:real^N->bool = {}` SUBST_ALL_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `(m:real^N) IN convex hull {}` THEN
        REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((m:real^N) IN moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4G_EDGE_MID_NOT_BD THEN
    MAP_EVERY EXISTS_TAC [`u1:real^N`; `u2:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. {u} IN kk ==> (m IN moi_s34_vb tt kk u <=> u = u1 \/ u = u2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `~((u:real^N) IN convex hull {u1,u2})` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(u:real^N) IN {u1,u2}` MP_TAC THENL
         [MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
          ASM_SIMP_TAC[AFFINE_INDEPENDENT_2];
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N`;
                     `convex hull {u1:real^N,u2}`] MOI_S4G_VB_OUT) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `m:real^N`) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?W:real^N->bool. ~affine_dependent W /\ q = convex hull W`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(q:real^N->bool) IN tt` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; simplex] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(m:real^N) IN q` THENL
   [ALL_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~((m:real^N) IN q)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `closure (q DIFF moi_s34_nb tt kk) SUBSET (q:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
      ASM SET_TAC[]]] THEN
  SUBGOAL_THEN `convex hull {u1:real^N,u2} SUBSET q` ASSUME_TAC THENL
   [UNDISCH_TAC `q:real^N->bool = convex hull W` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S4G_RELINT_SUB THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    EXISTS_TAC `m:real^N` THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u1:real^N) IN W /\ u2 IN W` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(u1:real^N) IN q /\ u2 IN q` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{u1:real^N,u2}`] HULL_SUBSET) THEN
      UNDISCH_TAC `convex hull {u1:real^N,u2} SUBSET q` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_S4G_VTX_C THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~((m:real^N) IN moi_s34_bd tt kk)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S4G_TWO_MAX_BD THEN
  MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `u1:real^N`; `u2:real^N`] THEN
  UNDISCH_TAC `q:real^N->bool = convex hull W` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cells are compact and contain their boundaries; the outer cells           *)
(* lie on Bd N and meet |kk| only in its boundary; the membership profile of *)
(* a relative interior point of a simplex of kk in every kind of cell.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_CELL_FACTS = prove
 (`!n (s:real^N->bool) b.
     pl_cell_with_boundary n s b ==> compact s /\ b SUBSET s /\ ~(s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `compact(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `&(CARD(c:real^N->bool)):int = &n + &1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN INT_ARITH_TAC]);;

(* Vertex balls are compact subsets of |tt|; Bd N meets them in closed sets. *)

let MOI_S4G_VB_CLOSED = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> compact (moi_s34_vb tt kk v) /\
         moi_s34_vb tt kk v SUBSET UNIONS tt /\
         closed (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN skeleton 1 kk` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (moi_s34_vb tt kk (v:real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_vb tt kk v SUBSET UNIONS {s | s IN tt /\ (v:real^N) IN s}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS tt:real^N->bool)`;
                 `moi_s34_nb tt (kk:(real^N->bool)->bool)`] CLOSED_IN_FRONTIER_OF) THEN
  REWRITE_TAC[moi_s34_nb; GSYM derived_frontier] THEN
  REWRITE_TAC[GSYM moi_s34_bd] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s34_vb tt kk v INTER moi_s34_bd tt kk =
                moi_s34_vb tt kk (v:real^N) INTER c` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* The outer cells lie on Bd N (closures of subsets of closed sets). *)

let MOI_S4G_OUT_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> (!v. {v} IN kk
              ==> closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)
                  SUBSET moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
         (!g. g IN moi_s34_simp kk (&1)
              ==> closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk)
                  SUBSET moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^N`; X_GEN_TAC `y:real^N->bool`] THEN
  DISCH_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`] MOI_S4G_VB_CLOSED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `y:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `segment[a:real^N,b] IN kk` THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MOI_S4A_SD_EDGE] THEN
    SUBGOAL_THEN `(moi_s34_vb tt kk a INTER moi_s34_vb tt kk b) INTER moi_s34_bd tt kk =
                  (moi_s34_vb tt kk a INTER moi_s34_bd tt kk) INTER
                  moi_s34_vb tt kk (b:real^N)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `a:real^N`] MOI_S4G_VB_CLOSED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `b:real^N`] MOI_S4G_VB_CLOSED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[COMPACT_IMP_CLOSED]]]]);;

(* The outer cells meet |kk| only in its boundary (MOI_S4O_FR). *)

let MOI_S4G_OUT_IN_B = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> (!v y. {v} IN kk /\ v IN complex_boundary kk /\
                y IN closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                              UNIONS kk) /\
                y IN UNIONS kk
                ==> y IN complex_boundary kk) /\
         (!g y. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk /\
                y IN closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                              UNIONS kk) /\
                y IN UNIONS kk
                ==> y IN complex_boundary kk)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4O_FR THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^N. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                         UNIONS kk):real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    REWRITE_TAC[moi_s34_vb; derived_dual_cell] THEN
    MATCH_ACCEPT_TAC(SET_RULE `!(A:real^N->bool) S B K.
      ((A INTER S) INTER B) DIFF K SUBSET S DIFF K`);
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `g = segment[a:real^N,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC MOI_S4O_FR THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `a:real^N`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `segment[a:real^N,b] SUBSET complex_boundary kk` THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t x:real^N. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `closure ((moi_s34_sd tt kk (segment[a,b]) INTER moi_s34_bd tt kk) DIFF
                           UNIONS kk):real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      SUBGOAL_THEN `moi_s34_sd tt kk (segment[a,b]) SUBSET moi_s34_vb tt kk (a:real^N)`
      MP_TAC THENL
       [REWRITE_TAC[moi_s34_sd] THEN
        MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        UNDISCH_TAC `{a:real^N} IN kk` THEN
        MATCH_ACCEPT_TAC(SET_RULE `!(kk:(real^N->bool)->bool) (f:real^N->real^N->bool) g a.
          {a} IN kk ==> a IN g ==> INTERS {f v | v | v IN g /\ {v} IN kk} SUBSET f a`);
        REWRITE_TAC[moi_s34_vb; derived_dual_cell] THEN
        MATCH_ACCEPT_TAC(SET_RULE `!(A:real^N->bool) N S B K.
          A SUBSET N INTER S ==> (A INTER B) DIFF K SUBSET S DIFF K`)]]]);;

(* The membership profile: a relative interior point w of a simplex         *)
(* convex hull V of kk lying exactly in the vertex balls of the vertices of  *)
(* U0 among V, and lying in a source cell l with label (k,q,x).              *)

let MOI_S4G_PROFILE = prove
 (`!(tt:(real^N->bool)->bool) kk V U0 w l k q x.
     moi_s34_tube tt kk /\ convex hull V IN kk /\ ~affine_dependent V /\
     w IN convex hull V /\ (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
     (!u. u IN V ==> (w IN moi_s34_vb tt kk u <=> u IN U0)) /\
     moi_s4g_lab tt kk l k q x /\ w IN l
     ==> (k = 1 ==> ?u. q = {u} /\ u IN U0) /\
         (k = 2 ==> ?a b. q = convex hull {a,b} /\ ~(a = b) /\ a IN U0 /\ b IN U0) /\
         ((k = 3 \/ k = 4)
          ==> convex hull V SUBSET q /\ w IN closure (q DIFF moi_s34_nb tt kk)) /\
         ((k = 5 \/ k = 6)
          ==> convex hull V SUBSET q /\ w IN moi_s34_bd tt kk /\
              ?u. x = {u} /\ u IN U0) /\
         ((k = 7 \/ k = 8)
          ==> convex hull V SUBSET q /\ w IN moi_s34_bd tt kk /\
              ?a b. x = convex hull {a,b} /\ ~(a = b) /\ a IN U0 /\ b IN U0) /\
         (k = 9
          ==> w IN moi_s34_bd tt kk /\ (?u. q = {u} /\ u IN U0) /\
              ?s. s IN moi_s34_simp kk (&2) /\ s SUBSET complex_boundary kk /\
                  convex hull V SUBSET s) /\
         (k = 10
          ==> w IN moi_s34_bd tt kk /\
              (?a b. q = convex hull {a,b} /\ ~(a = b) /\ a IN U0 /\ b IN U0) /\
              ?s. s IN moi_s34_simp kk (&2) /\ s SUBSET complex_boundary kk /\
                  convex hull V SUBSET s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN
  SUBGOAL_THEN `!u:real^N. {u} IN kk /\ w IN moi_s34_vb tt kk u ==> u IN U0`
  (LABEL_TAC "h1") THENL
   [X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(u:real^N) IN convex hull V` THENL
     [SUBGOAL_THEN `(u:real^N) IN V` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC MOI_S4G_VTX_C THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N`;
                     `convex hull V:real^N->bool`] MOI_S4G_VB_OUT) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q':real^N->bool. q' IN kk /\ w IN q' ==> convex hull V SUBSET q'`
  (LABEL_TAC "h2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4G_RELINT_SUB THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `w:real^N`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) IN complex_boundary kk
    ==> ?s. s IN moi_s34_simp kk (&2) /\ s SUBSET complex_boundary kk /\
            convex hull V SUBSET s`
  (LABEL_TAC "h3") THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_boundary] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
      REWRITE_TAC[complex_boundary] THEN MATCH_MP_TAC(SET_RULE
       `!(s:real^N->bool) c. s IN c ==> s SUBSET UNIONS c`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      USE_THEN "h2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:real^N->bool. g IN moi_s34_simp kk (&1) /\ w IN moi_s34_sd tt kk g
                     ==> ?a b. g = convex hull {a,b} /\ ~(a = b) /\ a IN U0 /\ b IN U0`
  (LABEL_TAC "h4") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    UNDISCH_TAC `segment[a:real^N,b] IN kk` THEN
    UNDISCH_TAC `(w:real^N) IN moi_s34_sd tt kk g` THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(w:real^N) IN moi_s34_sd tt kk (convex hull {a,b})` THEN
    ASM_SIMP_TAC[MOI_S4A_SD_EDGE; IN_INTER] THEN STRIP_TAC THEN
    CONJ_TAC THEN USE_THEN "h1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
                MOI_S4G_OUT_IN_B) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ob1") (LABEL_TAC "ob2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "os1") (LABEL_TAC "os2")) THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `convex hull V:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q':real^N->bool. q' IN kk ==> closure (q' DIFF moi_s34_nb tt kk) SUBSET q'`
  (LABEL_TAC "h5") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    SUBGOAL_THEN `(q':real^N->bool) IN tt` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^N) IN l` THEN ASM_REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THENL
   [(* k = 1 *)
    EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN USE_THEN "h1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    (* k = 2 *)
    USE_THEN "h4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* k = 3 *)
    ASM_REWRITE_TAC[] THEN USE_THEN "h2" MATCH_MP_TAC THEN
    CONJ_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "h5" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    (* k = 4 *)
    ASM_REWRITE_TAC[] THEN USE_THEN "h2" MATCH_MP_TAC THEN
    CONJ_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "h5" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    (* k = 5 *)
    UNDISCH_TAC `(w:real^N) IN q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN USE_THEN "h1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    (* k = 6 *)
    UNDISCH_TAC `(w:real^N) IN q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN USE_THEN "h1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    (* k = 7 *)
    UNDISCH_TAC `(w:real^N) IN q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      USE_THEN "h4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* k = 8 *)
    UNDISCH_TAC `(w:real^N) IN q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      USE_THEN "h4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* k = 9 *)
    SUBGOAL_THEN `(w:real^N) IN moi_s34_vb tt kk v INTER moi_s34_bd tt kk` MP_TAC THENL
     [USE_THEN "os1" (MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN USE_THEN "h1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "h3" MATCH_MP_TAC THEN USE_THEN "ob1" MATCH_MP_TAC THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
    (* k = 10 *)
    SUBGOAL_THEN `(w:real^N) IN moi_s34_sd tt kk q INTER moi_s34_bd tt kk` MP_TAC THENL
     [USE_THEN "os2" (MP_TAC o SPEC `q:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "h4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "h3" MATCH_MP_TAC THEN USE_THEN "ob2" MATCH_MP_TAC THEN
      EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Dimension bookkeeping for simplices of kk and the witness points          *)
(* of the face disks, tetra balls, patches, face arcs, edge arcs and marked   *)
(* points, in the form used by MOI_S4G_PROFILE.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_SIMP_VERTS = prove
 (`!(tt:(real^N->bool)->bool) kk q n.
     moi_s34_tube tt kk /\ q IN moi_s34_simp kk (&n)
     ==> ?V. ~affine_dependent V /\ q = convex hull V /\ CARD V = n + 1 /\ FINITE V`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `V:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(q:real^N->bool) = &(CARD(V:real^N->bool)) - &1` THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* Nested simplices of kk: equal dimension forces equality; inclusion        *)
(* bounds the dimension.                                                      *)

let MOI_S4G_NEST = prove
 (`!(tt:(real^N->bool)->bool) kk q1 q2 m n.
     moi_s34_tube tt kk /\ q1 IN moi_s34_simp kk (&m) /\ q2 IN moi_s34_simp kk (&n) /\
     q1 SUBSET q2
     ==> m <= n /\ (m = n ==> q1 = q2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `aff_dim(q1:real^N->bool) = &m` THEN
    UNDISCH_TAC `aff_dim(q2:real^N->bool) = &n` THEN
    MP_TAC(ISPECL [`q1:real^N->bool`; `q2:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISCH_TAC THEN ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `q1:real^N->bool`; `q2:real^N->bool`]
                  MOI_S4O_NEST_DIM) THEN
    ASM_SIMP_TAC[] THEN INT_ARITH_TAC]);;

let MOI_S4G_EDGE_EQ = prove
 (`!a b u1 u2:real^N.
     ~(a = b) /\ ~(u1 = u2) /\ a IN {u1,u2} /\ b IN {u1,u2}
     ==> convex hull {a,b} = convex hull {u1,u2}`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* Bd N lies in N. *)

let MOI_S4G_BD_NB = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ q IN kk ==> moi_s34_bd tt kk SUBSET moi_s34_nb tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4A_FLAT_KK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

(* Witnesses of the cells inside a triangle or tetrahedron q of kk. *)

let MOI_S4G_WIT_CQ = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ (q IN moi_s34_simp kk (&2) \/ q IN moi_s34_simp kk (&3))
     ==> ?V w. ~affine_dependent V /\ q = convex hull V /\ w IN q /\
               (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
               (!u. u IN V ==> (w IN moi_s34_vb tt kk u <=> u IN {})) /\
               ~(w IN moi_s34_nb tt kk) /\
               w IN closure (q DIFF moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`; `2`] MOI_S4G_SIMP_VERTS);
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`; `3`] MOI_S4G_SIMP_VERTS)] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_WITNESS_BARY) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `w:real^N`] THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `~((w:real^N) IN moi_s34_nb tt kk)` THEN
  REWRITE_TAC[moi_s34_vb; moi_s34_nb; derived_dual_cell; IN_INTER] THEN MESON_TAC[]);;

let MOI_S4G_WIT_QV = prove
 (`!(tt:(real^N->bool)->bool) kk q v.
     moi_s34_tube tt kk /\ (q IN moi_s34_simp kk (&2) \/ q IN moi_s34_simp kk (&3)) /\
     v IN q /\ {v} IN kk
     ==> ?V w. ~affine_dependent V /\ q = convex hull V /\ w IN q /\
               (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
               (!u. u IN V ==> (w IN moi_s34_vb tt kk u <=> u IN {v})) /\
               w IN q INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`; `2`] MOI_S4G_SIMP_VERTS);
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`; `3`] MOI_S4G_SIMP_VERTS)] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  (SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
    [MATCH_MP_TAC MOI_S4A_VTX THEN
     MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
     REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `{v:real^N}`] MOI_S4G_WITNESS) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[SING_SUBSET; NOT_INSERT_EMPTY; CARD_SING] THEN
     CONV_TAC NUM_REDUCE_CONV THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
     REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `w:real^N`] THEN ASM_REWRITE_TAC[IN_INTER] THEN
  ASM_SIMP_TAC[IN_SING]);;

let MOI_S4G_WIT_QG = prove
 (`!(tt:(real^N->bool)->bool) kk q g.
     moi_s34_tube tt kk /\ (q IN moi_s34_simp kk (&2) \/ q IN moi_s34_simp kk (&3)) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET q
     ==> ?V w u1 u2. ~affine_dependent V /\ q = convex hull V /\ w IN q /\
                     ~(u1 = u2) /\ g = convex hull {u1,u2} /\
                     (!E. E SUBSET V /\ w IN convex hull E ==> E = V) /\
                     (!u. u IN V ==> (w IN moi_s34_vb tt kk u <=> u IN {u1,u2})) /\
                     w IN q INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. (n = 2 \/ n = 3) /\ (q:real^N->bool) IN moi_s34_simp kk (&n)`
  (X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`; `n:num`] MOI_S4G_SIMP_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 3 \/ CARD V = 4` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `g = segment[u1:real^N,u2]` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  (SUBGOAL_THEN `(u1:real^N) IN V /\ u2 IN V` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC MOI_S4A_VTX THEN
     MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{u1:real^N,u2}`] HULL_SUBSET) THEN
     UNDISCH_TAC `convex hull {u1:real^N,u2} SUBSET q` THEN ASM SET_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`; `{u1:real^N,u2}`] MOI_S4G_WITNESS) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
     ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM SET_TAC[];
     ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `w:real^N`; `u1:real^N`; `u2:real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (convex hull {u1,u2}) =
                moi_s34_vb tt kk u1 INTER moi_s34_vb tt kk (u2:real^N)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_SD_EDGE THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ASM_SIMP_TAC[IN_INTER; IN_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* The source face relation, inclusion direction.  If m SUBSET l             *)
(* for labelled source cells, then the label of m is a face of the label of  *)
(* l (moi_s4g_face), by the witness of m and MOI_S4G_PROFILE.                 *)
(* ------------------------------------------------------------------------- *)

(* Dimension facts in a MESON-friendly form. *)

let MOI_S4G_SUB_EQ = prove
 (`!(tt:(real^N->bool)->bool) kk q1 q2 n.
     moi_s34_tube tt kk /\ q1 IN moi_s34_simp kk (&n) /\ q2 IN moi_s34_simp kk (&n) /\
     q1 SUBSET q2
     ==> q1 = q2`,
  MESON_TAC[MOI_S4G_NEST]);;

let MOI_S4G_SUB_32 = prove
 (`!(tt:(real^N->bool)->bool) kk q1 q2.
     moi_s34_tube tt kk /\ q1 IN moi_s34_simp kk (&3) /\ q2 IN moi_s34_simp kk (&2)
     ==> ~(q1 SUBSET q2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q1:real^N->bool`; `q2:real^N->bool`; `3`; `2`] MOI_S4G_NEST) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MOI_S4G_SING_EQ = prove
 (`!a b:real^N. {a} = {b} <=> a = b`,
  SET_TAC[]);;

(* Patches and face arcs (kinds 5, 6). *)

let MOI_S4G_FACE_IMP_QV = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ (k' = 5 \/ k' = 6) /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?v. (k' = 5 /\ q' IN moi_s34_simp kk (&3) \/ k' = 6 /\ q' IN moi_s34_simp kk (&2)) /\
        v IN q' /\ {v} IN kk /\ x' = {v:real^N} /\
        m = q' INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk`
  (X_CHOOSE_THEN `v:real^N` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    REWRITE_TAC[moi_s4g_lab] THEN
    UNDISCH_TAC `k' = 5 \/ k' = 6` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q' IN moi_s34_simp kk (&2) \/ q' IN moi_s34_simp (kk:(real^N->bool)->bool) (&3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q':real^N->bool`; `v:real^N`] MOI_S4G_WIT_QV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN l` ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^N->bool) SUBSET l` THEN
    UNDISCH_TAC `m = q' INTER moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(w:real^N) IN q' INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `q' IN moi_s34_simp kk (&2) \/ q' IN moi_s34_simp (kk:(real^N->bool)->bool) (&3)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `{v:real^N}`; `w:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN q'` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> concl th = `k' = 5 \/ k' = 6`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S4G_SING_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l,r = dest_eq(concl th) in is_var l && not(free_in l r)))) THEN
  ASM_MESON_TAC[MOI_S4G_SUB_EQ; MOI_S4G_SUB_32; MOI_S4G_SING_EQ]);;

(* Edge arcs and marked points (kinds 7, 8). *)

let MOI_S4G_FACE_IMP_QG = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ (k' = 7 \/ k' = 8) /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(k' = 7 /\ q' IN moi_s34_simp kk (&3) \/ k' = 8 /\ q' IN moi_s34_simp kk (&2)) /\
    x' IN moi_s34_simp kk (&1) /\ x' SUBSET q' /\
    m = q' INTER moi_s34_sd tt kk x' INTER moi_s34_bd tt (kk:(real^N->bool)->bool)`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    REWRITE_TAC[moi_s4g_lab] THEN
    UNDISCH_TAC `k' = 7 \/ k' = 8` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q' IN moi_s34_simp kk (&2) \/ q' IN moi_s34_simp (kk:(real^N->bool)->bool) (&3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_WIT_QG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `w:real^N`
    (X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(w:real^N) IN l` ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^N->bool) SUBSET l` THEN
    UNDISCH_TAC `m = q' INTER moi_s34_sd tt kk x' INTER moi_s34_bd tt (kk:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(w:real^N) IN q' INTER moi_s34_sd tt kk x' INTER moi_s34_bd tt kk` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `q' IN moi_s34_simp kk (&2) \/ q' IN moi_s34_simp (kk:(real^N->bool)->bool) (&3)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `{u1:real^N,u2}`; `w:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN q'` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `x' = convex hull {u1:real^N,u2}` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> concl th = `k' = 7 \/ k' = 8`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S4G_SING_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l,r = dest_eq(concl th) in is_var l && not(free_in l r)))) THEN
  ASM_MESON_TAC[MOI_S4G_SUB_EQ; MOI_S4G_SUB_32; MOI_S4G_SING_EQ; MOI_S4G_EDGE_EQ;
                SING_SUBSET; HULL_INC; IN_INSERT]);;

(* Face disks and tetra balls (kinds 3, 4). *)

let MOI_S4G_FACE_IMP_CQ = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ (k' = 3 \/ k' = 4) /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(k' = 4 /\ q' IN moi_s34_simp kk (&3) \/ k' = 3 /\ q' IN moi_s34_simp kk (&2)) /\
    (x':real^N->bool) = {} /\ m = closure (q' DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    REWRITE_TAC[moi_s4g_lab] THEN
    UNDISCH_TAC `k' = 3 \/ k' = 4` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q' IN moi_s34_simp kk (&2) \/ q' IN moi_s34_simp (kk:(real^N->bool)->bool) (&3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q':real^N->bool`] MOI_S4G_WIT_CQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN l` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `{}:real^N->bool`; `w:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN q'` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `q' = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> concl th = `k' = 3 \/ k' = 4`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  ASM_MESON_TAC[MOI_S4G_SUB_EQ; MOI_S4G_SUB_32]);;

(* Vertex balls (kind 1). *)

let MOI_S4G_FACE_IMP_VB = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ k' = 1 /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?v. {v} IN kk /\ q' = {v:real^N} /\ (x':real^N->bool) = {} /\ m = moi_s34_vb tt kk v`
  (X_CHOOSE_THEN `v:real^N` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    ASM_REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
                MOI_S4G_VERTEX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN l` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `{v:real^N}`;
                 `{v:real^N}`; `v:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_SING; AFFINE_INDEPENDENT_1; IN_SING] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
      ASM_CASES_TAC `E:real^N->bool = {}` THENL
       [UNDISCH_TAC `(v:real^N) IN convex hull E` THEN
        ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
        ASM SET_TAC[]];
      X_GEN_TAC `u:real^N` THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_S4G_SING_EQ]);;

(* Splitting disks (kind 2). *)

let MOI_S4G_FACE_IMP_SD = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ k' = 2 /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `q' IN moi_s34_simp kk (&1) /\ (x':real^N->bool) = {} /\
    m = moi_s34_sd tt (kk:(real^N->bool)->bool) q'`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    ASM_REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q':real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `q' = segment[u1:real^N,u2]` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `convex hull {u1:real^N,u2} IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `u1:real^N`; `u2:real^N`] MOI_S4G_MIDPOINT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `midpoint(u1:real^N,u2) IN l` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `{u1:real^N,u2}`;
                 `{u1:real^N,u2}`; `midpoint(u1:real^N,u2)`; `l:real^N->bool`; `k:num`;
                 `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN X_GEN_TAC `u:real^N` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S4G_SING_EQ; moi_s34_simp; IN_ELIM_THM]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let l,r = dest_eq(concl th) in is_var l && not(free_in l r)))) THEN
  ASM_MESON_TAC[MOI_S4G_EDGE_EQ; SING_SUBSET; HULL_INC; IN_INSERT]);;

(* The outer cells from SCELL_A: nonempty, with the face arcs, outer arcs   *)
(* and marked points of the boundary inside them.                            *)

let MOI_S4G_OUTER_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> (!v. {v} IN kk /\ v IN complex_boundary kk
              ==> ~(closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                             UNIONS kk) = {}) /\
                  (!s. s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk
                       ==> s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk SUBSET
                           closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk)) /\
                  (!g. g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk
                       ==> closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk) SUBSET
                           closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk))) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
              ==> ~(closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                             UNIONS kk) = {}) /\
                  (!s. s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                       s SUBSET complex_boundary kk
                       ==> s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk SUBSET
                           closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                    UNIONS kk)))`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP SCELL_A (ASSUME `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  REWRITE_TAC[moi_s34_scell_facts] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "c7" (el 6 cs) THEN LABEL_TAC "c8" (el 7 cs)) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    USE_THEN "c7" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC;
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "SUBSET" (concl th) &&
      is_binary "UNION" (lhand(concl th)))) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let c = concl th in is_binary "IN" c || is_binary "SUBSET" c))) THEN
    SET_TAC[];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "c8" (MP_TAC o SPEC `g:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "SUBSET" (concl th) &&
      is_comb(lhand(concl th)) && is_const(rator(lhand(concl th))) &&
      fst(dest_const(rator(lhand(concl th)))) = "UNIONS")) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let c = concl th in is_binary "IN" c || is_binary "SUBSET" c))) THEN
    SET_TAC[]]);;

(* Cells of kinds 3-8 lie in their simplex, hence in |kk|. *)

let MOI_S4G_KK_CLOSED = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ q IN kk
     ==> compact q /\ closure (q DIFF moi_s34_nb tt kk) SUBSET q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(q:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN ASM_SIMP_TAC[FINITE_IMP_COMPACT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[]);;

let MOI_S4G_LAB_IN_KK = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\ 3 <= k /\ k <= 8
     ==> l SUBSET q /\ q IN kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  TRY(UNDISCH_TAC `3 <= k` THEN UNDISCH_TAC `k <= 8` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
  (SUBGOAL_THEN `(q:real^N->bool) IN kk` ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
     REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4G_KK_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Outer patches (kind 9). *)

let MOI_S4G_FACE_IMP_OP = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ k' = 9 /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?v. {v} IN kk /\ v IN complex_boundary kk /\ q' = {v:real^N} /\
        (x':real^N->bool) = {} /\
        m = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)`
  (X_CHOOSE_THEN `v:real^N` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    ASM_REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
                MOI_S4G_OUTER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:real^N. y0 IN l /\ ~(y0 IN UNIONS kk)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                    UNIONS (kk:(real^N->bool)->bool) = {})` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(closure ((moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk) DIFF
                              UNIONS kk) = {})` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y0:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET l` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                  UNIONS (kk:(real^N->bool)->bool)` CLOSURE_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(3 <= k /\ k <= 8)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_LAB_IN_KK) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y0:real^N) IN UNIONS kk)` THEN UNDISCH_TAC `(y0:real^N) IN l` THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET complex_boundary kk`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) IN complex_boundary kk` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_boundary] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
    REWRITE_TAC[complex_boundary] THEN MATCH_MP_TAC(SET_RULE
     `!(s:real^N->bool) c. s IN c ==> s SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`; `v:real^N`] MOI_S4G_WIT_QV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `w:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN l` ASSUME_TAC THENL
   [UNDISCH_TAC `(m:real^N->bool) SUBSET l` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_vb"))
          (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
          (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `s = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `{v:real^N}`; `w:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(3 <= k /\ k <= 8)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th)))) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[MOI_S4G_SING_EQ]);;

(* Outer arcs (kind 10). *)

let MOI_S4G_FACE_IMP_OA = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\ k' = 10 /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `q' IN moi_s34_simp kk (&1) /\ q' SUBSET complex_boundary kk /\
    (x':real^N->bool) = {} /\
    m = closure ((moi_s34_sd tt kk q' INTER moi_s34_bd tt kk) DIFF
                 UNIONS (kk:(real^N->bool)->bool))`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    ASM_REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
                MOI_S4G_OUTER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q':real^N->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:real^N. y0 IN l /\ ~(y0 IN UNIONS kk)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((moi_s34_sd tt kk q' INTER moi_s34_bd tt kk) DIFF
                    UNIONS (kk:(real^N->bool)->bool) = {})` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(closure ((moi_s34_sd tt kk (q':real^N->bool) INTER
                               moi_s34_bd tt kk) DIFF UNIONS kk) = {})` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y0:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(m:real^N->bool) SUBSET l` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(moi_s34_sd tt kk q' INTER moi_s34_bd tt kk) DIFF
                  UNIONS (kk:(real^N->bool)->bool)` CLOSURE_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(3 <= k /\ k <= 8)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_LAB_IN_KK) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y0:real^N) IN UNIONS kk)` THEN UNDISCH_TAC `(y0:real^N) IN l` THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN moi_s34_simp kk (&2) /\ (q':real^N->bool) SUBSET s /\
        s SUBSET complex_boundary kk`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `q':real^N->bool`] MOI_S4O_IN_BOUNDARY) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `moi_s34_tube (tt:(real^N->bool)->bool) kk` THEN
        SIMP_TAC[moi_s34_tube; combinatorial_manifold_with_boundary];
        ALL_TAC] THEN
      UNDISCH_TAC `(q':real^N->bool) IN moi_s34_simp kk (&1)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN MESON_TAC[MOI_S4O_DIM_NONEMPTY];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
    REWRITE_TAC[complex_boundary] THEN MATCH_MP_TAC(SET_RULE
     `!(s:real^N->bool) c. s IN c ==> s SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`; `q':real^N->bool`] MOI_S4G_WIT_QG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `w:real^N`
    (X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(w:real^N) IN l` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!w:real^N A C l. w IN A /\ A SUBSET C /\ C SUBSET l ==> w IN l`) THEN
    EXISTS_TAC `s INTER moi_s34_sd tt kk q' INTER moi_s34_bd tt (kk:(real^N->bool)->bool)` THEN
    EXISTS_TAC `m:real^N->bool` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd"))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull V IN (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `s = convex hull (V:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `V:real^N->bool`;
                 `{u1:real^N,u2}`; `w:real^N`; `l:real^N->bool`; `k:num`; `q:real^N->bool`;
                 `x:real^N->bool`] MOI_S4G_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^N) IN s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `q' = convex hull {u1:real^N,u2}` THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(3 <= k /\ k <= 8)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th)))) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN REWRITE_TAC[moi_s4g_lab] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ; moi_s4g_face; IN_SING; IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[MOI_S4G_EDGE_EQ; SING_SUBSET; HULL_INC; IN_INSERT]);;

(* ------------------------------------------------------------------------- *)
(* The cell of a label, uniqueness of labels, and the source face            *)
(* relation by kinds in both directions:                                      *)
(*   MOI_S4G_LAB_UNIQUE  a source cell determines its kind and index;         *)
(*   MOI_S4G_FACE        m SUBSET l <=> moi_s4g_face (label m) (label l).      *)
(* ------------------------------------------------------------------------- *)

let moi_s4g_cell = new_definition
 `moi_s4g_cell (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (k:num) (q:real^N->bool) (x:real^N->bool) =
   if k = 1 then moi_s34_vb tt kk (CHOICE q) else
   if k = 2 then moi_s34_sd tt kk q else
   if k = 3 \/ k = 4 then closure (q DIFF moi_s34_nb tt kk) else
   if k = 5 \/ k = 6 then q INTER moi_s34_vb tt kk (CHOICE x) INTER moi_s34_bd tt kk else
   if k = 7 \/ k = 8 then q INTER moi_s34_sd tt kk x INTER moi_s34_bd tt kk else
   if k = 9 then closure ((moi_s34_vb tt kk (CHOICE q) INTER moi_s34_bd tt kk) DIFF
                          UNIONS kk) else
   closure ((moi_s34_sd tt kk q INTER moi_s34_bd tt kk) DIFF UNIONS kk)`;;

let MOI_S4G_CHOICE_SING = prove
 (`!a:A. CHOICE {a} = a`,
  GEN_TAC THEN MP_TAC(ISPEC `{a:A}` CHOICE_DEF) THEN SET_TAC[]);;

let MOI_S4G_LAB_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s4g_lab tt kk l k q x ==> l = moi_s4g_cell tt kk k q x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_cell; MOI_S4G_CHOICE_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let MOI_S4G_LAB_FUN = prove
 (`!(tt:(real^N->bool)->bool) kk l m k q x.
     moi_s4g_lab tt kk l k q x /\ moi_s4g_lab tt kk m k q x ==> l = m`,
  MESON_TAC[MOI_S4G_LAB_CELL]);;

(* Proper faces have smaller kind dimension, so the face relation is        *)
(* antisymmetric.                                                             *)

let moi_s4g_kd = new_definition
 `moi_s4g_kd (k:num) =
   if k = 1 \/ k = 4 then 3 else
   if k = 2 \/ k = 3 \/ k = 5 \/ k = 9 then 2 else
   if k = 8 then 0 else 1`;;

let MOI_S4G_FACE_KD = prove
 (`!(kk:(real^N->bool)->bool) k' q' x' k q x.
     moi_s4g_face kk k' q' x' k q x
     ==> (k' = k /\ q' = q /\ x' = x) \/ moi_s4g_kd k' < moi_s4g_kd k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_face] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_kd] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_S4G_FACE_ANTISYM = prove
 (`!(kk:(real^N->bool)->bool) k' q' x' k q x.
     moi_s4g_face kk k' q' x' k q x /\ moi_s4g_face kk k q x k' q' x'
     ==> k' = k /\ q' = q /\ x' = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_FACE_KD) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_FACE_KD) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[LT_ANTISYM]);;

(* The inclusion direction for any pair of labels. *)

let MOI_S4G_FACE_IMP = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\
     moi_s4g_lab tt kk l k q x /\ m SUBSET l
     ==> moi_s4g_face kk k' q' x' k q x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k' = 1 \/ k' = 2 \/ (k' = 3 \/ k' = 4) \/ (k' = 5 \/ k' = 6) \/
                (k' = 7 \/ k' = 8) \/ k' = 9 \/ k' = 10`
  MP_TAC THENL
   [UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
    REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN
                        MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `m:real^N->bool`;
                                              `l:real^N->bool`] THEN
                        ASM_REWRITE_TAC[] THEN NO_TAC)
             [MOI_S4G_FACE_IMP_VB; MOI_S4G_FACE_IMP_SD; MOI_S4G_FACE_IMP_CQ;
              MOI_S4G_FACE_IMP_QV; MOI_S4G_FACE_IMP_QG; MOI_S4G_FACE_IMP_OP;
              MOI_S4G_FACE_IMP_OA]));;

(* (i): a source cell determines its kind and index. *)

let MOI_S4G_LAB_UNIQUE = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x k' q' x'.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\ moi_s4g_lab tt kk l k' q' x'
     ==> k = k' /\ q = q' /\ x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_FACE_ANTISYM) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4G_FACE_IMP THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `l:real^N->bool`; `l:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The converse direction (faces are subsets) and the face relation          *)
(* MOI_S4G_FACE.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_SD_SUB_VB = prove
 (`!(tt:(real^N->bool)->bool) kk g v.
     {v} IN kk /\ v IN g ==> moi_s34_sd tt kk g SUBSET moi_s34_vb tt kk v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_sd] THEN
  UNDISCH_TAC `(v:real^N) IN g` THEN UNDISCH_TAC `{v:real^N} IN kk` THEN
  MATCH_ACCEPT_TAC(SET_RULE `!(kk:(real^N->bool)->bool) (f:real^N->real^N->bool) g a.
    {a} IN kk ==> a IN g ==> INTERS {f v | v | v IN g /\ {v} IN kk} SUBSET f a`));;

let MOI_S4G_BD_CL = prove
 (`!(tt:(real^N->bool)->bool) kk q.
     moi_s34_tube tt kk /\ q IN kk
     ==> q INTER moi_s34_bd tt kk SUBSET closure (q DIFF moi_s34_nb tt kk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `q:real^N->bool`] MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `q = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `V:real^N->bool`] MOI_S4G_FLAT_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MOI_S4G_FLAT_THEN "h"] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_s34_bd tt kk` THEN
  MOI_S4G_USE_IFF "fbd" [`y:real^N`] THEN STRIP_TAC THEN
  MOI_S4G_USE_IFF "fcl" [`y:real^N`] THEN ASM_REWRITE_TAC[]);;

(* Tactic: move the quantifier-free assumptions into the goal and finish  *)
(* with SET_TAC.                                                              *)

let MOI_S4G_SSET_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c = concl th in
    not(is_forall c) && not(is_exists c)))) THEN SET_TAC[];;

let MOI_S4G_FACE_REV = prove
 (`!(tt:(real^N->bool)->bool) kk m l k' q' x' k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk m k' q' x' /\
     moi_s4g_lab tt kk l k q x /\ moi_s4g_face kk k' q' x' k q x
     ==> m SUBSET l`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `(k':num) = k /\ (q':real^N->bool) = q /\ (x':real^N->bool) = x` THENL
   [SUBGOAL_THEN `(m:real^N->bool) = l` (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    MATCH_MP_TAC MOI_S4G_LAB_FUN THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_OUT_SUB) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
                MOI_S4G_OUTER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "of1") (LABEL_TAC "of2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "os1") (LABEL_TAC "os2")) THEN
  UNDISCH_TAC `moi_s4g_face kk k' q' x' k q (x:real^N->bool)` THEN
  REWRITE_TAC[moi_s4g_face] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk m k' q' (x':real^N->bool)` THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  ASM_REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    USE_THEN "os1" (MP_TAC o SPEC `v':real^N`) THEN MOI_S4G_SSET_TAC;
    USE_THEN "os2" (MP_TAC o SPEC `q':real^N->bool`) THEN MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    USE_THEN "os2" (MP_TAC o SPEC `q:real^N->bool`) THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    MATCH_MP_TAC SUBSET_CLOSURE THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    (MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `q:real^N->bool`] MOI_S4G_BD_CL) THEN ANTS_TAC THENL [RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    MOI_S4G_SSET_TAC;
    USE_THEN "of1" (MP_TAC o SPEC `v:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool` o CONJUNCT1 o CONJUNCT2)] THEN MOI_S4G_SSET_TAC;
    USE_THEN "of1" (MP_TAC o SPEC `v:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool` o CONJUNCT1 o CONJUNCT2)] THEN MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`; `v:real^N`] MOI_S4G_SD_SUB_VB) THEN MOI_S4G_SSET_TAC;
    USE_THEN "of1" (MP_TAC o SPEC `v:real^N`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool` o CONJUNCT2 o CONJUNCT2)] THEN MOI_S4G_SSET_TAC;
    USE_THEN "of2" (MP_TAC o SPEC `q:real^N->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `q':real^N->bool` o CONJUNCT2)] THEN MOI_S4G_SSET_TAC]);;

(* (ii): the source face relation by kinds. *)

let MOI_S4G_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x m k' q' x'.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\ moi_s4g_lab tt kk m k' q' x'
     ==> (m SUBSET l <=> moi_s4g_face kk k' q' x' k q x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_S4G_FACE_IMP THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `m:real^N->bool`; `l:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC MOI_S4G_FACE_REV THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `k':num`; `q':real^N->bool`; `x':real^N->bool`;
                          `k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4G_PROPER_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x m k' q' x'.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\ moi_s4g_lab tt kk m k' q' x'
     ==> (m SUBSET l /\ ~(m = l) <=>
          moi_s4g_face kk k' q' x' k q x /\ ~(k' = k /\ q' = q /\ x' = x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                 `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(TAUT `(c <=> d) ==> (a /\ ~c <=> a /\ ~d)`) THEN EQ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC MOI_S4G_LAB_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `l:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC MOI_S4G_LAB_FUN THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Dimensions of source cells by labels, and the evaluation of               *)
(* moi_s34_tgt by labels.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_POINT_CELL = prove
 (`!p:real^N. pl_cell_with_boundary 0 {p} {}`,
  GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`{p:real^N}`; `\x:real^N. x`; `\x:real^N. x`] THEN
  REWRITE_TAC[RELATIVE_FRONTIER_SING; IMAGE_CLAUSES; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_SING] THEN
  REWRITE_TAC[simplex] THEN EXISTS_TAC `{p:real^N}` THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_1; CONVEX_HULL_SING; CARD_SING] THEN INT_ARITH_TAC);;

(* Each source cell is a PL cell of the kind dimension of its label. *)

let MOI_S4G_LAB_CELLB = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x
     ==> ?b. pl_cell_with_boundary (moi_s4g_kd k) l b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCELL_A) THEN REWRITE_TAC[moi_s34_scell_facts] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "c1" (el 0 cs) THEN LABEL_TAC "c2" (el 1 cs) THEN
    LABEL_TAC "c3" (el 2 cs) THEN LABEL_TAC "c4" (el 3 cs) THEN
    LABEL_TAC "c5" (el 4 cs) THEN LABEL_TAC "c6" (el 5 cs) THEN
    LABEL_TAC "c7" (el 6 cs) THEN LABEL_TAC "c8" (el 7 cs)) THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
                GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "gv" (el 1 cs) THEN LABEL_TAC "ge" (el 2 cs)) THEN
  UNDISCH_TAC `moi_s4g_lab tt kk l k q (x:real^N->bool)` THEN
  REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_kd] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [(* 1 *)
    USE_THEN "gv" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
      DISCH_THEN(fun th -> MESON_TAC[last(CONJUNCTS th)])];
    (* 2 *)
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `q:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_s34_sd tt kk q = moi_s34_vb tt kk a INTER moi_s34_vb tt kk (b:real^N)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC MOI_S4A_SD_EDGE THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
      ALL_TAC] THEN
    USE_THEN "ge" (MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL;
                      AFF_DIM_2] THEN
      UNDISCH_TAC `segment[a:real^N,b] IN kk` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SIMP_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN(fun th -> MESON_TAC[CONJUNCT1 th])];
    (* 3 *)
    USE_THEN "c2" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 4 *)
    USE_THEN "c1" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 5 *)
    USE_THEN "c3" (MP_TAC o SPECL [`q:real^N->bool`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 6 *)
    USE_THEN "c4" (MP_TAC o SPECL [`q:real^N->bool`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 7 *)
    USE_THEN "c5" (MP_TAC o SPECL [`q:real^N->bool`; `x:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 8 *)
    USE_THEN "c6" (MP_TAC o SPECL [`q:real^N->bool`; `x:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MOI_S4G_POINT_CELL];
    (* 9 *)
    USE_THEN "c7" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])];
    (* 10 *)
    USE_THEN "c8" (MP_TAC o SPEC `q:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> MESON_TAC[th])]]);;

let MOI_S4G_DIM = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x
     ==> moi_s34_dim l = moi_s4g_kd k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_LAB_CELLB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:real^N->bool`) THEN
  MATCH_MP_TAC MOI_S4D_SAN_DIM_CELL THEN EXISTS_TAC `b:real^N->bool` THEN
  ASM_REWRITE_TAC[moi_s4g_kd] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* The target of a label, and moi_s34_tgt evaluated by labels. *)

let moi_s4g_tgtl = new_definition
 `moi_s4g_tgtl (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (dd:(real^N->bool)->real^3->bool)
               (rr:(real^N->bool)->real^3->bool) (k:num) (q:real^N->bool) (x:real^N->bool) =
   if k = 1 then IMAGE f1 (moi_s34_vb tt kk (CHOICE q)) else
   if k = 2 then IMAGE f1 (moi_s34_sd tt kk q) else
   if k = 3 then dd q else
   if k = 4 then rr q else
   if k = 5 then rr q INTER IMAGE f1 (moi_s34_vb tt kk (CHOICE x)) else
   if k = 6 then dd q INTER IMAGE f1 (moi_s34_vb tt kk (CHOICE x)) else
   if k = 7 then rr q INTER IMAGE f1 (moi_s34_sd tt kk x) else
   if k = 8 then dd q INTER IMAGE f1 (moi_s34_sd tt kk x) else
   if k = 9 then moi_s34_opatch tt kk f1 rr (CHOICE q) else
   moi_s34_oarc tt kk f1 rr q`;;

let MOI_S4G_TGT_REL_LAB = prove
 (`!(tt:(real^N->bool)->bool) kk f1 dd rr l y.
     moi_s34_tgt_rel tt kk f1 dd rr l y <=>
     ?k q x. moi_s4g_lab tt kk l k q x /\ y = moi_s4g_tgtl tt kk f1 dd rr k q x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[moi_s34_tgt_rel] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `{v:real^N}`; `{}:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`2`; `g:real^N->bool`; `{}:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`3`; `s:real^N->bool`; `{}:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`4`; `r:real^N->bool`; `{}:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`5`; `r:real^N->bool`; `{v:real^N}`];
      MAP_EVERY EXISTS_TAC [`6`; `s:real^N->bool`; `{v:real^N}`];
      MAP_EVERY EXISTS_TAC [`7`; `r:real^N->bool`; `g:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`8`; `s:real^N->bool`; `g:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`9`; `{v:real^N}`; `{}:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`10`; `g:real^N->bool`; `{}:real^N->bool`]] THEN
    ASM_REWRITE_TAC[moi_s4g_lab; moi_s4g_tgtl; MOI_S4G_CHOICE_SING] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[moi_s34_tgt_rel; moi_s4g_tgtl; MOI_S4G_CHOICE_SING] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]]);;

let MOI_S4G_TGT_EVAL = prove
 (`!(tt:(real^N->bool)->bool) kk f1 dd rr l k q x.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x
     ==> moi_s34_tgt tt kk f1 dd rr l = moi_s4g_tgtl tt kk f1 dd rr k q x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_tgt; MOI_S4G_TGT_REL_LAB] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:real^3->bool` THEN BETA_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`; `k':num`;
                   `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_LAB_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`k:num`; `q:real^N->bool`; `x:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Facts on the target side (the frame, the face disks and the               *)
(* tetra balls) for the boundaries of the target cells, and the reduction of *)
(* a target boundary to the targets of the proper faces by labels.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_BALL_CELL = prove
 (`!c:real^3->bool. pl_ball 3 c ==> pl_cell_with_boundary 3 c (frontier c)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
  EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]);;

let MOI_S4G_CELL_BD_COMPACT = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary n s b ==> compact b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `compact(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED];
    ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED]]);;

(* N is the union of the vertex balls. *)

let MOI_S4G_NB_UNIONS = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> moi_s34_nb tt kk = UNIONS {moi_s34_vb tt kk v | v | {v} IN kk}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_tube]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP GRAPH_TUBE_DUAL_CELLS) THEN
  REWRITE_TAC[GSYM moi_s34_nb; GSYM moi_s34_vb] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS]);;

let MOI_S4G_VB_NB = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk ==> moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_S4G_NB_UNIONS] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S4G_SD_NB = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> moi_s34_sd tt kk g SUBSET moi_s34_nb tt kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s34_vb tt kk (a:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4G_SD_SUB_VB THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    MATCH_MP_TAC MOI_S4G_VB_NB THEN ASM_REWRITE_TAC[]]);;

(* Injectivity of f1 on N moves Bd N across images. *)

let MOI_S4G_IMG_BD = prove
 (`!(f:real^N->real^3) N A B X.
     (!x y. x IN N /\ y IN N /\ f x = f y ==> x = y) /\ A SUBSET N /\ B SUBSET N /\
     X INTER IMAGE f N = X INTER IMAGE f B
     ==> X INTER IMAGE f A SUBSET IMAGE f (A INTER B)`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_IMAGE] THEN MESON_TAC[]);;

let MOI_S4G_FRAME_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_frame tt kk h ep f1 car
     ==> f1 continuous_on moi_s34_nb tt kk /\
         (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
         (!v. {v} IN kk
              ==> pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
                  frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                  UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                          g IN moi_s34_simp kk (&1) /\ v IN g}) /\
         (!g. g IN moi_s34_simp kk (&1)
              ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
                    (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN ASM_MESON_TAC[]);;

let MOI_S4G_DD_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd s A.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ s IN moi_s34_simp kk (&2) /\
     A SUBSET moi_s34_nb tt kk
     ==> dd s INTER IMAGE f1 A SUBSET dd s INTER IMAGE f1 (A INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!X Y Z:real^3->bool. X INTER Y SUBSET Z ==> X INTER Y SUBSET X INTER Z`) THEN
  MATCH_MP_TAC MOI_S4G_IMG_BD THEN EXISTS_TAC `moi_s34_nb tt kk:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_FRAME_FACTS];
    MATCH_MP_TAC MOI_S4G_BD_NB THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[moi_s34_simp; IN_ELIM_THM];
    UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
    REWRITE_TAC[moi_s34_fdisk] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_MESON_TAC[]]);;

let MOI_S4G_RR_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r A.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_resid tt kk f1 car dd rr /\ r IN moi_s34_simp kk (&3) /\
     A SUBSET moi_s34_nb tt kk
     ==> rr r INTER IMAGE f1 A SUBSET rr r INTER IMAGE f1 (A INTER moi_s34_bd tt kk)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!X Y Z:real^3->bool. X INTER Y SUBSET Z ==> X INTER Y SUBSET X INTER Z`) THEN
  MATCH_MP_TAC MOI_S4G_IMG_BD THEN EXISTS_TAC `moi_s34_nb tt kk:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_S4G_FRAME_FACTS];
    MATCH_MP_TAC MOI_S4G_BD_NB THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_MESON_TAC[moi_s34_simp; IN_ELIM_THM];
    UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
    REWRITE_TAC[moi_s34_resid] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN ASM_MESON_TAC[]]);;

(* A target missing the vertex balls of the vertices outside q meets F(Bd N) *)
(* only inside the vertex balls of the vertices of q.                         *)

let MOI_S4G_BD_COVER = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) X q y.
     moi_s34_tube tt kk /\ q IN kk /\
     (!w. {w} IN kk /\ ~(w IN q) ==> DISJOINT X (IMAGE f1 (moi_s34_vb tt kk w))) /\
     y IN X /\ y IN IMAGE f1 (moi_s34_bd tt kk)
     ==> ?v. v IN q /\ {v} IN kk /\ y IN IMAGE f1 (moi_s34_vb tt kk v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s34_bd tt kk SUBSET UNIONS {moi_s34_vb tt kk v | v | {v:real^N} IN kk}`
  MP_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4G_NB_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S4G_BD_NB THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE f1 (moi_s34_bd tt (kk:(real^N->bool)->bool))` THEN
  REWRITE_TAC[IN_IMAGE; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `w:real^N` THEN
  ASM_CASES_TAC `(w:real^N) IN q` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `z:real^N` THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

(* F(C_v n Bd N) and F(D_g n Bd N) are covered by the tetra balls and, at  *)
(* the boundary of kk, by the outer patch and the outer arc.                 *)

let MOI_S4G_VB_BD_SPLIT = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr v y.
     moi_s34_resid tt kk f1 car dd rr /\ {v} IN kk /\
     y IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> (?r. r IN moi_s34_simp kk (&3) /\ v IN r /\ y IN rr r) \/
         (v IN complex_boundary kk /\ y IN moi_s34_opatch tt kk f1 rr v)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?r. r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r /\ (y:real^3) IN rr r` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(v:real^N) IN complex_boundary kk` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[moi_s34_opatch] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
    REWRITE_TAC[moi_s34_resid] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_S4G_SD_BD_SPLIT = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd rr g y.
     moi_s34_resid tt kk f1 car dd rr /\ g IN moi_s34_simp kk (&1) /\
     y IN IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
     ==> (?r. r IN moi_s34_simp kk (&3) /\ g SUBSET r /\ y IN rr r) \/
         (g SUBSET complex_boundary kk /\ y IN moi_s34_oarc tt kk f1 rr g)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?r. r IN moi_s34_simp kk (&3) /\ (g:real^N->bool) SUBSET r /\
                     (y:real^3) IN rr r` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(g:real^N->bool) SUBSET complex_boundary kk` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[moi_s34_oarc] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `moi_s34_resid tt kk (f1:real^N->real^3) car dd rr` THEN
    REWRITE_TAC[moi_s34_resid] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o ONCE_REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_S4G_OPATCH_IN = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) rr v c.
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET c /\ closed c
     ==> moi_s34_opatch tt kk f1 rr v SUBSET c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_opatch] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM SET_TAC[]);;

let MOI_S4G_OARC_IN = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) rr g c.
     IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET c /\ closed c
     ==> moi_s34_oarc tt kk f1 rr g SUBSET c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_oarc] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  ASM SET_TAC[]);;

(* The parameters of a label (without the self-referential q = {CHOICE q}). *)

let MOI_S4G_LAB_PARAMS = prove
 (`!(tt:(real^N->bool)->bool) kk l k q x.
     moi_s4g_lab tt kk l k q x
     ==> (k = 1 ==> x = {} /\ {CHOICE q} IN kk) /\
         (k = 2 ==> x = {} /\ q IN moi_s34_simp kk (&1)) /\
         (k = 3 ==> x = {} /\ q IN moi_s34_simp kk (&2)) /\
         (k = 4 ==> x = {} /\ q IN moi_s34_simp kk (&3)) /\
         (k = 5 ==> q IN moi_s34_simp kk (&3) /\ CHOICE x IN q /\ {CHOICE x} IN kk) /\
         (k = 6 ==> q IN moi_s34_simp kk (&2) /\ CHOICE x IN q /\ {CHOICE x} IN kk) /\
         (k = 7 ==> q IN moi_s34_simp kk (&3) /\ x IN moi_s34_simp kk (&1) /\ x SUBSET q) /\
         (k = 8 ==> q IN moi_s34_simp kk (&2) /\ x IN moi_s34_simp kk (&1) /\ x SUBSET q) /\
         (k = 9 ==> x = {} /\ {CHOICE q} IN kk /\ CHOICE q IN complex_boundary kk) /\
         (k = 10 ==> x = {} /\ q IN moi_s34_simp kk (&1) /\ q SUBSET complex_boundary kk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ; MOI_S4G_CHOICE_SING]);;

(* The boundary of a target by labels of the proper faces. *)

let MOI_S4G_BDRY_MEM = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) dd rr l k q x y.
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x
     ==> (y IN UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                       m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)} <=>
          ?m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\
                       moi_s4g_face kk k' q' x' k q x /\
                       ~(k' = k /\ q' = q /\ x' = x) /\
                       y IN moi_s4g_tgtl tt kk f1 dd rr k' q' x')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(m:real^N->bool) IN moi_s34_scells tt kk` THEN
    REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `q':real^N->bool`
      (X_CHOOSE_TAC `x':real^N->bool`))) THEN
    MAP_EVERY EXISTS_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                   `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                   `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_PROPER_FACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                   `m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`]
                  MOI_S4G_TGT_EVAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `moi_s34_tgt tt kk (f1:real^N->real^3) dd rr m` THEN CONJ_TAC THENL
     [EXISTS_TAC `m:real^N->bool` THEN REWRITE_TAC[MOI_S4G_SCELLS_LAB] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                     `k:num`; `q:real^N->bool`; `x:real^N->bool`; `m:real^N->bool`;
                     `k':num`; `q':real^N->bool`; `x':real^N->bool`] MOI_S4G_PROPER_FACE) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                     `m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`]
                    MOI_S4G_TGT_EVAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The boundary of a target equals H when the proper-face targets lie in H *)
(* and cover it (the per-kind boundary identities MOI_S4G_BS1-BS10 below).   *)

let MOI_S4G_BS_RULE = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) dd rr l k q x (H:real^3->bool).
     moi_s34_tube tt kk /\ moi_s4g_lab tt kk l k q x /\
     (!m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\ moi_s4g_face kk k' q' x' k q x /\
                   ~(k' = k /\ q' = q /\ x' = x)
                   ==> moi_s4g_tgtl tt kk f1 dd rr k' q' x' SUBSET H) /\
     (!y. y IN H
          ==> ?m k' q' x'. moi_s4g_lab tt kk m k' q' x' /\
                           moi_s4g_face kk k' q' x' k q x /\
                           ~(k' = k /\ q' = q /\ x' = x) /\
                           y IN moi_s4g_tgtl tt kk f1 dd rr k' q' x')
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)} = H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC (el 0 cs) THEN ASSUME_TAC (el 1 cs) THEN
    LABEL_TAC "A" (el 2 cs) THEN LABEL_TAC "B" (el 3 cs)) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`;
                 `y:real^3`] MOI_S4G_BDRY_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:real^N->bool`; `k':num`; `q':real^N->bool`; `x':real^N->bool`] THEN
    STRIP_TAC THEN
    USE_THEN "A" (MP_TAC o SPECL [`m:real^N->bool`; `k':num`; `q':real^N->bool`;
                                  `x':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The target cells by kind (TC1-TC10): each target is a PL cell             *)
(* whose boundary is the union of the targets of the proper faces of its     *)
(* source cell.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_IN_IMAGE_INTER = prove
 (`!(f:real^N->real^3) A B y.
     y IN IMAGE f (A INTER B) ==> y IN IMAGE f A /\ y IN IMAGE f B`,
  SET_TAC[]);;

(* Tactics: the hypotheses of a TC lemma; the common start of the inclusion *)
(* part (proper face cases by kind); membership in a union of targets; the  *)
(* Bd N transfer for tetra balls and face disks.                             *)

let MOI_S4G_HYP_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "tube" (el 0 cs) THEN LABEL_TAC "frame" (el 1 cs) THEN
    LABEL_TAC "fdisk" (el 2 cs) THEN LABEL_TAC "resid" (el 3 cs) THEN
    LABEL_TAC "outer" (el 4 cs) THEN MAP_EVERY ASSUME_TAC (snd(chop_list 5 cs)));;

let MOI_S4G_SUB_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_S4G_LAB_PARAMS) MP_TAC) THEN
  REWRITE_TAC[moi_s4g_face; ARITH_EQ; SING_SUBSET] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[ARITH_EQ; MOI_S4G_CHOICE_SING; moi_s4g_tgtl] THEN REPEAT STRIP_TAC;;

let MOI_S4G_UNM_TAC : tactic =
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_MESON_TAC[SING_SUBSET];;

let MOI_S4G_RR_TAC (r:term) (a:term) : tactic =
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`; r; a]
                MOI_S4G_RR_SUB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_S4G_VB_NB; MOI_S4G_SD_NB]; SET_TAC[]];;

let MOI_S4G_DD_TAC (s:term) (a:term) : tactic =
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `dd:(real^N->bool)->real^3->bool`; s; a]
                MOI_S4G_DD_SUB) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_S4G_VB_NB; MOI_S4G_SD_NB]; SET_TAC[]];;

(* Tactic: SET_TAC on the membership and inclusion assumptions only. *)

let MOI_S4G_MSET_TAC : tactic =
  let ok th = let c = concl th in
    let c' = if is_neg c then dest_neg c else c in
    is_comb c' &&
    (let f,_ = strip_comb c' in is_const f && mem (fst(dest_const f)) ["IN"; "SUBSET"]) in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check ok)) THEN SET_TAC[];;

(* The face case MP(s,g) inside a cell at the vertex v of g. *)

let MOI_S4G_MPV_TAC : tactic =
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `x':real^N->bool`;
                 `v:real^N`] MOI_S4G_SD_SUB_VB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE f1 (moi_s34_vb tt kk (v:real^N))` ASSUME_TAC THENL
   [MOI_S4G_MSET_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN q'` ASSUME_TAC THENL [MOI_S4G_MSET_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[];;

(* BS1: the boundary of F(C_v) is its frontier. *)

let MOI_S4G_BS1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ {v} IN kk
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_vb tt kk v /\
                 ~(m = moi_s34_vb tt kk v)} =
         frontier (IMAGE f1 (moi_s34_vb tt kk v))`,
  MOI_S4G_HYP_TAC THEN
  USE_THEN "frame" (MP_TAC o MATCH_MP MOI_S4G_FRAME_FACTS) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MP_TAC (SPEC `v:real^N` (el 2 cs)) THEN LABEL_TAC "fsd" (el 3 cs)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fr")) THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`1`; `{v:real^N}`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_MESON_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 2 *) MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. b SUBSET c ==> b SUBSET a UNION c`) THEN
      MOI_S4G_UNM_TAC;
      (* 5 *) MOI_S4G_RR_TAC `q':real^N->bool` `moi_s34_vb tt kk (v:real^N)`;
      (* 6 *) MOI_S4G_DD_TAC `q':real^N->bool` `moi_s34_vb tt kk (v:real^N)`;
      (* 7 *) MOI_S4G_UNM_TAC;
      (* 8 *) MOI_S4G_UNM_TAC;
      (* 9 *) MATCH_MP_TAC MOI_S4G_OPATCH_IN THEN CONJ_TAC THENL
       [SET_TAC[]; USE_THEN "fr" (fun th -> REWRITE_TAC[GSYM th; FRONTIER_CLOSED])];
      (* 10 *) MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk q')` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4G_OARC_IN THEN CONJ_TAC THENL
         [SET_TAC[];
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
          USE_THEN "fsd" (MP_TAC o SPEC `q':real^N->bool`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[MOI_S4G_CELL_FACTS]]];
        MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. b SUBSET c ==> b SUBSET a UNION c`) THEN
        MOI_S4G_UNM_TAC]];
    X_GEN_TAC `y:real^3` THEN USE_THEN "fr" SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                     `rr:(real^N->bool)->real^3->bool`; `v:real^N`; `y:real^3`]
                    MOI_S4G_VB_BD_SPLIT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
      STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`r INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                              `5`; `r:real^N->bool`; `{v:real^N}`] THEN
        REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING;
                    IN_INTER] THEN
        ASM_MESON_TAC[];
        MAP_EVERY EXISTS_TAC [`closure((moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk) DIFF
                                       UNIONS kk)`; `9`; `{v:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN
        ASM_MESON_TAC[]];
      MAP_EVERY EXISTS_TAC [`moi_s34_sd tt kk (g:real^N->bool)`; `2`; `g:real^N->bool`;
                            `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; SING_SUBSET] THEN
      ASM_MESON_TAC[]]]);;

(* BS2: the boundary of F(D_g) is the rim F(D_g n Bd N). *)

let MOI_S4G_BS2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ g IN moi_s34_simp kk (&1)
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_sd tt kk g /\
                 ~(m = moi_s34_sd tt kk g)} =
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`,
  MOI_S4G_HYP_TAC THEN
  USE_THEN "frame" (MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS o
                    MATCH_MP MOI_S4G_FRAME_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`2`; `g:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 7 *) MOI_S4G_RR_TAC `q':real^N->bool` `moi_s34_sd tt kk (g:real^N->bool)`;
      (* 8 *) MOI_S4G_DD_TAC `q':real^N->bool` `moi_s34_sd tt kk (g:real^N->bool)`;
      (* 10 *) MATCH_MP_TAC MOI_S4G_OARC_IN THEN REWRITE_TAC[SUBSET_REFL] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S4G_CELL_BD_COMPACT THEN
      ASM_MESON_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                   `rr:(real^N->bool)->real^3->bool`; `g:real^N->bool`; `y:real^3`]
                  MOI_S4G_SD_BD_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4G_IN_IMAGE_INTER) THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`r INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                            `7`; `r:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; IN_INTER] THEN
      ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`closure((moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk)
                                     DIFF UNIONS kk)`; `10`; `g:real^N->bool`;
                            `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ] THEN
      ASM_MESON_TAC[]]]);;

(* BS3: the boundary of a face disk dd s is dd s n F(Bd N). *)

let MOI_S4G_BS3 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2)
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\ m SUBSET closure (s DIFF moi_s34_nb tt kk) /\
                 ~(m = closure (s DIFF moi_s34_nb tt kk))} =
         dd s INTER IMAGE f1 (moi_s34_bd tt kk)`,
  MOI_S4G_HYP_TAC THEN
  USE_THEN "fdisk" (MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_fdisk]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in LABEL_TAC "dj" (el 3 cs)) THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`3`; `s:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 6 *) MOI_S4G_DD_TAC `s:real^N->bool` `moi_s34_vb tt kk (CHOICE x':real^N)`;
      (* 8 *) MOI_S4G_DD_TAC `s:real^N->bool` `moi_s34_sd tt kk (x':real^N->bool)`];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                   `(dd:(real^N->bool)->real^3->bool) s`; `s:real^N->bool`; `y:real^3`]
                  MOI_S4G_BD_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (u:real^N) INTER moi_s34_bd tt kk`; `6`;
                          `s:real^N->bool`; `{u:real^N}`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING;
                IN_INTER] THEN
    ASM_MESON_TAC[]]);;

(* BS4: the boundary of a tetra ball rr r is its frontier. *)

let MOI_S4G_BS4 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3)
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\ m SUBSET closure (r DIFF moi_s34_nb tt kk) /\
                 ~(m = closure (r DIFF moi_s34_nb tt kk))} =
         frontier (rr r)`,
  MOI_S4G_HYP_TAC THEN
  USE_THEN "resid" (MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_resid]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "fr" (el 2 cs) THEN LABEL_TAC "dj" (el 6 cs)) THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`4`; `r:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 3 *) MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      MOI_S4G_UNM_TAC;
      (* 6 *) MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      MOI_S4G_UNM_TAC;
      (* 8 *) MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b ==> a SUBSET b UNION c`) THEN
      MOI_S4G_UNM_TAC;
      (* 5 *) MOI_S4G_RR_TAC `r:real^N->bool` `moi_s34_vb tt kk (CHOICE x':real^N)`;
      (* 7 *) MOI_S4G_RR_TAC `r:real^N->bool` `moi_s34_sd tt kk (x':real^N->bool)`];
    X_GEN_TAC `y:real^3` THEN USE_THEN "fr" SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`closure (s DIFF moi_s34_nb tt (kk:(real^N->bool)->bool))`; `3`;
                            `s:real^N->bool`; `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                     `(rr:(real^N->bool)->real^3->bool) r`; `r:real^N->bool`; `y:real^3`]
                    MOI_S4G_BD_COVER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[moi_s34_simp; IN_ELIM_THM]) THEN
        REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`r INTER moi_s34_vb tt kk (u:real^N) INTER moi_s34_bd tt kk`; `5`;
                            `r:real^N->bool`; `{u:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING;
                  IN_INTER] THEN
      ASM_MESON_TAC[]]]);;

(* BS5: patches rr r n F(C_v). *)

let MOI_S4G_BS5 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                 ~(m = r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)} =
         UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
         UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`5`; `r:real^N->bool`; `{v:real^N}`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_MESON_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 6 *) MOI_S4G_UNM_TAC;
      (* 7 *) MOI_S4G_UNM_TAC;
      (* 8 *) MOI_S4G_MPV_TAC];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`; `6`;
                            `s:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN
      ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`r INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                            `7`; `r:real^N->bool`; `g:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; SING_SUBSET] THEN
      ASM_MESON_TAC[]]]);;

(* BS6: face arcs dd s n F(C_v). *)

let MOI_S4G_BS6 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                 ~(m = s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)} =
         UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`6`; `s:real^N->bool`; `{v:real^N}`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_MESON_TAC[];
    MOI_S4G_SUB_TAC THEN MOI_S4G_UNM_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; SING_SUBSET] THEN
    ASM_MESON_TAC[]]);;

(* BS7: edge arcs rr r n F(D_g). *)

let MOI_S4G_BS7 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                 ~(m = r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)} =
         UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                 s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`7`; `r:real^N->bool`; `g:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC THEN MOI_S4G_UNM_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ] THEN
    ASM_MESON_TAC[]]);;

(* BS8: marked points have empty boundary. *)

let MOI_S4G_BS8 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET s
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                 ~(m = s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)} = {}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`8`; `s:real^N->bool`; `g:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC;
    REWRITE_TAC[NOT_IN_EMPTY]]);;

(* BS9: outer patches. *)

let MOI_S4G_BS9 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ {v} IN kk /\ v IN complex_boundary kk
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                   UNIONS kk) /\
                 ~(m = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                UNIONS kk))} =
         UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} UNION
         UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`9`; `{v:real^N}`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_MESON_TAC[];
    MOI_S4G_SUB_TAC THENL
     [(* 6 *) MOI_S4G_UNM_TAC;
      (* 8 *) MOI_S4G_MPV_TAC;
      (* 10 *) MOI_S4G_UNM_TAC];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`s INTER moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`; `6`;
                            `s:real^N->bool`; `{v:real^N}`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN
      ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`closure((moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk)
                                     DIFF UNIONS kk)`; `10`; `g:real^N->bool`;
                            `{}:real^N->bool`] THEN
      REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ; SING_SUBSET] THEN
      ASM_MESON_TAC[]]]);;

(* BS10: outer arcs. *)

let MOI_S4G_BS10 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET complex_boundary kk
     ==> UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                 m IN moi_s34_scells tt kk /\
                 m SUBSET closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                   UNIONS kk) /\
                 ~(m = closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                UNIONS kk))} =
         UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                 s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET complex_boundary kk}`,
  MOI_S4G_HYP_TAC THEN
  MATCH_MP_TAC MOI_S4G_BS_RULE THEN
  MAP_EVERY EXISTS_TAC [`10`; `g:real^N->bool`; `{}:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s4g_lab; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    MOI_S4G_SUB_TAC THEN MOI_S4G_UNM_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s INTER moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                          `8`; `s:real^N->bool`; `g:real^N->bool`] THEN
    REWRITE_TAC[moi_s4g_lab; moi_s4g_face; moi_s4g_tgtl; ARITH_EQ] THEN
    ASM_MESON_TAC[]]);;

(* TC1-TC10: each target is a PL cell bounded by the targets of the proper *)
(* faces of its source cell.                                                *)

let MOI_S4G_TC1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ {v} IN kk
     ==> pl_cell_with_boundary 3 (IMAGE f1 (moi_s34_vb tt kk v))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_vb tt kk v /\
                    ~(m = moi_s34_vb tt kk v)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS1 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "frame" (MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS o
                    MATCH_MP MOI_S4G_FRAME_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_ACCEPT_TAC MOI_S4G_BALL_CELL);;

let MOI_S4G_TC2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ g IN moi_s34_simp kk (&1)
     ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\ m SUBSET moi_s34_sd tt kk g /\
                    ~(m = moi_s34_sd tt kk g)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS2 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "frame" (MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS o
                    MATCH_MP MOI_S4G_FRAME_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let MOI_S4G_TC3 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2)
     ==> pl_cell_with_boundary 2 (dd s)
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\ m SUBSET closure (s DIFF moi_s34_nb tt kk) /\
                    ~(m = closure (s DIFF moi_s34_nb tt kk))})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS3 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "fdisk" (MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_fdisk]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]);;

let MOI_S4G_TC4 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3)
     ==> pl_cell_with_boundary 3 (rr r)
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\ m SUBSET closure (r DIFF moi_s34_nb tt kk) /\
                    ~(m = closure (r DIFF moi_s34_nb tt kk))})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS4 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "resid" (MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_resid]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_ACCEPT_TAC MOI_S4G_BALL_CELL);;

let MOI_S4G_TC5 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk
     ==> pl_cell_with_boundary 2 (rr r INTER IMAGE f1 (moi_s34_vb tt kk v))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                    ~(m = r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS5 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "resid" (MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_resid]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 4 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let MOI_S4G_TC6 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk
     ==> pl_cell_with_boundary 1 (dd s INTER IMAGE f1 (moi_s34_vb tt kk v))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
                    ~(m = s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS6 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "fdisk" (MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_fdisk]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 4 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let MOI_S4G_TC7 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr r g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ r IN moi_s34_simp kk (&3) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r
     ==> pl_cell_with_boundary 1 (rr r INTER IMAGE f1 (moi_s34_sd tt kk g))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                    ~(m = r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS7 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "resid" (MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_resid]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 5 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let MOI_S4G_TC8 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr s g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ s IN moi_s34_simp kk (&2) /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET s
     ==> pl_cell_with_boundary 0 (dd s INTER IMAGE f1 (moi_s34_sd tt kk g))
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
                    ~(m = s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS8 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "fdisk" (MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o REWRITE_RULE[moi_s34_fdisk]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 5 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (SUBST1_TAC o CONJUNCT1)) THEN
  REWRITE_TAC[MOI_S4G_POINT_CELL]);;

let MOI_S4G_TC9 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ {v} IN kk /\ v IN complex_boundary kk
     ==> pl_cell_with_boundary 2 (moi_s34_opatch tt kk f1 rr v)
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                      UNIONS kk) /\
                    ~(m = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                                   UNIONS kk))})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS9 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "outer" (MP_TAC o SPEC `v:real^N` o CONJUNCT1 o REWRITE_RULE[moi_s34_outer]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let MOI_S4G_TC10 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ g IN moi_s34_simp kk (&1) /\
     g SUBSET complex_boundary kk
     ==> pl_cell_with_boundary 1 (moi_s34_oarc tt kk f1 rr g)
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\
                    m SUBSET closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                      UNIONS kk) /\
                    ~(m = closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                   UNIONS kk))})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP MOI_S4G_BS10 th) THEN MP_TAC th) THEN
  MOI_S4G_HYP_TAC THEN
  USE_THEN "outer" (MP_TAC o SPEC `g:real^N->bool` o CONJUNCT2 o REWRITE_RULE[moi_s34_outer]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The target cells for every label, and RECOG_A.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4G_TC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr l k q x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fdisk tt kk f1 car dd /\ moi_s34_resid tt kk f1 car dd rr /\
     moi_s34_outer tt kk f1 dd rr /\ moi_s4g_lab tt kk l k q x
     ==> pl_cell_with_boundary (moi_s4g_kd k) (moi_s4g_tgtl tt kk f1 dd rr k q x)
           (UNIONS {moi_s34_tgt tt kk f1 dd rr m | m |
                    m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  REWRITE_TAC[moi_s4g_lab] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_s4g_kd; moi_s4g_tgtl; ARITH_EQ; MOI_S4G_CHOICE_SING] THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_MESON_TAC[])
    [MOI_S4G_TC1; MOI_S4G_TC2; MOI_S4G_TC3; MOI_S4G_TC4; MOI_S4G_TC5;
     MOI_S4G_TC6; MOI_S4G_TC7; MOI_S4G_TC8; MOI_S4G_TC9; MOI_S4G_TC10]));;

let RECOG_A = prove
 (MOI_S34_RECOG_A,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_tgt_cells] THEN
  X_GEN_TAC `l:real^N->bool` THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[MOI_S4G_SCELLS_LAB]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `q:real^N->bool`
    (X_CHOOSE_TAC `x:real^N->bool`))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `l:real^N->bool`;
                 `k:num`; `q:real^N->bool`; `x:real^N->bool`] MOI_S4G_DIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                 `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                 `l:real^N->bool`; `k:num`; `q:real^N->bool`; `x:real^N->bool`]
                MOI_S4G_TGT_EVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_S4G_TC THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                        `car:(real^N->bool)->real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

