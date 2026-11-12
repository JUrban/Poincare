(* ========================================================================= *)
(* pc_moi_s34_frame: the Sec 34 unit s34_frame.  Main theorem                *)
(* FRAME_FND : |- MOI_FND_SOLID_TORUS_TRIANGLE ==> MOI_S34_FRAME            *)
(* (pc_moi_s34_stmt.ml; Moise, Geometric Topology in Dimensions 2 and 3,    *)
(* GTM 47, Sec 34, p.240, Lemmas 1-2): carriers for the simplices of kk and *)
(* the tube embedding f1 of graph_approximable satisfy the frame clauses.   *)
(* The foundation MOI_FND_SOLID_TORUS_TRIANGLE (pc_moi_fnd_stmt.ml) is       *)
(* proved as GRAPH_TUBE_TRIANGLE_SOLID_TORUS in pc_moi_fnd_tubec.ml and      *)
(* discharged in pc_moi_s34_status.ml.                                       *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_margin.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_moi_s35_approx.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_s34_outer.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Open stars of graph vertices: a map continuous and injective on a set     *)
(* m sends open subsets of the open star inside m to open sets (vertex chart *)
(* MOI_FMB_STAR_SPHERE_CHART and invariance of domain, as in                *)
(* MOI_S5A_STAR_IMAGE_OPEN, with the map given only on m).                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_STAR_IMAGE_OPEN_ON = prove
 (`!(t:(real^N->bool)->bool) l (f:real^N->real^3) m w u.
     graph_in_complex t l /\ {w} IN l /\ f continuous_on m /\
     (!x y. x IN m /\ y IN m /\ f x = f y ==> x = y) /\ open u /\
     u INTER moi_sta_open_star t w SUBSET m
     ==> open (IMAGE f (u INTER moi_sta_open_star t w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\
                {w:real^N} IN t /\
                pl_sphere 2 (UNIONS (simplicial_link t w))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
    UNDISCH_TAC `{w:real^N} IN l` THEN SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `w:real^N`]
    MOI_FMB_STAR_SPHERE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `p':real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `o0 = (u:real^N->bool) INTER moi_sta_open_star t w` THEN
  SUBGOAL_THEN `(o0:real^N->bool) SUBSET moi_sta_open_star t w` ASSUME_TAC THENL
   [EXPAND_TAC "o0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^3) o0)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) (moi_sta_open_star t w)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^3->real^N`;
                          `moi_sta_open_star t (w:real^N)`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "o0" THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (moi_sta_open_star t (w:real^N),
                              IMAGE (p:real^N->real^3) (moi_sta_open_star t w))
                             (p,p')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^3) o0 =
    IMAGE (f o (p':real^3->real^N)) (IMAGE (p:real^N->real^3) o0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE (f:real^N->real^3) s = IMAGE g s`)
    THEN UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
    UNDISCH_TAC `!x. x IN moi_sta_open_star t w
                     ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (p:real^N->real^3) (moi_sta_open_star t w)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
      UNDISCH_TAC `(o0:real^N->bool) SUBSET m` THEN
      UNDISCH_TAC `!x. x IN moi_sta_open_star t w
                       ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]];
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^N) IN moi_sta_open_star t w /\
                  (b:real^N) IN moi_sta_open_star t w /\
                  (a:real^N) IN m /\ (b:real^N) IN m` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
      UNDISCH_TAC `(o0:real^N->bool) SUBSET m` THEN
      UNDISCH_TAC `(a:real^N) IN o0` THEN UNDISCH_TAC `(b:real^N) IN o0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p':real^3->real^N) (p a) = a /\ p' (p b) = b`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x y. x IN m /\ y IN m /\ (f:real^N->real^3) x = f y ==> x = y`)) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Simplices, vertices and open stars in a locally finite complex.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_SIMPLEX_VERTS_FINITE = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ s IN t ==> FINITE {w | {w} IN t /\ w IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{w:real^N | w extreme_point_of s}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
    MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
    UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM FACE_OF_SING] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{w:real^N} = {w} INTER s` SUBST1_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN s` THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPECL [`{w:real^N}`; `s:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

let MOI_S4K_COFACES_FINITE = prove
 (`!(t:(real^N->bool)->bool) x.
     lf_simplicial_complex t /\ x IN UNIONS t
     ==> FINITE {r | r IN t /\ x IN r}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ ~(s INTER u = {})}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN r` THEN UNDISCH_TAC `(x:real^N) IN u` THEN SET_TAC[]);;

let MOI_S4K_IN_VERTEX_STAR = prove
 (`!(t:(real^N->bool)->bool) q x.
     lf_simplicial_complex t /\ q IN t /\ x IN q
     ==> ?v. {v} IN t /\ v IN q /\ x IN moi_sta_open_star t v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_STA_OPEN_STAR_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN moi_sta_open_star t v` THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

let MOI_S4K_OPEN_STAR_FACTS = prove
 (`!(t:(real^N->bool)->bool) q v.
     (v IN q /\ {v} IN t ==> moi_sta_open_star t v SUBSET moi_s34_cstar t q) /\
     (q IN t /\ ~(v IN q) ==> DISJOINT (moi_sta_open_star t v) q) /\
     moi_sta_open_star t v SUBSET UNIONS t`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[SUBSET; moi_sta_open_star; moi_s34_cstar;
                               IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                               moi_sta_open_star; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `q:real^N->bool`)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* PL images under a map that is PL and injective on a set m: cells         *)
(* (transfer of the model simplex as in MOI_FCL_CELL_TRANSFER, via          *)
(* CHOOSE_SIMPLEX and MOI_FM3_SIMPLEX_PLH), solid tori, and the PL          *)
(* homeomorphism onto the image of a polyhedron (PL_INJECTIVE_INVERSE).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_CELL_TRANSFER = prove
 (`!n (X:real^M->bool) bX (Y:real^P->bool) f f'.
     pl_cell_with_boundary n X bX /\ pl_homeomorphism (X,Y) (f,f') /\
     n <= dimindex(:P)
     ==> pl_cell_with_boundary n Y (IMAGE f bX)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `a:real^M->real^M`
     (X_CHOOSE_THEN `b:real^M->real^M` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `&n:int` (INST_TYPE [`:P`,`:N`] CHOOSE_SIMPLEX)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `k':real^P->bool`)] THEN
  MP_TAC(ISPECL [`k':real^P->bool`; `k:real^M->bool`; `&n:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^P->real^M` (X_CHOOSE_THEN `q:real^M->real^P`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`k':real^P->bool`; `(f:real^M->real^P) o (a:real^M->real^M) o (p:real^P->real^M)`;
    `((q:real^M->real^P) o (b:real^M->real^M)) o (f':real^P->real^M)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `X:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier k',relative_frontier k)
                 (p:real^P->real^M,q)` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_S4K_CELL_POLY = prove
 (`!n (X:real^N->bool) b. pl_cell_with_boundary n X b ==> pl_polyhedron X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `a:real^N->real^N`
    (X_CHOOSE_THEN `c:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `X:real^N->bool = IMAGE (a:real^N->real^N) k` SUBST1_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_S4K_PLH_ON = prove
 (`!(m:real^N->bool) (f:real^N->real^3) X.
     pl_map_on m f /\ (!x y. x IN m /\ y IN m /\ f x = f y ==> x = y) /\
     X SUBSET m /\ pl_polyhedron X
     ==> ?g. pl_homeomorphism (X,IMAGE f X) (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_INJECTIVE_INVERSE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    UNDISCH_TAC `(X:real^N->bool) SUBSET m` THEN
    UNDISCH_TAC `!x y. x IN m /\ y IN m /\ (f:real^N->real^3) x = f y ==> x = y` THEN
    SET_TAC[]]);;

let MOI_S4K_CELL_IMAGE = prove
 (`!n (m:real^N->bool) (f:real^N->real^3) X b.
     pl_cell_with_boundary n X b /\ X SUBSET m /\ pl_map_on m f /\
     (!x y. x IN m /\ y IN m /\ f x = f y ==> x = y) /\ n <= 3
     ==> pl_cell_with_boundary n (IMAGE f X) (IMAGE f b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `f:real^N->real^3`; `X:real^N->bool`]
    MOI_S4K_PLH_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4K_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N`)] THEN
  MATCH_MP_TAC MOI_S4K_CELL_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `g:real^3->real^N`] THEN
  ASM_REWRITE_TAC[DIMINDEX_3]);;

let MOI_S4K_SOLID_TORUS_IMAGE = prove
 (`!(m:real^N->bool) (f:real^N->real^3) X.
     pl_solid_torus X /\ pl_polyhedron X /\ X SUBSET m /\ pl_map_on m f /\
     (!x y. x IN m /\ y IN m /\ f x = f y ==> x = y)
     ==> pl_solid_torus (IMAGE f X)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^N->bool`; `f:real^N->real^3`; `X:real^N->bool`]
    MOI_S4K_PLH_ON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N`) THEN
  UNDISCH_TAC `pl_solid_torus (X:real^N->bool)` THEN REWRITE_TAC[pl_solid_torus] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^(2,1)finite_sum->real^N`
    (X_CHOOSE_TAC `c:real^N->real^(2,1)finite_sum`)) THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^N->real^3) o (a:real^(2,1)finite_sum->real^N)`;
    `(c:real^N->real^(2,1)finite_sum) o (g:real^3->real^N)`] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `X:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The carriers.  car q is h of the union of the open stars (in tt) of      *)
(* the vertices of q, cut down to the d r-neighbourhoods of h(r UNION N_r)  *)
(* for the 3-simplices r of kk containing q (d r from MARGIN).              *)
(* ------------------------------------------------------------------------- *)

let moi_s4k_car = new_definition
 `moi_s4k_car (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (h:real^N->real^3) (d:(real^N->bool)->real) (q:real^N->bool) =
    IMAGE h (UNIONS {moi_sta_open_star tt v | v | v IN q /\ {v} IN kk}) INTER
    INTERS {{y | ?x. x IN r UNION moi_s34_ft tt kk r /\ dist(y,h x) < d r} | r |
            r IN moi_s34_simp kk (&3) /\ q SUBSET r}`;;

let MOI_S4K_TUBE_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> lf_simplicial_complex tt /\ lf_simplicial_complex kk /\ kk SUBSET tt /\
         (!s f. s IN kk /\ f face_of s ==> f IN kk) /\
         graph_in_complex tt (skeleton 1 kk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ASM_MESON_TAC[simplicial_subcomplex];
    ASM_MESON_TAC[simplicial_subcomplex]]);;

let MOI_S4K_SKEL_VERTEX = prove
 (`!(kk:(real^N->bool)->bool) v. {v} IN skeleton 1 kk <=> {v} IN kk`,
  REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS]);;

let MOI_S4K_NBHD_OPEN = prove
 (`!(h:real^N->real^3) a e.
     open {y | ?x. x IN a /\ dist(y,h x) < e}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y | ?x. x IN a /\ dist(y,(h:real^N->real^3) x) < e} =
                UNIONS (IMAGE (\x. ball(h x,e)) a)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
    MESON_TAC[DIST_SYM];
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL]]);;

let MOI_S4K_CAR_MONO = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d q q'.
     q SUBSET q' ==> moi_s4k_car tt kk h d q SUBSET moi_s4k_car tt kk h d q'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4k_car] THEN
  MATCH_MP_TAC(SET_RULE
   `a SUBSET a' /\ b SUBSET b' ==> (a:real^3->bool) INTER b SUBSET a' INTER b'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^N) IN q` THEN UNDISCH_TAC `(q:real^N->bool) SUBSET q'` THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN X_GEN_TAC `t:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x:real^N. x IN q' ==> x IN r` THEN
    UNDISCH_TAC `(q:real^N->bool) SUBSET q'` THEN SET_TAC[]]);;

let MOI_S4K_CAR_VERTEX = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d v.
     {v} IN kk ==> moi_s4k_car tt kk h d {v} SUBSET IMAGE h (moi_sta_open_star tt v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4k_car] THEN
  MATCH_MP_TAC(SET_RULE `a SUBSET a' ==> (a:real^3->bool) INTER b SUBSET a'`) THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[]);;

let MOI_S4K_CAR_BASIC = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d q.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ q IN kk /\ ~(q = {}) /\
     (!r. r IN moi_s34_simp kk (&3) ==> &0 < d r)
     ==> open (moi_s4k_car tt kk h d q) /\
         moi_s4k_car tt kk h d q SUBSET IMAGE h (UNIONS tt) /\
         IMAGE h q SUBSET moi_s4k_car tt kk h d q /\
         moi_s4k_car tt kk h d q SUBSET IMAGE h (moi_s34_cstar tt q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {moi_sta_open_star tt v | v | v IN q /\ {v} IN kk} SUBSET
                moi_s34_cstar tt (q:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `q:real^N->bool`; `v:real^N`]
      MOI_S4K_OPEN_STAR_FACTS) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `{v:real^N} IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_cstar tt (q:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_cstar] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET
                UNIONS {moi_sta_open_star tt v | v | v IN q /\ {v} IN kk}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `q:real^N->bool`; `x:real^N`]
      MOI_S4K_IN_VERTEX_STAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(q:real^N->bool) IN kk` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `moi_sta_open_star tt (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!s f. s IN kk /\ f face_of s ==> f IN (kk:(real^N->bool)->bool)`)) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{v:real^N} = {v} INTER q` SUBST1_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN q` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `q:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(q:real^N->bool) IN kk` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s4k_car] THEN MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN MATCH_MP_TAC OPEN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S4M_OPEN_STAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
        UNDISCH_TAC `{v:real^N} IN kk` THEN SET_TAC[];
        UNDISCH_TAC `graph_in_complex tt (skeleton 1 (kk:(real^N->bool)->bool))` THEN
        REWRITE_TAC[graph_in_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX]];
      MATCH_MP_TAC OPEN_INTERS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o GEN_REWRITE_RULE I
          [GSYM MEMBER_NOT_EMPTY]) THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{r:real^N->bool | r IN kk /\ x IN r}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S4K_COFACES_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
          EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN
          UNDISCH_TAC `(x:real^N) IN q` THEN SET_TAC[]];
        REWRITE_TAC[FORALL_IN_GSPEC; MOI_S4K_NBHD_OPEN]]];
    REWRITE_TAC[moi_s4k_car] THEN
    MATCH_MP_TAC(SET_RULE `a SUBSET a' ==> (a:real^3->bool) INTER b SUBSET a'`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `moi_s34_cstar tt (q:real^N->bool) SUBSET UNIONS tt` THEN
    UNDISCH_TAC `UNIONS {moi_sta_open_star tt v | v | v IN q /\ {v} IN kk} SUBSET
                 moi_s34_cstar tt (q:real^N->bool)` THEN SET_TAC[];
    REWRITE_TAC[moi_s4k_car; SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    REWRITE_TAC[DIST_REFL; IN_UNION] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    REWRITE_TAC[moi_s4k_car] THEN
    MATCH_MP_TAC(SET_RULE `a SUBSET a' ==> (a:real^3->bool) INTER b SUBSET a'`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Carrier clauses: vertex carriers miss the simplices not containing      *)
(* the vertex (9), contain h of the vertex ball, smallness (13), the       *)
(* margin clause (11), local finiteness at their own points (12).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_CAR_DISJOINT = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d v q.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     {v} IN kk /\ q IN kk /\ ~(v IN q)
     ==> DISJOINT (moi_s4k_car tt kk h d {v}) (IMAGE h q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `d:(real^N->bool)->real`; `v:real^N`]
    MOI_S4K_CAR_VERTEX) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `q:real^N->bool`; `v:real^N`]
    MOI_S4K_OPEN_STAR_FACTS) THEN
  SUBGOAL_THEN `(q:real^N->bool) IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(q:real^N->bool) IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^N->bool) IN tt` THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_sta_open_star tt (v:real^N) SUBSET UNIONS tt` THEN
  UNDISCH_TAC `(q:real^N->bool) SUBSET UNIONS tt` THEN
  UNDISCH_TAC `DISJOINT (moi_sta_open_star tt (v:real^N)) q` THEN
  UNDISCH_TAC `!x y. x IN UNIONS tt /\ y IN UNIONS tt /\ (h:real^N->real^3) x = h y
                     ==> x = y` THEN
  SET_TAC[]);;

let MOI_S4K_CAR_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d v.
     moi_s34_tube tt kk /\ {v} IN kk /\
     (!r. r IN moi_s34_simp kk (&3) ==> &0 < d r)
     ==> IMAGE h (moi_s34_vb tt kk v) SUBSET moi_s4k_car tt kk h d {v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  REWRITE_TAC[moi_s4k_car; SUBSET_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_sta_open_star tt (v:real^N)` THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s34_vb] THEN MATCH_MP_TAC MOI_S5A_CELL_OPEN_STAR THEN
      ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `moi_sta_open_star tt (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
  REWRITE_TAC[DIST_REFL; IN_UNION] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[moi_s34_ft; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{v:real^N} SUBSET r` THEN SET_TAC[];
    ASM_SIMP_TAC[]]);;

let MOI_S4K_CAR_SMALL = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep d q x y z.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ moi_s34_fine tt kk h ep /\
     (!x. x IN UNIONS kk ==> &0 < ep x) /\
     (!r. r IN moi_s34_simp kk (&3) ==> &0 < d r) /\
     q IN kk /\ x IN q /\
     y IN moi_s4k_car tt kk h d q /\ z IN moi_s4k_car tt kk h d q
     ==> dist(y,z) < ep x / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `d:(real^N->bool)->real`; `q:real^N->bool`]
    MOI_S4K_CAR_BASIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^N) IN q` THEN SET_TAC[];
    DISCH_THEN(MP_TAC o last o CONJUNCTS)] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `y:real^3` th) THEN MP_TAC(SPEC `z:real^3` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (ep:real^N->real) x` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(ep:real^N->real) x / &4` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `moi_s34_fine tt kk (h:real^N->real^3) ep` THEN
    REWRITE_TAC[moi_s34_fine] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `&0 < (ep:real^N->real) x` THEN REAL_ARITH_TAC]);;

let MOI_S4K_CAR_OUTSIDE = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d r w.
     r IN moi_s34_simp kk (&3) /\ {w} IN kk /\ ~(w IN r) /\
     h w IN outside {y | ?x. x IN r UNION moi_s34_ft tt kk r /\ dist(y,h x) <= d r}
     ==> h w IN outside (UNIONS {moi_s4k_car tt kk h d q | q |
                                 q IN kk /\ ~(q = {}) /\ q SUBSET r /\ ~(q = r)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!(s:real^3->bool) t. s SUBSET t /\ x IN s ==> x IN t`) THEN
  EXISTS_TAC `outside {y | ?x. x IN r UNION moi_s34_ft tt kk r /\
                               dist(y,(h:real^N->real^3) x) <= d r}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OUTSIDE_MONO THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4k_car] THEN
  MATCH_MP_TAC(SET_RULE `b SUBSET c ==> (a:real^3->bool) INTER b SUBSET c`) THEN
  MATCH_MP_TAC(SET_RULE `!(s:real^3->bool) f. s IN f /\ s SUBSET t ==> INTERS f SUBSET t`) THEN
  EXISTS_TAC `{y | ?x. x IN r UNION moi_s34_ft tt kk r /\
                       dist(y,(h:real^N->real^3) x) < d r}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]]);;


(* ------------------------------------------------------------------------- *)
(* Local finiteness of the carriers at their own points (clause 12):       *)
(* at y = h x, x in the open star of a vertex v0, the open set             *)
(* h(oo INTER ost v0), oo from the local finiteness of tt at x, meets only   *)
(* the carriers of simplices with a vertex in one of the finitely many     *)
(* simplices of tt meeting oo.                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_CAR_LF = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt)
     ==> !y. y IN UNIONS {moi_s4k_car tt kk h d q | q | q IN kk /\ ~(q = {})}
             ==> ?u. open u /\ y IN u /\
                     FINITE {q | q IN kk /\ ~(q = {}) /\
                                 ~(moi_s4k_car tt kk h d q INTER u = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `q0:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `?x v0. {v0} IN kk /\ x IN moi_sta_open_star tt v0 /\
                       y = (h:real^N->real^3) x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN c0` THEN ASM_REWRITE_TAC[moi_s4k_car; IN_INTER] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_sta_open_star tt v0` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(SPEC `x:real^N` (last(CONJUNCTS(REWRITE_RULE[lf_simplicial_complex] th))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (h:real^N->real^3) (oo INTER moi_sta_open_star tt v0)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5A_STAR_IMAGE_OPEN THEN
    EXISTS_TAC `skeleton 1 (kk:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `S0 = {s:real^N->bool | s IN tt /\ ~(s INTER oo = {})}` THEN
  ABBREV_TAC `V0 = UNIONS {{w:real^N | {w} IN tt /\ w IN s} | s | s IN S0}` THEN
  SUBGOAL_THEN `FINITE (V0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[SET_RULE `!s:A->bool. {x | x IN s} = s`];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN
      DISCH_TAC THEN MATCH_MP_TAC MOI_S4K_SIMPLEX_VERTS_FINITE THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^N->bool) IN S0` THEN
      EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {{q:real^N->bool | q IN tt /\ w IN q} | w | w IN V0}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[SET_RULE `!s:A->bool. {x | x IN s} = s`];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_TAC THEN MATCH_MP_TAC MOI_S4K_COFACES_FINITE THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:real^N) IN V0` THEN EXPAND_TAC "V0" THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `vs:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
  X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
    concl th = `~(moi_s4k_car tt kk (h:real^N->real^3) d q INTER
                  IMAGE h (oo INTER moi_sta_open_star tt v0) = {})`)) THEN
  REWRITE_TAC[moi_s4k_car; IN_INTER; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC) (K ALL_TAC))
    (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(z1:real^N) = z2` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x y. x IN UNIONS tt /\ y IN UNIONS tt /\ (h:real^N->real^3) x = h y
                        ==> x = y`)) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(z1:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[];
      UNDISCH_TAC `(z2:real^N) IN moi_sta_open_star tt v0` THEN
      REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z2:real^N) IN moi_sta_open_star tt v` ASSUME_TAC THENL
   [UNDISCH_TAC `(z2:real^N) IN t` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN tt /\ z2 IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z2:real^N) IN moi_sta_open_star tt v` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `(z2:real^N) IN moi_sta_open_star tt v` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{q':real^N->bool | q' IN tt /\ v IN q'}` THEN CONJ_TAC THENL
   [EXISTS_TAC `v:real^N` THEN REWRITE_TAC[] THEN EXPAND_TAC "V0" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `{w:real^N | {w} IN tt /\ w IN s}` THEN CONJ_TAC THENL
     [EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[] THEN EXPAND_TAC "S0" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z2:real^N) IN s` THEN UNDISCH_TAC `(z2:real^N) IN oo` THEN
      SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `{v:real^N} IN kk` THEN SET_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(q:real^N->bool) IN kk` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Vertex balls and splitting disks as cells (GRAPH_TUBE_DUAL_CELLS),      *)
(* their images under f1 (PL ball, frontier, PL 2-cell).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_EDGE_SD = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> {moi_s34_vb tt kk v INTER moi_s34_vb tt kk w | w |
          ~(w = v) /\ segment[v,w] IN skeleton 1 kk} =
         {moi_s34_sd tt kk g | g | g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N->bool` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `segment[v:real^N,w] IN skeleton 1 kk` THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:real^N = v)` THEN MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `w:real^N`] MOI_S4A_SD_EDGE) THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(v:real^N) = a \/ v = b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXTREME_POINT_OF_SEGMENT; GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{v:real^N} = {v} INTER segment[a,b]` SUBST1_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `segment[a:real^N,b]`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (g:real^N->bool) = moi_s34_vb tt kk a INTER moi_s34_vb tt kk b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `a:real^N`; `b:real^N`] MOI_S4A_SD_EDGE) THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] IN skeleton 1 kk` ASSUME_TAC THENL
   [REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
    ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[b:real^N,a] IN skeleton 1 kk` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a:real^N = b)` THEN MESON_TAC[];
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[INTER_COMM]]);;

let MOI_S4K_VB_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk /\
         pl_cell_with_boundary 3 (moi_s34_vb tt kk v)
           ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
            UNIONS {moi_s34_sd tt kk g | g | g IN moi_s34_simp kk (&1) /\ v IN g})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
    GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `v:real^N` o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_vb; moi_s34_nb] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `derived_dual_cell tt (skeleton 1 kk) (v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real^N` THEN
    ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4K_EDGE_SD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[moi_s34_vb; moi_s34_bd]]);;

let MOI_S4K_SD_CELL = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> moi_s34_sd tt kk g SUBSET moi_s34_nb tt kk /\
         pl_cell_with_boundary 2 (moi_s34_sd tt kk g)
           (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`] MOI_S4A_SD_EDGE) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `a:real^N`]
    MOI_S4K_VB_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] IN skeleton 1 kk` ASSUME_TAC THENL
   [REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
    ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(MP (SPECL [`a:real^N`; `b:real^N`] (CONJUNCT1 (CONJUNCT2 (CONJUNCT2
    (MATCH_MP GRAPH_TUBE_DUAL_CELLS
      (ASSUME `graph_in_complex tt (skeleton 1 (kk:(real^N->bool)->bool))`))))))
    (CONJ (ASSUME `~(a:real^N = b)`)
          (ASSUME `segment[a:real^N,b] IN skeleton 1 kk`))) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[moi_s34_vb; moi_s34_bd; INTER_ASSOC]);;


(* ------------------------------------------------------------------------- *)
(* Images of the vertex balls and splitting disks under a map PL and       *)
(* injective on N: PL 3-balls with frontier the image of the cell boundary *)
(* (MOI_S5A_CELL_BD_NOT_INTERIOR, MOI_S5A_CELL_INT_INTERIOR), PL 2-cells.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_VB_IMAGE = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) v.
     moi_s34_tube tt kk /\ pl_map_on (moi_s34_nb tt kk) f1 /\
     (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
     {v} IN kk
     ==> pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4K_VB_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `C = moi_s34_vb tt kk (v:real^N)` THEN
  ABBREV_TAC `B = (C INTER moi_s34_bd tt kk) UNION
                  UNIONS {moi_s34_sd tt kk g | g |
                          g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `compact (C:real^N->bool) /\ compact (B:real^N->bool) /\ B SUBSET C`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5A_CELL_COMPACT THEN EXISTS_TAC `3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real^N->real^3) continuous_on C` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN C /\ y IN C /\ (f1:real^N->real^3) x = f1 y ==> x = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(C:real^N->bool) SUBSET moi_s34_nb tt kk` THEN
    UNDISCH_TAC `!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\
                       (f1:real^N->real^3) x = f1 y ==> x = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5A_PL_BALL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`B:real^N->bool`; `moi_s34_nb tt (kk:(real^N->bool)->bool)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (f1:real^N->real^3) C) = IMAGE f1 B` SUBST1_TAC THENL
   [SUBGOAL_THEN `closed (IMAGE (f1:real^N->real^3) C)` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(x:real^N) IN B` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((y:real^3) IN interior (IMAGE (f1:real^N->real^3) C))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5A_CELL_INT_INTERIOR THEN
      EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5A_CELL_BD_NOT_INTERIOR THEN
        EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  EXPAND_TAC "B" THEN REWRITE_TAC[IMAGE_UNION; IMAGE_UNIONS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_S4K_SD_IMAGE = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) g.
     moi_s34_tube tt kk /\ pl_map_on (moi_s34_nb tt kk) f1 /\
     (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
     g IN moi_s34_simp kk (&1)
     ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4K_SD_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4K_CELL_IMAGE THEN
  EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Clause (4): f1(N) DIFF interior f1(N) = f1(Bd N).  Interior points      *)
(* of N in |tt| go to interior points (open images of open parts of open   *)
(* stars); a frontier point of N cannot go to an interior point: a local   *)
(* inverse of f1 on a compact finite union of vertex balls (local          *)
(* finiteness of the carriers) and the vertex chart would make it a        *)
(* |tt|-interior point of N.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_STAR_OPEN_IN = prove
 (`!(t:(real^N->bool)->bool) l (g:real^3->real^N) b w.
     graph_in_complex t l /\ {w} IN l /\ open b /\ g continuous_on b /\
     (!x y. x IN b /\ y IN b /\ g x = g y ==> x = y) /\
     IMAGE g b SUBSET moi_sta_open_star t w
     ==> open_in (subtopology euclidean (UNIONS t)) (IMAGE g b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\
                {w:real^N} IN t /\
                pl_sphere 2 (UNIONS (simplicial_link t w))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
    UNDISCH_TAC `{w:real^N} IN l` THEN SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `w:real^N`]
    MOI_FMB_STAR_SPHERE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `p':real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `homeomorphism (moi_sta_open_star t (w:real^N),
                              IMAGE (p:real^N->real^3) (moi_sta_open_star t w))
                             (p,p')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN b ==> (g:real^3->real^N) x IN moi_sta_open_star t w`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^N) b SUBSET moi_sta_open_star t w` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE ((p:real^N->real^3) o (g:real^3->real^N)) b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_sta_open_star t (w:real^N)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
        `!x y. x IN b /\ y IN b /\ (g:real^3->real^N) x = g y ==> x = y`)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p':real^3->real^N) (p ((g:real^3->real^N) x1)) = g x1 /\
                    p' (p (g x2)) = g x2` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
          `!x. x IN moi_sta_open_star t w
               ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x`)) THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^3->real^N) b =
    {z | z IN moi_sta_open_star t w /\
         (p:real^N->real^3) z IN IMAGE (p o g) b}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(p':real^3->real^N) (p (z:real^N)) = z /\
                    p' (p ((g:real^3->real^N) x)) = g x` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
          `!x. x IN moi_sta_open_star t w
               ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x`)) THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `moi_sta_open_star t (w:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_STA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[]]);;

let MOI_S4K_NB_UNION_CELLS = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> moi_s34_nb tt kk = UNIONS {moi_s34_vb tt kk v | v | {v} IN kk} /\
         moi_s34_bd tt kk SUBSET moi_s34_nb tt kk /\
         moi_s34_nb tt kk SUBSET UNIONS tt /\
         closed_in (subtopology euclidean (UNIONS tt)) (moi_s34_nb tt kk)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
    DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `graph_in_complex tt (skeleton 1 (kk:(real^N->bool)->bool))` THEN
    SIMP_TAC[graph_in_complex];
    STRIP_TAC] THEN
  REWRITE_TAC[moi_s34_nb; moi_s34_bd; moi_s34_vb] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
      GRAPH_TUBE_DUAL_CELLS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
    REWRITE_TAC[derived_frontier] THEN MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    ASM_REWRITE_TAC[]]);;


let MOI_S4K_TUBE_FRONTIER = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3)
    (car:(real^N->bool)->real^3->bool).
     moi_s34_tube tt kk /\ pl_map_on (moi_s34_nb tt kk) f1 /\
     (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
     (!v. {v} IN kk ==> IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v}) /\
     (!y. y IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
          ==> ?u. open u /\ y IN u /\
                  FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})})
     ==> IMAGE f1 (moi_s34_nb tt kk) DIFF interior (IMAGE f1 (moi_s34_nb tt kk)) =
         IMAGE f1 (moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "vbc")
      (LABEL_TAC "lf"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4K_NB_UNION_CELLS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nbu") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^N. x IN moi_s34_nb tt kk
                           ==> ?v. {v} IN kk /\ x IN moi_s34_vb tt kk v`
  (LABEL_TAC "cov") THENL
   [USE_THEN "nbu" (fun th -> GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o RAND_CONV)
      [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN kk
                ==> moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk /\
                    moi_s34_vb tt kk v SUBSET moi_sta_open_star tt v /\
                    compact (moi_s34_vb tt kk v)`
  (LABEL_TAC "vbf") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4K_VB_CELL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_s34_vb] THEN MATCH_MP_TAC MOI_S5A_CELL_OPEN_STAR THEN
      ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX];
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_COMPACT) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "nbu" (K ALL_TAC) THEN
  SUBGOAL_THEN `moi_s34_bd (tt:(real^N->bool)->bool) kk =
                (subtopology euclidean (UNIONS tt)) frontier_of (moi_s34_nb tt kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_bd; moi_s34_nb; derived_frontier]; ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real^N->real^3) continuous_on moi_s34_nb tt kk` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  ABBREV_TAC `N = moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
  ABBREV_TAC `Bd = moi_s34_bd (tt:(real^N->bool)->bool) kk` THEN
  ABBREV_TAC `top = subtopology euclidean (UNIONS (tt:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(N:real^N->bool) SUBSET top closure_of N` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN EXPAND_TAC "top" THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((y:real^3) IN interior (IMAGE (f1:real^N->real^3) N))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN top interior_of N` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^N) IN top frontier_of N)` THEN
      REWRITE_TAC[frontier_of; IN_DIFF] THEN
      UNDISCH_TAC `(N:real^N->bool) SUBSET top closure_of N` THEN
      UNDISCH_TAC `(x:real^N) IN N` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:(real^N)topology`; `N:real^N->bool`] OPEN_IN_INTERIOR_OF) THEN
    EXPAND_TAC "top" THEN REWRITE_TAC[OPEN_IN_OPEN] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN N`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "vbf" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
  STRIP_TAC THEN
    SUBGOAL_THEN `U INTER moi_sta_open_star tt (v:real^N) SUBSET N` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `{}:real^N->bool`; `v:real^N`]
        MOI_S4K_OPEN_STAR_FACTS) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      MP_TAC(ISPECL [`top:(real^N)topology`; `N:real^N->bool`] INTERIOR_OF_SUBSET) THEN
      UNDISCH_TAC `top interior_of N = UNIONS tt INTER (U:real^N->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (IMAGE (f1:real^N->real^3) (U INTER moi_sta_open_star tt v))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4K_STAR_IMAGE_OPEN_ON THEN
      MAP_EVERY EXISTS_TAC [`skeleton 1 (kk:(real^N->bool)->bool)`; `N:real^N->bool`] THEN
      ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX] THEN
      USE_THEN "inj" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (U INTER moi_sta_open_star tt v)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN top interior_of N` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[];
        UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET moi_sta_open_star tt v` THEN
        UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk v` THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) N`;
                   `IMAGE (f1:real^N->real^3) (U INTER moi_sta_open_star tt v)`]
      INTERIOR_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                                   (U INTER moi_sta_open_star tt v)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  ABBREV_TAC `y = (f1:real^N->real^3) x` THEN
  SUBGOAL_THEN `(x:real^N) IN N` ASSUME_TAC THENL
   [UNDISCH_TAC `(Bd:real^N->bool) SUBSET N` THEN
    UNDISCH_TAC `(x:real^N) IN Bd` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~((x:real^N) IN top interior_of N)` MP_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN Bd` THEN ASM_REWRITE_TAC[frontier_of] THEN SET_TAC[];
    REWRITE_TAC[]] THEN
  USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN N`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "vbf" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN (car:(real^N->bool)->real^3->bool) {v}` ASSUME_TAC THENL
   [USE_THEN "vbc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk v` THEN
    UNDISCH_TAC `(f1:real^N->real^3) x = y` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "lf" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q0 = {q:real^N->bool | q IN kk /\ ~(q = {}) /\
                    ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}` THEN
  ABBREV_TAC `W0 = {w:real^N | {w} IN Q0}` THEN
  SUBGOAL_THEN `FINITE (W0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. w IN W0 ==> {w} IN kk` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN EXPAND_TAC "Q0" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `M = UNIONS (IMAGE (moi_s34_vb tt (kk:(real^N->bool)->bool)) W0)` THEN
  SUBGOAL_THEN `compact (M:real^N->bool) /\ M SUBSET N` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN W0` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN EXPAND_TAC "Q0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    UNDISCH_TAC `(y:real^3) IN (car:(real^N->bool)->real^3->bool) {v}` THEN
    UNDISCH_TAC `(y:real^3) IN u0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) N INTER u0 SUBSET IMAGE f1 M` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `x':real^N` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cov" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x':real^N) IN N`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W0" THEN EXPAND_TAC "Q0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    USE_THEN "vbc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{w:real^N} IN kk`))) THEN
    UNDISCH_TAC `(x':real^N) IN moi_s34_vb tt kk w` THEN
    UNDISCH_TAC `(z:real^3) IN u0` THEN UNDISCH_TAC `(z:real^3) = f1 (x':real^N)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real^N->bool`; `f1:real^N->real^3`;
                 `IMAGE (f1:real^N->real^3) M`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `N:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N`)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  UNDISCH_TAC `(y:real^3) IN interior (IMAGE (f1:real^N->real^3) N)` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B2 = {z | z IN ball(y,e) INTER u0 /\ (g:real^3->real^N) z IN O1}` THEN
  SUBGOAL_THEN `ball(y:real^3,e) INTER u0 SUBSET IMAGE (f1:real^N->real^3) M`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f1:real^N->real^3) N INTER u0 SUBSET IMAGE f1 M` THEN
    UNDISCH_TAC `ball(y:real^3,e) SUBSET IMAGE (f1:real^N->real^3) N` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (B2:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B2" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) M` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^N) y = x` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!x. x IN M ==> (g:real^3->real^N) ((f1:real^N->real^3) x) = x`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN B2` ASSUME_TAC THENL
   [EXPAND_TAC "B2" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; CENTRE_IN_BALL] THEN
    UNDISCH_TAC `moi_sta_open_star tt (v:real^N) = UNIONS tt INTER O1` THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET moi_sta_open_star tt v` THEN
    UNDISCH_TAC `(x:real^N) IN moi_s34_vb tt kk v` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B2:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) M` ASSUME_TAC THENL
   [EXPAND_TAC "B2" THEN
    UNDISCH_TAC `ball(y:real^3,e) INTER u0 SUBSET IMAGE (f1:real^N->real^3) M` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (g:real^3->real^N) B2)` ASSUME_TAC THENL
   [EXPAND_TAC "top" THEN MATCH_MP_TAC MOI_S4K_STAR_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC [`skeleton 1 (kk:(real^N->bool)->bool)`; `v:real^N`] THEN
    ASM_REWRITE_TAC[MOI_S4K_SKEL_VERTEX] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) M` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`z1:real^3`; `z2:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f1:real^N->real^3) ((g:real^3->real^N) z1) = z1 /\
                    f1 (g z2) = z2` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
          `!y. y IN IMAGE (f1:real^N->real^3) M ==> f1 ((g:real^3->real^N) y) = y`)) THEN
        UNDISCH_TAC `(B2:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) M` THEN
        ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      UNDISCH_TAC `moi_sta_open_star tt (v:real^N) = UNIONS tt INTER O1` THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^N) (IMAGE (f1:real^N->real^3) M) = M` THEN
      UNDISCH_TAC `(B2:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) M` THEN
      UNDISCH_TAC `(M:real^N->bool) SUBSET N` THEN
      UNDISCH_TAC `(N:real^N->bool) SUBSET UNIONS tt` THEN
      EXPAND_TAC "B2" THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:(real^N)topology`; `N:real^N->bool`;
                 `IMAGE (g:real^3->real^N) B2`] INTERIOR_OF_MAXIMAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^N) (IMAGE (f1:real^N->real^3) M) = M` THEN
    UNDISCH_TAC `(B2:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) M` THEN
    UNDISCH_TAC `(M:real^N->bool) SUBSET N` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(g:real^3->real^N) y = x` THEN UNDISCH_TAC `(y:real^3) IN B2` THEN
  SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Face tori: N_s inside N, a polyhedron, Bd s in the graph; clause         *)
(* (10) from the foundation MOI_FND_SOLID_TORUS_TRIANGLE, the avoidance of  *)
(* the other vertex balls near h(s) (MOI_S4Q_AVOID_VB) and SHELL.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_PL_POLYHEDRON_UNIONS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!x. x IN f ==> pl_polyhedron x) ==> pl_polyhedron (UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_SIMP_TAC[]]);;

let MOI_S4K_FT_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> moi_s34_ft tt kk s SUBSET moi_s34_nb tt kk /\
         pl_polyhedron (moi_s34_ft tt kk s) /\
         relative_frontier s SUBSET UNIONS (skeleton 1 kk) /\
         (!e. e face_of s /\ aff_dim e = &1 ==> e IN skeleton 1 kk) /\
         s IN kk /\ s IN tt /\ aff_dim s = &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e face_of s /\ aff_dim e = &1 ==> e IN skeleton 1 kk`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[skeleton; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      concl th = `!s f. s IN kk /\ f face_of s ==> f IN (kk:(real^N->bool)->bool)`)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_ft; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4K_VB_CELL) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[moi_s34_ft] THEN MATCH_MP_TAC MOI_S4K_PL_POLYHEDRON_UNIONS THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{w:real^N | {w} IN tt /\ w IN s}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4K_SIMPLEX_VERTS_FINITE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S4K_CELL_POLY THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
        MOI_S4K_VB_CELL) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    SUBGOAL_THEN `polyhedron (s:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
      UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `f:real^N->bool` THEN
    REWRITE_TAC[facet_of] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!(x:real^N->bool) c. x IN c ==> x SUBSET UNIONS c`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
      `!e:real^N->bool. e face_of s /\ aff_dim e = &1 ==> e IN skeleton 1 kk`)) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_S4K_TORUS_CLAUSE = prove
 (mk_imp(MOI_FND_SOLID_TORUS_TRIANGLE,
   `!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) (f1:real^N->real^3)
     (car:(real^N->bool)->real^3->bool) s w0.
      moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
      pl_map_on (moi_s34_nb tt kk) f1 /\
      (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
      IMAGE h (UNIONS (skeleton 1 kk)) SUBSET interior (IMAGE f1 (moi_s34_nb tt kk)) /\
      (!q. q IN kk /\ ~(q = {}) ==> IMAGE h q SUBSET car q) /\
      (!v. {v} IN kk
           ==> IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v} /\
               pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v))) /\
      (!v q. {v} IN kk /\ q IN kk /\ ~(v IN q) ==> DISJOINT (car {v}) (IMAGE h q)) /\
      (!y. y IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
           ==> ?u. open u /\ y IN u /\
                   FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})}) /\
      s IN moi_s34_simp kk (&2) /\
      IMAGE f1 (moi_s34_ft tt kk s) SUBSET IMAGE h w0 /\
      (!f':real^N->real^3.
         moi_s34_emb f' (moi_s34_ft tt kk s) /\
         IMAGE f' (moi_s34_ft tt kk s) SUBSET IMAGE h w0 /\
         IMAGE h (relative_frontier s) SUBSET interior (IMAGE f' (moi_s34_ft tt kk s))
         ==> loops_carried (IMAGE h (relative_frontier s)) (IMAGE f' (moi_s34_ft tt kk s)))
      ==> pl_solid_torus (IMAGE f1 (moi_s34_ft tt kk s)) /\
          IMAGE h (relative_frontier s) SUBSET interior (IMAGE f1 (moi_s34_ft tt kk s)) /\
          loops_carried (IMAGE h (relative_frontier s)) (IMAGE f1 (moi_s34_ft tt kk s))`),
  DISCH_THEN(LABEL_TAC "sttri") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hq")
    (CONJUNCTS_THEN2 (LABEL_TAC "vb") (CONJUNCTS_THEN2 (LABEL_TAC "dis")
    (CONJUNCTS_THEN2 (LABEL_TAC "lf") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shell")))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4K_FT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_solid_torus (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4K_SOLID_TORUS_IMAGE THEN
    EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sttri" (MP_TAC o SPECL [`tt:(real^N->bool)->bool`;
      `skeleton 1 (kk:(real^N->bool)->bool)`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[moi_s34_ft; moi_s34_vb; MOI_S4K_SKEL_VERTEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4Q_AVOID_VB) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "hq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "avw"))))] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
                interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) INTER w SUBSET
                  IMAGE f1 (moi_s34_ft tt kk s)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
        MOI_S4K_NB_UNION_CELLS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2
        ASSUME_TAC (X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) ASSUME_TAC) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[moi_s34_ft] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN
      CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[]] THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(v:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "avw" (fun th -> MP_TAC(MP (SPEC `v:real^N` th)
        (CONJ (ASSUME `{v:real^N} IN kk`) (ASSUME `~((v:real^N) IN s)`)))) THEN
      MATCH_MP_TAC(SET_RULE
       `!(w:real^3->bool) a z. z IN w /\ z IN a ==> DISJOINT w a ==> F`) THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) INTER w` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (h:real^N->real^3) (UNIONS (skeleton 1 kk))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (h:real^N->real^3) s` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
        UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) INTER w SUBSET
                   IMAGE f1 (moi_s34_ft tt kk s)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "shell" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s34_emb] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    UNDISCH_TAC `moi_s34_ft tt kk s SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\
                       (f1:real^N->real^3) x = f1 y ==> x = y` THEN
    SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The open sets handed to graph_approximable, and FRAME_FND.                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4K_W_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) d
    (w0:(real^N->bool)->real^N->bool) v.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ {v} IN kk /\
     (!r. r IN moi_s34_simp kk (&3) ==> &0 < d r) /\
     (!s. s IN moi_s34_simp kk (&2)
          ==> open (IMAGE h (w0 s)) /\ moi_s34_ft tt kk s SUBSET w0 s)
     ==> open (moi_s4k_car tt kk h d {v} INTER
               INTERS {IMAGE h (w0 s) | s | s IN moi_s34_simp kk (&2) /\ v IN s}) /\
         IMAGE h (moi_s34_vb tt kk v) SUBSET
         moi_s4k_car tt kk h d {v} INTER
         INTERS {IMAGE h (w0 s) | s | s IN moi_s34_simp kk (&2) /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `d:(real^N->bool)->real`; `{v:real^N}`]
        MOI_S4K_CAR_BASIC) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN SIMP_TAC[];
      MATCH_MP_TAC OPEN_INTERS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S4K_COFACES_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
          EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[IN_SING] THEN
          UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
          UNDISCH_TAC `{v:real^N} IN kk` THEN SET_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN
          UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[]];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[]]];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4K_CAR_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s34_ft tt kk (s:real^N->bool)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_s34_ft; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]]);;

let FRAME_FND = prove
 (mk_imp(MOI_FND_SOLID_TORUS_TRIANGLE,MOI_S34_FRAME),
  DISCH_THEN(LABEL_TAC "sttri") THEN
  DISCH_THEN(LABEL_TAC "shell") THEN DISCH_THEN(LABEL_TAC "margin") THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4K_TUBE_FACTS) THEN
  SUBGOAL_THEN
   `?d:(real^N->bool)->real.
      !r. r IN moi_s34_simp kk (&3)
          ==> &0 < d r /\
              !w. {w} IN kk /\ ~(w IN r)
                  ==> (h:real^N->real^3) w IN
                      outside {y | ?x. x IN r UNION moi_s34_ft tt kk r /\
                                       dist(y,h x) <= d r}`
  (X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "dd")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "margin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w0:(real^N->bool)->real^N->bool.
      !s. s IN moi_s34_simp kk (&2)
          ==> w0 s SUBSET UNIONS tt /\ moi_s34_ft tt kk s SUBSET w0 s /\
              open (IMAGE (h:real^N->real^3) (w0 s)) /\
              !f':real^N->real^3.
                moi_s34_emb f' (moi_s34_ft tt kk s) /\
                IMAGE f' (moi_s34_ft tt kk s) SUBSET IMAGE h (w0 s) /\
                IMAGE h (relative_frontier s) SUBSET
                interior (IMAGE f' (moi_s34_ft tt kk s))
                ==> loops_carried (IMAGE h (relative_frontier s))
                                  (IMAGE f' (moi_s34_ft tt kk s))`
  (X_CHOOSE_THEN `w0:(real^N->bool)->real^N->bool` (LABEL_TAC "ww")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "shell" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN moi_s34_simp kk (&3) ==> &0 < (d:(real^N->bool)->real) r`
  ASSUME_TAC THENL [USE_THEN "dd" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  MP_TAC(ISPEC
   `\v:real^N. moi_s4k_car tt kk (h:real^N->real^3) d {v} INTER
               INTERS {IMAGE h ((w0:(real^N->bool)->real^N->bool) s) | s |
                       s IN moi_s34_simp kk (&2) /\ v IN s}`
   (REWRITE_RULE[graph_approximable]
     (ASSUME `graph_approximable tt (skeleton 1 (kk:(real^N->bool)->bool))
                                 (h:real^N->real^3)`))) THEN
  REWRITE_TAC[MOI_S4K_SKEL_VERTEX; GSYM moi_s34_vb; GSYM moi_s34_nb] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4K_W_FACTS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ww" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw"))))) THEN
  ABBREV_TAC `car = moi_s4k_car tt kk (h:real^N->real^3) d` THEN
  SUBGOAL_THEN `!v:real^N. {v} IN kk
                ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v} /\
                    !s. s IN moi_s34_simp kk (&2) /\ v IN s
                        ==> IMAGE f1 (moi_s34_vb tt kk v) SUBSET
                            IMAGE h ((w0:(real^N->bool)->real^N->bool) s)`
  (LABEL_TAC "fv") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "fw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    REWRITE_TAC[SUBSET_INTER; SUBSET_INTERS; FORALL_IN_GSPEC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN UNIONS {(car:(real^N->bool)->real^3->bool) q | q |
                                 q IN kk /\ ~(q = {})}
                    ==> ?u. open u /\ y IN u /\
                            FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})}`
  (LABEL_TAC "lf") THENL
   [EXPAND_TAC "car" THEN MATCH_MP_TAC MOI_S4K_CAR_LF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN kk
                ==> pl_ball 3 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
                    frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
                    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                    UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                            g IN moi_s34_simp kk (&1) /\ v IN g}`
  (LABEL_TAC "vimg") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN MP_TAC(ISPECL [`tt:(real^N->bool)->bool`;
      `kk:(real^N->bool)->bool`; `f1:real^N->real^3`; `v:real^N`] MOI_S4K_VB_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `f1:real^N->real^3` THEN
  EXISTS_TAC `car:(real^N->bool)->real^3->bool` THEN
  REWRITE_TAC[moi_s34_frame] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4K_TUBE_FRONTIER THEN
    EXISTS_TAC `car:(real^N->bool)->real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "fv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    SIMP_TAC[];
    X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN EXPAND_TAC "car" THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `d:(real^N->bool)->real`; `q:real^N->bool`]
      MOI_S4K_CAR_BASIC) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN EXPAND_TAC "car" THEN MATCH_MP_TAC MOI_S4K_CAR_MONO THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "fv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    USE_THEN "vimg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "car" THEN
    MATCH_MP_TAC MOI_S4K_CAR_CELL THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4K_SD_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN EXPAND_TAC "car" THEN MATCH_MP_TAC MOI_S4K_CAR_DISJOINT THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `f1:real^N->real^3`;
                  `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                  `(w0:(real^N->bool)->real^N->bool) s`]
      (MP MOI_S4K_TORUS_CLAUSE (ASSUME MOI_FND_SOLID_TORUS_TRIANGLE))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ww" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN EXPAND_TAC "car" THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `d:(real^N->bool)->real`; `q:real^N->bool`]
        MOI_S4K_CAR_BASIC) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "fv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
      USE_THEN "vimg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THEN EXPAND_TAC "car" THEN
      MATCH_MP_TAC MOI_S4K_CAR_DISJOINT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_s34_ft; IMAGE_UNIONS; UNIONS_SUBSET; FORALL_IN_IMAGE;
                  FORALL_IN_GSPEC] THEN
      X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      USE_THEN "fv" (fun th -> MP_TAC(MATCH_MP th (ASSUME `{v:real^N} IN kk`))) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN EXPAND_TAC "car" THEN MATCH_MP_TAC MOI_S4K_CAR_OUTSIDE THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dd" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(r:real^N->bool) IN moi_s34_simp kk (&3)`))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4K_CAR_SMALL THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `d:(real^N->bool)->real`; `q:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

