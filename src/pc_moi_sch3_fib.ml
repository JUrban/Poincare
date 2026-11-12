(* ========================================================================= *)
(* pc_moi_sch3_fib: the theorem SADDLE_FREE_FIBRED, proving the statement    *)
(* MOI_SCH3_SADDLE_FREE_FIBRED: a triangulated PL 2-sphere in real^3 with a  *)
(* generic height and no saddle (every vertex has at most two link edges     *)
(* crossing its level) is fibred by its levels.                              *)
(* Moise GTM 47, Sec 17, Lemmas 2-3 (p.123) and the paragraph after them:    *)
(* the extreme levels meet the sphere in single vertices (Lemma 2); each     *)
(* level in between meets it in one polygon (Lemma 3: components of the      *)
(* parts below a level merge only at critical points, here an induction over *)
(* the vertices of the edge graph; the polygon splits the sphere into two    *)
(* disks containing the parts below and above it); the bounded component is  *)
(* the union of the plane 2-cells bounded by these polygons.                 *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_cvx.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_sch3_lev.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Simplices of a complex: vertices, edges, lowest and highest vertices. *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_EXTREME_VERTEX = prove
 (`!c s (x:real^3). simplicial_complex c /\ s IN c /\ x extreme_point_of s
                    ==> {x} IN c`,
  REWRITE_TAC[GSYM FACE_OF_SING] THEN MESON_TAC[simplicial_complex]);;

let MOI_SFB_SEG_VERTICES = prove
 (`!c (y:real^3) z. simplicial_complex c /\ segment[y,z] IN c
                    ==> {y} IN c /\ {z} IN c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFB_EXTREME_VERTEX THEN
  EXISTS_TAC `segment[y:real^3,z]` THEN
  ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT]);;

let MOI_SFB_EDGE_IN = prove
 (`!c s (u:real^3) w. simplicial_complex c /\ s IN c /\ {u} IN c /\ {w} IN c /\
                      u IN s /\ w IN s ==> segment[u,w] IN c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^3) IN V /\ (w:real^3) IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_VERTEX_EXTREME]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^3,w] face_of s` MP_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{u:real^3,w}` THEN ASM SET_TAC[];
    ASM_MESON_TAC[simplicial_complex]]);;

let MOI_SFB_LOWER_VERTEX = prove
 (`!c s (a:real^3) x. simplicial_complex c /\ s IN c /\ x IN s
                      ==> ?w. {w} IN c /\ w IN s /\ a dot w <= a dot x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `?w:real^3. w IN V /\ a dot w <= a dot x` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE]) THEN
    SUBGOAL_THEN `convex hull V SUBSET {y:real^3 | a dot y > a dot x}` MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    EXISTS_TAC `w:real^3` THEN ASM_SIMP_TAC[HULL_INC] THEN
    MATCH_MP_TAC MOI_SFB_EXTREME_VERTEX THEN
    EXISTS_TAC `convex hull V:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_SFB_MIN_FACE = prove
 (`!c (a:real^3) s x.
     moi_sch3_generic c a /\ s IN c /\ x IN s /\
     (!y. y IN s ==> a dot x <= a dot y)
     ==> {x} IN c`,
  REWRITE_TAC[moi_sch3_generic] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = (s:real^3->bool) INTER {y | a dot y = a dot x}` THEN
  SUBGOAL_THEN `(f:real^3->bool) face_of s` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
    ASM_SIMP_TAC[real_ge] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN f` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `f:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w:real^3. w IN W ==> {w} IN c /\ a dot w = a dot x`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SFB_EXTREME_VERTEX THEN EXISTS_TAC `f:real^3->bool` THEN
      ASM_MESON_TAC[];
      SUBGOAL_THEN `(w:real^3) IN f` MP_TAC THENL
       [ASM_MESON_TAC[HULL_INC];
        EXPAND_TAC "f" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w0:real^3. w0 IN W` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^3) IN f` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `W = {w0:real^3}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SING] THEN X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN f` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]);;

let MOI_SFB_GENERIC_NEG = prove
 (`!c (a:real^3). moi_sch3_generic c a ==> moi_sch3_generic c (--a)`,
  REWRITE_TAC[moi_sch3_generic; DOT_LNEG; REAL_EQ_NEG2; VECTOR_NEG_EQ_0] THEN
  MESON_TAC[]);;

let MOI_SFB_MAX_FACE = prove
 (`!c (a:real^3) s x.
     moi_sch3_generic c a /\ s IN c /\ x IN s /\
     (!y. y IN s ==> a dot y <= a dot x)
     ==> {x} IN c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFB_MIN_FACE THEN
  MAP_EVERY EXISTS_TAC [`--a:real^3`; `s:real^3->bool`] THEN
  ASM_SIMP_TAC[MOI_SFB_GENERIC_NEG; DOT_LNEG; REAL_LE_NEG2]);;

let MOI_SFB_LOWER_STRICT = prove
 (`!c (a:real^3) s x.
     moi_sch3_generic c a /\ s IN c /\ x IN s /\ ~({x} IN c)
     ==> ?w. {w} IN c /\ w IN s /\ a dot w < a dot x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  UNDISCH_TAC `~({x:real^3} IN c)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SFB_MIN_FACE THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `convex hull V:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull V SUBSET {y:real^3 | a dot y >= a dot x}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `{w:real^3} IN c /\ w IN convex hull V` MP_TAC THENL
     [ASM_SIMP_TAC[HULL_INC] THEN MATCH_MP_TAC MOI_SFB_EXTREME_VERTEX THEN
      EXISTS_TAC `convex hull V:real^3->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge]]);;

let MOI_SFB_UPPER_STRICT = prove
 (`!c (a:real^3) s x.
     moi_sch3_generic c a /\ s IN c /\ x IN s /\ ~({x} IN c)
     ==> ?w. {w} IN c /\ w IN s /\ a dot x < a dot w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `--a:real^3`; `s:real^3->bool`; `x:real^3`]
    MOI_SFB_LOWER_STRICT) THEN
  ASM_SIMP_TAC[MOI_SFB_GENERIC_NEG; DOT_LNEG; REAL_LT_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* 2. Moise Lemma 2: the lowest and the highest level meet the sphere in    *)
(* single vertices.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_SPHERE_FACTS = prove
 (`!c:(real^3->bool)->bool.
     pl_sphere 2 (UNIONS c)
     ==> UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\ compact (UNIONS c) /\
         connected (UNIONS c) /\ ~(UNIONS c = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE];
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`] CONNECTED_SPHERE) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS];
    ASM_MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY]]);;

let MOI_SFB_MIN_POINT = prove
 (`!c (a:real^3) x.
     moi_sch3_generic c a /\ x IN UNIONS c /\
     (!y. y IN UNIONS c ==> a dot x <= a dot y)
     ==> {x} IN c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SFB_MIN_FACE THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `t:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SFB_MAX_POINT = prove
 (`!c (a:real^3) x.
     moi_sch3_generic c a /\ x IN UNIONS c /\
     (!y. y IN UNIONS c ==> a dot y <= a dot x)
     ==> {x} IN c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SFB_MAX_FACE THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `t:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SFB_EXTREMES = prove
 (`!c (a:real^3).
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c)
     ==> ?p q. {p} IN c /\ {q} IN c /\ a dot p < a dot q /\
               (!x. x IN UNIONS c ==> a dot p <= a dot x /\ a dot x <= a dot q) /\
               UNIONS c INTER {x | a dot x = a dot p} = {p} /\
               UNIONS c INTER {x | a dot x = a dot q} = {q}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  MP_TAC(ISPECL [`\x:real^3. a dot x`; `UNIONS c:real^3->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`\x:real^3. a dot x`; `UNIONS c:real^3->bool`]
    CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{p:real^3} IN c /\ {q:real^3} IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SFB_MIN_POINT; MATCH_MP_TAC MOI_SFB_MAX_POINT] THEN
    EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN UNIONS c /\ a dot x = a dot p ==> x = p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^3} IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SFB_MIN_POINT THEN EXISTS_TAC `a:real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN UNIONS c /\ a dot x = a dot q ==> x = q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^3} IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SFB_MAX_POINT THEN EXISTS_TAC `a:real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `UNIONS c:real^3->bool` MOI_SCD_NOT_PL_SPHERE_FINITE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:real^3}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `a dot (x:real^3) = a dot p` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `a dot p <= a dot (x:real^3) /\ a dot x <= a dot q` MP_TAC THENL
     [ASM_MESON_TAC[]; UNDISCH_TAC `a dot p = a dot (q:real^3)` THEN REAL_ARITH_TAC];
    ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Paths in the edge graph (a reflexive transitive closure) and the      *)
(* connectedness of the edge graph of a complex with connected polyhedron.  *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_RTC_RULES,MOI_SFB_RTC_INDUCT,MOI_SFB_RTC_CASES =
  new_inductive_definition
 `(!x. moi_sfb_rtc (R:real^3->real^3->bool) x x) /\
  (!x y z. moi_sfb_rtc R x y /\ R y z ==> moi_sfb_rtc R x z)`;;

let MOI_SFB_RTC_REFL = prove
 (`!R (x:real^3). moi_sfb_rtc R x x`,
  MESON_TAC[MOI_SFB_RTC_RULES]);;

let MOI_SFB_RTC_STEP = prove
 (`!R (x:real^3) y z. moi_sfb_rtc R x y /\ R y z ==> moi_sfb_rtc R x z`,
  MESON_TAC[MOI_SFB_RTC_RULES]);;

let MOI_SFB_RTC_INC = prove
 (`!R (x:real^3) y. R x y ==> moi_sfb_rtc R x y`,
  MESON_TAC[MOI_SFB_RTC_RULES]);;

let MOI_SFB_RTC_TRANS = prove
 (`!R (x:real^3) y z.
     moi_sfb_rtc R x y /\ moi_sfb_rtc R y z ==> moi_sfb_rtc R x z`,
  SUBGOAL_THEN
   `!R (y:real^3) z. moi_sfb_rtc R y z
                     ==> !x. moi_sfb_rtc R x y ==> moi_sfb_rtc R x z`
   (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC MOI_SFB_RTC_INDUCT THEN MESON_TAC[MOI_SFB_RTC_RULES]);;

let MOI_SFB_RTC_MONO = prove
 (`!R R' (x:real^3) y.
     (!x y. R x y ==> R' x y) /\ moi_sfb_rtc R x y ==> moi_sfb_rtc R' x y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`y:real^3`,`y:real^3`) THEN SPEC_TAC(`x:real^3`,`x:real^3`) THEN
  MATCH_MP_TAC MOI_SFB_RTC_INDUCT THEN ASM_MESON_TAC[MOI_SFB_RTC_RULES]);;

let MOI_SFB_RTC_SYM = prove
 (`!R (x:real^3) y.
     (!x y. R x y ==> R y x) /\ moi_sfb_rtc R x y ==> moi_sfb_rtc R y x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`y:real^3`,`y:real^3`) THEN SPEC_TAC(`x:real^3`,`x:real^3`) THEN
  MATCH_MP_TAC MOI_SFB_RTC_INDUCT THEN
  ASM_MESON_TAC[MOI_SFB_RTC_RULES; MOI_SFB_RTC_TRANS; MOI_SFB_RTC_INC]);;

let MOI_SFB_RTC_LAST = prove
 (`!R (x:real^3) y.
     moi_sfb_rtc R x y /\ ~(x = y) ==> ?z. moi_sfb_rtc R x z /\ R z y`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `moi_sfb_rtc R (x:real^3) y` THEN
  GEN_REWRITE_TAC LAND_CONV [MOI_SFB_RTC_CASES] THEN ASM_MESON_TAC[]);;

(* Edges of the complex c between vertices satisfying P.                    *)

let moi_sfb_edge = new_definition
 `moi_sfb_edge (c:(real^3->bool)->bool) (P:real^3->bool) (y:real^3) z <=>
    segment[y,z] IN c /\ ~(y = z) /\ P y /\ P z`;;

let MOI_SFB_EDGE_SYM = prove
 (`!c P (y:real^3) z. moi_sfb_edge c P y z ==> moi_sfb_edge c P z y`,
  REWRITE_TAC[moi_sfb_edge] THEN MESON_TAC[SEGMENT_SYM]);;

let MOI_SFB_EDGE_RTC_SYM = prove
 (`!c P (y:real^3) z.
     moi_sfb_rtc (moi_sfb_edge c P) y z ==> moi_sfb_rtc (moi_sfb_edge c P) z y`,
  MESON_TAC[MOI_SFB_RTC_SYM; MOI_SFB_EDGE_SYM]);;

let MOI_SFB_COMMON_VERTEX = prove
 (`!c t1 t2 (x:real^3).
     simplicial_complex c /\ t1 IN c /\ t2 IN c /\ x IN t1 /\ x IN t2
     ==> ?z. {z} IN c /\ z IN t1 /\ z IN t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1 INTER t2:real^3->bool`]
    MOI_SCF_SC_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_INTER] THEN MESON_TAC[]]);;

let MOI_SFB_GRAPH_CONNECTED = prove
 (`!c (u:real^3) w.
     simplicial_complex c /\ connected (UNIONS c) /\ {u} IN c /\ {w} IN c
     ==> moi_sfb_rtc (moi_sfb_edge c (\x. T)) u w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `kk = {v:real^3 | {v} IN c /\ moi_sfb_rtc (moi_sfb_edge c (\x. T)) u v}` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN kk ==> {y} IN c` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN kk /\ ~((w:real^3) IN kk)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[IN_ELIM_THM; MOI_SFB_RTC_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!y z:real^3. y IN kk /\ segment[y,z] IN c ==> z IN kk`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SFB_SEG_VERTICES]; ALL_TAC] THEN
    ASM_CASES_TAC `z:real^3 = y` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SFB_RTC_STEP THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[moi_sfb_edge] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y z:real^3. t IN c /\ y IN kk /\ y IN t /\ {z} IN c /\ z IN t ==> z IN kk`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `z:real^3 = y` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[y:real^3,z] IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SFB_EDGE_IN THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `A = UNIONS {t:real^3->bool | t IN c /\ ?v. v IN kk /\ v IN t}` THEN
  ABBREV_TAC
   `B = UNIONS {t:real^3->bool | t IN c /\ ?v. {v} IN c /\ ~(v IN kk) /\ v IN t}` THEN
  SUBGOAL_THEN `!x:real^3. x IN A /\ x IN B ==> F` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `t1:real^3->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `t2:real^3->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1:real^3->bool`; `t2:real^3->bool`;
                   `x:real^3`] MOI_SFB_COMMON_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN kk` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (UNIONS c:real^3->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; MOI_SCF_SC_FINITE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_SCF_SC_CLOSED];
    EXPAND_TAC "B" THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; MOI_SCF_SC_FINITE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_SCF_SC_CLOSED];
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SCF_SC_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(v:real^3) IN kk` THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `u:real^3` THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `{u:real^3}` THEN ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[IN_SING];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `w:real^3` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `{w:real^3}` THEN ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[IN_SING]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The cycle of link vertices at a vertex of a triangulated 2-sphere and *)
(* the lower link of a vertex with at most two crossing link edges.         *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_PERIODIC_MOD = prove
 (`!(f:num->A) n. ~(n = 0) /\ (!i. f(i + n) = f i) ==> !i. f(i MOD n) = f i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q r. (f:num->A)(q * n + r) = f r` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(q * n + n) + r = (q * n + r) + n:num`] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP DIVISION) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SFB_MOD_WINDOW = prove
 (`!n i j. ~(n = 0) /\ i < j /\ j < i + n ==> ~(i MOD n = j MOD n)`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `i DIV n < j DIV n \/ j DIV n <= i DIV n`) THENL
   [SUBGOAL_THEN `SUC(i DIV n) * n <= j DIV n * n` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES]];
    SUBGOAL_THEN `j DIV n * n <= i DIV n * n` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_RCANCEL]; ALL_TAC]] THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN
  MP_TAC(SPECL [`j:num`; `n:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOI_SFB_WINDOW_INJ = prove
 (`!(f:num->A) n.
     ~(n = 0) /\ (!i. f(i + n) = f i) /\
     (!i j. i < n /\ j < n /\ f i = f j ==> i = j)
     ==> !i j. i < j /\ j < i + n ==> ~(f i = f j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->A`; `n:num`] MOI_SFB_PERIODIC_MOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `i:num`; `j:num`] MOI_SFB_MOD_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOD_LT_EQ]);;

let MOI_SFB_PAIR_EQ = prove
 (`!v x y:real^3. {v,x} = {v,y} /\ ~(x = v) ==> x = y`,
  SET_TAC[]);;

let MOI_SFB_TRIPLE_EQ = prove
 (`!v x z y1 y2:real^3.
     x IN {v,y1,y2} /\ z IN {v,y1,y2} /\ ~(x = v) /\ ~(z = v) /\ ~(x = z)
     ==> {v,x,z} = {v,y1,y2}`,
  SET_TAC[]);;

let MOI_SFB_CYCLE_M = prove
 (`!c (v:real^3) (S:num->real^3->bool).
     simplicial_complex c /\ {v} IN c /\
     (!i. S i IN c /\ aff_dim(S i) = &2 /\ v IN S i /\
          aff_dim(S i INTER S(SUC i)) = &1)
     ==> ?m. !i. ~(m i = v) /\ S i INTER S(SUC i) = segment[v,m i]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `SUC i`) THEN
  ABBREV_TAC `e = (S:num->real^3->bool) i INTER S(SUC i)` THEN
  SUBGOAL_THEN `(e:real^3->bool) face_of (S:num->real^3->bool) i /\ v IN e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `(S:num->real^3->bool) i`; `v:real^3`]
    MOI_SCF_TRIANGLE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`v:real^3`; `y1:real^3`; `y2:real^3`; `e:real^3->bool`]
    MOI_SCF_EDGE_AT_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN STRIP_TAC THENL
     [EXISTS_TAC `y1:real^3` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y2:real^3` THEN ASM_REWRITE_TAC[]]]);;

let MOI_SFB_CYCLE = prove
 (`!c (v:real^3).
     simplicial_complex c /\ UNIONS c homeomorphic sphere(vec 0:real^3,&1) /\
     {v} IN c
     ==> ?n m. 3 <= n /\ (!i. m(i + n) = m i) /\
               (!i. ~(m i = v) /\ {m i} IN c /\ segment[v,m i] IN c /\
                    ~(m i = m(SUC i)) /\ segment[m i,m(SUC i)] IN c /\
                    segment[m i,m(SUC i)] IN simplicial_link c v) /\
               (!i j. i < j /\ j < i + n
                      ==> ~(segment[m i,m(SUC i)] = segment[m j,m(SUC j)])) /\
               (!y. segment[v,y] IN c /\ ~(y = v) ==> ?i. i < n /\ y = m i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`] MOI_SCF_SURF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per")
      (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "tri")
        (LABEL_TAC "all"))))))) THEN
  SUBGOAL_THEN `!i j. i < j /\ j < i + n ==> ~((S:num->real^3->bool) i = S j)`
  (LABEL_TAC "winj") THENL
   [MATCH_MP_TAC MOI_SFB_WINDOW_INJ THEN
    USE_THEN "per" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `S:num->real^3->bool`]
    MOI_SFB_CYCLE_M) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num->real^3` (LABEL_TAC "m")) THEN
  (* periodicity of m *)
  SUBGOAL_THEN `!i. (m:num->real^3)(i + n) = m i` (LABEL_TAC "mper") THENL
   [X_GEN_TAC `i:num` THEN
    USE_THEN "m" (MP_TAC o SPEC `i + n:num`) THEN
    USE_THEN "m" (MP_TAC o SPEC `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `SUC(i + n) = SUC i + n`] THEN
    USE_THEN "per" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `segment[v:real^3,(m:num->real^3)(i + n)] = segment[v,m i]` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[SEGMENT_EQ]] THEN
    ASM_MESON_TAC[MOI_SFB_PAIR_EQ];
    ALL_TAC] THEN
  (* the edges at v *)
  SUBGOAL_THEN `!i. segment[v:real^3,m i] IN c /\ {(m:num->real^3) i} IN c`
  (LABEL_TAC "medge") THENL
   [X_GEN_TAC `i:num` THEN
    SUBGOAL_THEN `segment[v:real^3,(m:num->real^3) i] IN c`
      (fun th -> ASM_MESON_TAC[th; MOI_SFB_SEG_VERTICES]) THEN
    USE_THEN "m" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(SPEC `i:num` th))]) THEN
    USE_THEN "tri" (fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `SUC i` th)) THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  (* consecutive link vertices are distinct *)
  SUBGOAL_THEN `!i. ~((m:num->real^3) i = m(SUC i))` (LABEL_TAC "mdist") THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `segment[v:real^3,(m:num->real^3) i]`;
                   `(S:num->real^3->bool) i`] MOI_SCF_SURF_OTHER_TRIANGLE) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `~(v:real^3 = (m:num->real^3) i) /\ segment[v,m i] SUBSET S i`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "m" (MP_TAC o SPEC `i:num`) THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      USE_THEN "medge" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "tri" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two")))))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(S:num->real^3->bool)(SUC i) = t' /\ S(SUC(SUC i)) = t'` MP_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "two" (MP_TAC o SPEC `(S:num->real^3->bool)(SUC i)`) THEN
        ANTS_TAC THENL
         [USE_THEN "tri" (fun th -> REWRITE_TAC[th]) THEN
          USE_THEN "m" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(SPEC `i:num` th))]) THEN
          REWRITE_TAC[INTER_SUBSET];
          USE_THEN "winj" (MP_TAC o SPECL [`i:num`; `SUC i`]) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]];
        USE_THEN "two" (MP_TAC o SPEC `(S:num->real^3->bool)(SUC(SUC i))`) THEN
        ANTS_TAC THENL
         [USE_THEN "tri" (fun th -> REWRITE_TAC[th]) THEN
          SUBGOAL_THEN `segment[v:real^3,(m:num->real^3) i] = S(SUC i) INTER S(SUC(SUC i))`
          SUBST1_TAC THENL
           [USE_THEN "m" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `SUC i` th)]) THEN
            ASM_REWRITE_TAC[];
            REWRITE_TAC[INTER_SUBSET]];
          USE_THEN "winj" (MP_TAC o SPECL [`i:num`; `SUC(SUC i)`]) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]]];
      USE_THEN "winj" (MP_TAC o SPECL [`SUC i`; `SUC(SUC i)`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]];
    ALL_TAC] THEN
  (* the triangle S(SUC i) has vertices v, m i, m(SUC i) *)
  SUBGOAL_THEN
   `!i. ~affine_dependent {v:real^3,m i,m(SUC i)} /\
        (S:num->real^3->bool)(SUC i) = convex hull {v,m i,m(SUC i)}`
  (LABEL_TAC "mtri") THENL
   [X_GEN_TAC `i:num` THEN
    USE_THEN "tri" (STRIP_ASSUME_TAC o SPEC `SUC i`) THEN
    SUBGOAL_THEN `(m:num->real^3) i IN S(SUC i) /\ m(SUC i) IN S(SUC i)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(m:num->real^3) i IN S i INTER S(SUC i)` MP_TAC THENL
         [USE_THEN "m" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `i:num` th)]) THEN
          REWRITE_TAC[ENDS_IN_SEGMENT];
          SIMP_TAC[IN_INTER]];
        SUBGOAL_THEN `(m:num->real^3)(SUC i) IN S(SUC i) INTER S(SUC(SUC i))`
        MP_TAC THENL
         [USE_THEN "m" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `SUC i` th)]) THEN
          REWRITE_TAC[ENDS_IN_SEGMENT];
          SIMP_TAC[IN_INTER]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `(S:num->real^3->bool)(SUC i)`;
                   `v:real^3`] MOI_SCF_TRIANGLE_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(S:num->real^3->bool)(SUC i)`)) THEN
    SUBGOAL_THEN `!x:real^3. {x} IN c /\ x IN convex hull {v,y1,y2}
                             ==> x IN {v,y1,y2}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`{v:real^3,y1,y2}`; `x:real^3`]
        EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{v:real^3,m i,m(SUC i)} = {v,y1,y2}`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_SFB_TRIPLE_EQ THEN
    USE_THEN "m" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `i:num` th);
                                        CONJUNCT1(SPEC `SUC i` th)]) THEN
    USE_THEN "mdist" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "medge" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the link edges *)
  SUBGOAL_THEN
   `!i. segment[(m:num->real^3) i,m(SUC i)] IN c /\
        segment[m i,m(SUC i)] IN simplicial_link c v`
  (LABEL_TAC "mlink") THENL
   [X_GEN_TAC `i:num` THEN
    USE_THEN "mtri" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    USE_THEN "tri" (STRIP_ASSUME_TAC o SPEC `SUC i`) THEN
    SUBGOAL_THEN `segment[(m:num->real^3) i,m(SUC i)] face_of S(SUC i)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{(m:num->real^3) i,m(SUC i)}` THEN REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[(m:num->real^3) i,m(SUC i)] IN c` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(v:real^3) extreme_point_of S(SUC i)` MP_TAC THENL
       [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[extreme_point_of] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`(m:num->real^3) i`; `(m:num->real^3)(SUC i)`]) THEN
        REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
        SUBGOAL_THEN `(m:num->real^3) i IN S(SUC i) /\ m(SUC i) IN S(SUC i)`
          (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
          REWRITE_TAC[IN_INSERT];
          ALL_TAC] THEN
        USE_THEN "m" (MP_TAC o SPEC `i:num`) THEN
        USE_THEN "m" (MP_TAC o SPEC `SUC i`) THEN ASM_MESON_TAC[]];
      EXISTS_TAC `(S:num->real^3->bool)(SUC i)` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* distinct positions in a window give distinct link edges *)
  SUBGOAL_THEN
   `!i j. i < j /\ j < i + n
          ==> ~(segment[(m:num->real^3) i,m(SUC i)] = segment[m j,m(SUC j)])`
  (LABEL_TAC "mwin") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SEGMENT_EQ] THEN DISCH_TAC THEN
    USE_THEN "winj" (MP_TAC o SPECL [`SUC i`; `SUC j`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "mtri" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `i:num` th);
                                           CONJUNCT2(SPEC `j:num` th)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* every neighbour of v is one of the m i *)
  SUBGOAL_THEN `!y:real^3. segment[v,y] IN c /\ ~(y = v) ==> ?i. i < n /\ y = (m:num->real^3) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `segment[v:real^3,y]`]
      MOI_SCF_SURF_PURE) THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "all" (MP_TAC o SPEC `t:real^3->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(S:num->real^3->bool) j = S(SUC(j + n - 1))` ASSUME_TAC THENL
     [SUBGOAL_THEN `SUC(j + n - 1) = j + n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; USE_THEN "per" (fun th -> REWRITE_TAC[th])];
      ALL_TAC] THEN
    SUBGOAL_THEN `{y:real^3} IN c /\ y IN S(SUC(j + n - 1))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[MOI_SFB_SEG_VERTICES]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    USE_THEN "mtri" (STRIP_ASSUME_TAC o SPEC `j + n - 1:num`) THEN
    USE_THEN "tri" (STRIP_ASSUME_TAC o SPEC `SUC(j + n - 1)`) THEN
    SUBGOAL_THEN `(y:real^3) IN {v,m(j + n - 1),m(SUC(j + n - 1))}` MP_TAC THENL
     [MP_TAC(ISPECL [`{v:real^3,m(j + n - 1),m(SUC(j + n - 1))}`; `y:real^3`]
        EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(S:num->real^3->bool)(SUC(j + n - 1))`)) THEN
      MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `(j + n - 1) MOD n` THEN
      MP_TAC(ISPECL [`m:num->real^3`; `n:num`] MOI_SFB_PERIODIC_MOD) THEN
      USE_THEN "mper" (fun th -> REWRITE_TAC[th]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      ASM_REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC;
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SUC(j + n - 1) = j + n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; USE_THEN "mper" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `m:num->real^3`] THEN ASM_REWRITE_TAC[]);;

(* Discrete intermediate values along a window of positions.                *)

let MOI_SFB_DIVT = prove
 (`!L:num->bool a d. L a /\ ~L(a + d) ==> ?k. a <= k /\ k < a + d /\ L k /\ ~L(SUC k)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[];
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(L:num->bool)(a + d)` THENL
     [EXISTS_TAC `a + d:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ARITH_RULE `k < a + d ==> k < SUC(a + d)`]]]);;

let MOI_SFB_WINDOW3 = prove
 (`!L:num->bool n i j.
     i <= j /\ j <= i + n /\ L i /\ L j /\ L(i + n)
     ==> (!k. i <= k /\ k <= j ==> L k) \/
         (!k. j <= k /\ k <= i + n ==> L k) \/
         ?k1 k2 k3. i <= k1 /\ k1 < k2 /\ k2 < k3 /\ k3 < i + n /\
                    (L k1 <=> ~L(SUC k1)) /\ (L k2 <=> ~L(SUC k2)) /\
                    (L k3 <=> ~L(SUC k3))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!k. i <= k /\ k <= j ==> (L:num->bool) k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `!k. j <= k /\ k <= i + n ==> (L:num->bool) k` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u1:num` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u0:num` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  MP_TAC(ISPECL [`L:num->bool`; `i:num`; `u0 - i:num`] MOI_SFB_DIVT) THEN
  ASM_SIMP_TAC[ARITH_RULE `i <= u0 ==> i + (u0 - i) = u0:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\k. ~(L:num->bool) k`; `u0:num`; `j - u0:num`] MOI_SFB_DIVT) THEN
  ASM_SIMP_TAC[ARITH_RULE `u0 <= j ==> u0 + (j - u0) = j:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:num->bool`; `j:num`; `u1 - j:num`] MOI_SFB_DIVT) THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= u1 ==> j + (u1 - j) = u1:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k1:num`; `k2:num`; `k3:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOI_SFB_WALK = prove
 (`!c P (m:num->real^3) i d.
     (!k. i <= k /\ k < i + d ==> moi_sfb_edge c P (m k) (m(SUC k)))
     ==> moi_sfb_rtc (moi_sfb_edge c P) (m i) (m(i + d))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; MOI_SFB_RTC_REFL];
    DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC MOI_SFB_RTC_STEP THEN
    EXISTS_TAC `(m:num->real^3)(i + d)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

let MOI_SFB_CROSS_CASES = prove
 (`!x y v:real. ((x < v) <=> ~(y < v)) /\ ~(x = v) /\ ~(y = v)
                ==> (x < v /\ v < y) \/ (y < v /\ v < x)`,
  REAL_ARITH_TAC);;

(* Any two lower neighbours of a vertex with at most two crossing link edges *)
(* are joined by a path of lower link vertices.                              *)

let MOI_SFB_LOWER_LINK = prove
 (`!c (a:real^3) v y z.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\ {v} IN c /\
     segment[v,y] IN c /\ ~(y = v) /\ a dot y < a dot v /\
     segment[v,z] IN c /\ ~(z = v) /\ a dot z < a dot v
     ==> moi_sfb_rtc (moi_sfb_edge c (\x. a dot x < a dot v)) y z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_saddle_free; moi_sch3_generic] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`] MOI_SFB_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `m:num->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mper")
      (CONJUNCTS_THEN2 (LABEL_TAC "mfacts") (CONJUNCTS_THEN2 (LABEL_TAC "mwin")
        (LABEL_TAC "nb"))))))) THEN
  SUBGOAL_THEN
   `!i j. i <= j /\ j < n /\ a dot ((m:num->real^3) i) < a dot v /\
          a dot ((m:num->real^3) j) < a dot v
          ==> moi_sfb_rtc (moi_sfb_edge c (\x. a dot x < a dot v)) (m i) (m j)`
  (LABEL_TAC "main") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\k. a dot ((m:num->real^3) k) < a dot v`; `n:num`; `i:num`; `j:num`]
      MOI_SFB_WINDOW3) THEN
    USE_THEN "mper" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `\x:real^3. a dot x < a dot v`;
                     `m:num->real^3`; `i:num`; `j - i:num`] MOI_SFB_WALK) THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= j ==> i + (j - i) = j:num`] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[moi_sfb_edge] THEN USE_THEN "mfacts" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC MOI_SFB_EDGE_RTC_SYM THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `\x:real^3. a dot x < a dot v`;
                     `m:num->real^3`; `j:num`; `i + n - j:num`] MOI_SFB_WALK) THEN
      ASM_SIMP_TAC[ARITH_RULE `j < n ==> j + (i + n - j) = i + n:num`] THEN
      USE_THEN "mper" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[moi_sfb_edge] THEN USE_THEN "mfacts" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    (* three crossing link edges contradict the saddle-free hypothesis *)
    SUBGOAL_THEN
     `!k. ((a dot ((m:num->real^3) k) < a dot v) <=> ~(a dot (m(SUC k)) < a dot v))
          ==> segment[m k,m(SUC k)] IN
              {e | e IN simplicial_link c v /\
                   ?x y. e = segment[x,y] /\ a dot x < a dot v /\ a dot v < a dot y}`
    (LABEL_TAC "cross") THENL
     [X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "tr") THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [USE_THEN "mfacts" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      SUBGOAL_THEN `~(a dot ((m:num->real^3) k) = a dot v) /\
                    ~(a dot ((m:num->real^3)(SUC k)) = a dot v)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "tr" (fun th -> MP_TAC(MATCH_MP MOI_SFB_CROSS_CASES
        (CONJ th (ASSUME `~(a dot ((m:num->real^3) k) = a dot v) /\
                          ~(a dot ((m:num->real^3)(SUC k)) = a dot v)`)))) THEN
      STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`(m:num->real^3) k`; `(m:num->real^3)(SUC k)`] THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`(m:num->real^3)(SUC k)`; `(m:num->real^3) k`] THEN
        ASM_REWRITE_TAC[SEGMENT_SYM]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(segment[(m:num->real^3) k1,m(SUC k1)] = segment[m k2,m(SUC k2)]) /\
      ~(segment[(m:num->real^3) k1,m(SUC k1)] = segment[m k3,m(SUC k3)]) /\
      ~(segment[(m:num->real^3) k2,m(SUC k2)] = segment[m k3,m(SUC k3)])`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "mwin" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `FINITE {e | e IN simplicial_link c v /\
                  ?x y. e = segment[x,y] /\ a dot x < a dot v /\ a dot v < a dot (y:real^3)}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; simplicial_link] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `3 <= moi_sch3_crossings c a v` MP_TAC THENL
     [REWRITE_TAC[moi_sch3_crossings] THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {segment[(m:num->real^3) k1,m(SUC k1)], segment[m k2,m(SUC k2)],
                        segment[m k3,m(SUC k3)]}` THEN
      CONJ_TAC THENL
       [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY] THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        REPEAT CONJ_TAC THEN USE_THEN "cross" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(MATCH_MP (SPEC `v:real^3` (ASSUME
        `!v:real^3. {v} IN c ==> moi_sch3_crossings c a v <= 2`))
        (ASSUME `{v:real^3} IN c`)) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "nb" (MP_TAC o C MATCH_MP (CONJ (ASSUME `segment[v:real^3,y] IN c`)
                                           (ASSUME `~(y:real^3 = v)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  USE_THEN "nb" (MP_TAC o C MATCH_MP (CONJ (ASSUME `segment[v:real^3,z] IN c`)
                                           (ASSUME `~(z:real^3 = v)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  DISJ_CASES_TAC(ARITH_RULE `i <= j \/ j <= i:num`) THENL
   [USE_THEN "main" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SFB_EDGE_RTC_SYM THEN USE_THEN "main" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Components of the parts below a level merge only at saddles: in the   *)
(* edge graph, two vertices are joined through vertices not higher than     *)
(* the higher of them (removal of the top vertex by its lower link, by       *)
(* induction on the number of vertices above that height).                  *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_KEY_STEP = prove
 (`!c (a:real^3) P xt.
     moi_sch3_generic c a /\ {xt} IN c /\ P xt /\
     (!y. {y} IN c /\ P y ==> a dot y <= a dot xt) /\
     (!y z. segment[xt,y] IN c /\ ~(y = xt) /\ a dot y < a dot xt /\
            segment[xt,z] IN c /\ ~(z = xt) /\ a dot z < a dot xt
            ==> moi_sfb_rtc (moi_sfb_edge c (\w. a dot w < a dot xt)) y z)
     ==> !u w. moi_sfb_rtc (moi_sfb_edge c P) u w /\ ~(u = xt) /\ ~(w = xt)
               ==> moi_sfb_rtc (moi_sfb_edge c (\w. a dot w < a dot xt)) u w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic])
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "top") (LABEL_TAC "g2"))))) THEN
  SUBGOAL_THEN `!y:real^3. {y} IN c /\ P y /\ ~(y = xt) ==> a dot y < a dot xt`
  (LABEL_TAC "lt") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [USE_THEN "top" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u w. moi_sfb_rtc (moi_sfb_edge c P) u w
          ==> !u' w'. (if u = xt
                       then segment[xt,u'] IN c /\ ~(u' = xt) /\ a dot u' < a dot xt
                       else u' = u) /\
                      (if w = xt
                       then segment[xt,w'] IN c /\ ~(w' = xt) /\ a dot w' < a dot xt
                       else w' = w)
                      ==> moi_sfb_rtc (moi_sfb_edge c (\w. a dot w < a dot xt)) u' w'`
  (LABEL_TAC "gen") THENL
   [MATCH_MP_TAC MOI_SFB_RTC_INDUCT THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real^3` THEN MAP_EVERY X_GEN_TAC [`u':real^3`; `w':real^3`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THENL
       [STRIP_TAC THEN USE_THEN "g2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[MOI_SFB_RTC_REFL]];
      MAP_EVERY X_GEN_TAC [`u:real^3`; `z:real^3`; `z2:real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") MP_TAC) THEN
      REWRITE_TAC[moi_sfb_edge] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`u':real^3`; `w':real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cu") MP_TAC) THEN
      SUBGOAL_THEN `{z:real^3} IN c /\ {z2:real^3} IN c` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_SFB_SEG_VERTICES]; ALL_TAC] THEN
      ASM_CASES_TAC `z2:real^3 = xt` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `z2:real^3 = xt`)) THEN
        REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `~(z:real^3 = xt)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `a dot (z:real^3) < a dot xt` ASSUME_TAC THENL
         [USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `segment[xt:real^3,z] IN c` ASSUME_TAC THENL
         [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
        MATCH_MP_TAC MOI_SFB_RTC_TRANS THEN EXISTS_TAC `z:real^3` THEN CONJ_TAC THENL
         [USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "g2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `a dot (z2:real^3) < a dot xt` ASSUME_TAC THENL
         [USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_CASES_TAC `z:real^3 = xt` THENL
         [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `z:real^3 = xt`)) THEN
          USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `a dot (z:real^3) < a dot xt` ASSUME_TAC THENL
           [USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC MOI_SFB_RTC_STEP THEN EXISTS_TAC `z:real^3` THEN CONJ_TAC THENL
           [USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[moi_sfb_edge]]]]];
    REPEAT STRIP_TAC THEN
    USE_THEN "gen" (MP_TAC o C MATCH_MP
      (ASSUME `moi_sfb_rtc (moi_sfb_edge c P) (u:real^3) w`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `w:real^3`]) THEN ASM_REWRITE_TAC[]]);;

let MOI_SFB_GRAPH_LEMMA = prove
 (`!c (a:real^3) u w.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\ {u} IN c /\ {w} IN c
     ==> moi_sfb_rtc (moi_sfb_edge c (\x. a dot x <= max (a dot u) (a dot w))) u w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  ABBREV_TAC `m0 = max (a dot u) (a dot (w:real^3))` THEN
  SUBGOAL_THEN `a dot (u:real^3) <= m0 /\ a dot (w:real^3) <= m0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m0" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_VERTICES_FINITE; MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n P. (!y z. {y} IN c /\ {z} IN c /\ P z /\ a dot y <= a dot z ==> P y) /\
          P u /\ P w /\
          CARD {v:real^3 | {v} IN c /\ P v /\ m0 < a dot v} = n /\
          moi_sfb_rtc (moi_sfb_edge c P) u w
          ==> moi_sfb_rtc (moi_sfb_edge c (\x. a dot x <= m0)) u w`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [X_GEN_TAC `P:real^3->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `FINITE {v:real^3 | {v} IN c /\ P v /\ m0 < a dot v}` ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!v:real^3. {v} IN c /\ P v ==> a dot v <= m0` ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        MP_TAC(ISPEC `{v:real^3 | {v} IN c /\ P v /\ m0 < a dot v}` CARD_EQ_0) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SFB_RTC_MONO THEN EXISTS_TAC `moi_sfb_edge c (P:real^3->bool)` THEN
      ASM_REWRITE_TAC[moi_sfb_edge] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `x:real^3`; `y:real^3`]
        MOI_SFB_SEG_VERTICES) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    POP_ASSUM(LABEL_TAC "ih") THEN
    X_GEN_TAC `P:real^3->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dc") STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `S = {v:real^3 | {v} IN c /\ P v /\ m0 < a dot v}` THEN
    SUBGOAL_THEN `FINITE (S:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(S:real^3->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `CARD(S:real^3->bool) = SUC n` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES; NOT_SUC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^3. a dot x`; `S:real^3->bool`] CONTINUOUS_ATTAINS_SUP) THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_IMP_COMPACT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `xt:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup"))) THEN
    SUBGOAL_THEN `{xt:real^3} IN c /\ P xt /\ m0 < a dot xt` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(xt:real^3) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y:real^3. {y} IN c /\ P y ==> a dot y <= a dot xt` (LABEL_TAC "top") THENL
     [REPEAT STRIP_TAC THEN ASM_CASES_TAC `m0 < a dot (y:real^3)` THENL
       [USE_THEN "sup" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        MAP_EVERY UNDISCH_TAC [`~(m0 < a dot (y:real^3))`; `m0 < a dot (xt:real^3)`] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(u:real^3 = xt) /\ ~(w:real^3 = xt)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`m0 < a dot (xt:real^3)`; `a dot (xt:real^3) <= m0`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_sfb_rtc (moi_sfb_edge c (\y. a dot y < a dot xt)) u w`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `P:real^3->bool`; `xt:real^3`]
        MOI_SFB_KEY_STEP) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          USE_THEN "top" ACCEPT_TAC;
          REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFB_LOWER_LINK THEN ASM_REWRITE_TAC[]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "ih" (MP_TAC o SPEC `\y:real^3. P y /\ a dot y < a dot xt`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
       [ALL_TAC; CONJ_TAC]]] THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
         [USE_THEN "dc" MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
          MAP_EVERY UNDISCH_TAC [`a dot (y:real^3) <= a dot z`; `a dot (z:real^3) < a dot xt`] THEN
          REAL_ARITH_TAC];
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`m0 < a dot (xt:real^3)`; `a dot (u:real^3) <= m0`] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`m0 < a dot (xt:real^3)`; `a dot (w:real^3) <= m0`] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `{v:real^3 | {v} IN c /\ (P v /\ a dot v < a dot xt) /\ m0 < a dot v} =
                      S DELETE xt` SUBST1_TAC THENL
         [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM] THEN
          X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
           [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
            UNDISCH_TAC `a dot (xt:real^3) < a dot xt` THEN REWRITE_TAC[REAL_LT_REFL];
            STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
             [USE_THEN "top" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]];
          ASM_SIMP_TAC[CARD_DELETE] THEN ARITH_TAC];
        MATCH_MP_TAC MOI_SFB_RTC_MONO THEN
        EXISTS_TAC `moi_sfb_edge c (\y:real^3. a dot y < a dot xt)` THEN
        ASM_REWRITE_TAC[moi_sfb_edge] THEN
        MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `x:real^3`; `y:real^3`]
          MOI_SFB_SEG_VERTICES) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        CONJ_TAC THEN USE_THEN "dc" MATCH_MP_TAC THEN
        EXISTS_TAC `xt:real^3` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPECL
      [`CARD {v:real^3 | {v} IN c /\ (\x:real^3. T) v /\ m0 < a dot v}`;
       `\x:real^3. T`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_SFB_GRAPH_CONNECTED THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Moise Lemma 3, first half: the parts of the sphere below and above a  *)
(* level are connected, and every point of the sphere above its lowest      *)
(* level is a limit of points below its own level (dually above).           *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_SADDLE_FREE_NEG = prove
 (`!c (a:real^3). moi_sch3_saddle_free c a ==> moi_sch3_saddle_free c (--a)`,
  REWRITE_TAC[moi_sch3_saddle_free] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[MOI_SFB_GENERIC_NEG];
    SUBGOAL_THEN `moi_sch3_crossings c (--a) v = moi_sch3_crossings c a v`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[moi_sch3_crossings; DOT_LNEG; REAL_LT_NEG2] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[SEGMENT_SYM]]);;

let MOI_SFB_SEG_HEIGHT = prove
 (`!(a:real^3) x y r. a dot x < r /\ a dot y < r ==> segment[x,y] SUBSET {z | a dot z < r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `r:real`] CONVEX_HALFSPACE_LT) THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let MOI_SFB_TO_VERTEX = prove
 (`!c (a:real^3) x.
     simplicial_complex c /\ x IN UNIONS c
     ==> ?u. {u} IN c /\ a dot u <= a dot x /\ segment[x,u] SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t:real^3->bool`; `a:real^3`; `x:real^3`]
    MOI_SFB_LOWER_VERTEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `convex (t:real^3->bool)` MP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]]);;

let MOI_SFB_RTC_COMPONENT = prove
 (`!c P (X:real^3->bool) y z.
     (!y z. moi_sfb_edge c P y z ==> segment[y,z] SUBSET X) /\
     moi_sfb_rtc (moi_sfb_edge c P) y z /\ y IN X
     ==> connected_component X y z`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`z:real^3`,`z:real^3`) THEN SPEC_TAC(`y:real^3`,`y:real^3`) THEN
  MATCH_MP_TAC MOI_SFB_RTC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`; `z2:real^3`] THEN
    STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `z:real^3` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[connected_component] THEN EXISTS_TAC `segment[z:real^3,z2]` THEN
      REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]]);;

let MOI_SFB_SUBLEVEL_CONNECTED = prove
 (`!c (a:real^3) r.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c)
     ==> connected (UNIONS c INTER {x | a dot x < r})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  ABBREV_TAC `X = UNIONS c INTER {x:real^3 | a dot x < r}` THEN
  SUBGOAL_THEN
   `!x:real^3. x IN X ==> ?u. {u} IN c /\ a dot u < r /\ connected_component X x u`
  (LABEL_TAC "tov") THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "X" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `x:real^3`]
      MOI_SFB_TO_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `a dot (u:real^3) < r` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a dot (u:real^3) <= a dot x`; `a dot (x:real^3) < r`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[connected_component] THEN EXISTS_TAC `segment[x:real^3,u]` THEN
    REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SFB_SEG_HEIGHT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN STRIP_TAC THEN
  USE_THEN "tov" (MP_TAC o C MATCH_MP (ASSUME `(x1:real^3) IN X`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "tov" (MP_TAC o C MATCH_MP (ASSUME `(x2:real^3) IN X`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `u1:real^3` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `u2:real^3` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_SFB_RTC_COMPONENT THEN
  MAP_EVERY EXISTS_TAC
   [`c:(real^3->bool)->bool`; `\x:real^3. a dot x <= max (a dot u1) (a dot u2)`] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN REWRITE_TAC[moi_sfb_edge] THEN
    STRIP_TAC THEN EXPAND_TAC "X" THEN REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_SFB_SEG_HEIGHT THEN
      MAP_EVERY UNDISCH_TAC [`a dot (y:real^3) <= max (a dot u1) (a dot u2)`;
                             `a dot (z:real^3) <= max (a dot u1) (a dot u2)`;
                             `a dot (u1:real^3) < r`; `a dot (u2:real^3) < r`] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC MOI_SFB_GRAPH_LEMMA THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "X" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `{u1:real^3}` THEN ASM_REWRITE_TAC[IN_SING]]);;

let MOI_SFB_SUPERLEVEL_CONNECTED = prove
 (`!c (a:real^3) r.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c)
     ==> connected (UNIONS c INTER {x | r < a dot x})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `--a:real^3`; `--r:real`]
    MOI_SFB_SUBLEVEL_CONNECTED) THEN
  ASM_SIMP_TAC[MOI_SFB_SADDLE_FREE_NEG; DOT_LNEG; REAL_LT_NEG2]);;

let MOI_SFB_DESCEND = prove
 (`!c (a:real^3) y x.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     y IN UNIONS c /\ x IN UNIONS c /\ a dot x < a dot y
     ==> ?w. a dot w < a dot y /\ segment[y,w] SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  ASM_CASES_TAC `{y:real^3} IN c` THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `x:real^3`]
      MOI_SFB_TO_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `u:real^3`; `y:real^3`]
      MOI_SFB_GRAPH_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `max (a dot u) (a dot (y:real^3)) = a dot y` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a dot (u:real^3) <= a dot x`; `a dot (x:real^3) < a dot y`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_sfb_edge c (\x:real^3. a dot x <= a dot y)`; `u:real^3`;
                   `y:real^3`] MOI_SFB_RTC_LAST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`a dot (y:real^3) <= a dot x`; `a dot (x:real^3) < a dot y`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN
    UNDISCH_TAC `moi_sfb_edge c (\x:real^3. a dot x <= a dot y) z y` THEN
    REWRITE_TAC[moi_sfb_edge] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{z:real^3} IN c` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SFB_SEG_VERTICES]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`y:real^3`; `z:real^3`] (CONJUNCT1 SEGMENT_SYM)) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]];
    UNDISCH_TAC `(y:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real^3->bool`; `y:real^3`]
      MOI_SFB_LOWER_STRICT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `convex (t:real^3->bool)` MP_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]]]);;

let MOI_SFB_IN_CLOSURE_LT = prove
 (`!c (a:real^3) y x.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     y IN UNIONS c /\ x IN UNIONS c /\ a dot x < a dot y
     ==> y IN closure (UNIONS c INTER {z | a dot z < a dot y})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `y:real^3`; `x:real^3`]
    MOI_SFB_DESCEND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_saddle_free; moi_sch3_generic]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = w)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `a dot (w:real^3) < a dot w` THEN
    REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment(w:real^3,y) SUBSET {z | a dot z < a dot y}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z:real^3 | a dot z < a dot y}`; `w:real^3`; `y:real^3`]
      IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ASM_SIMP_TAC[CONVEX_HALFSPACE_LT; INTERIOR_OPEN; OPEN_HALFSPACE_LT;
                 CLOSURE_HALFSPACE_LT; IN_ELIM_THM; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment(y:real^3,w) SUBSET UNIONS c INTER {z | a dot z < a dot y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET_TRANS];
      SUBGOAL_THEN `segment(y:real^3,w) = segment(w,y)` SUBST1_TAC THENL
       [REWRITE_TAC[SEGMENT_SYM]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`) THEN
  EXISTS_TAC `closure(segment(y:real^3,w))` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT];
    MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]]);;

let MOI_SFB_IN_CLOSURE_GT = prove
 (`!c (a:real^3) y x.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     y IN UNIONS c /\ x IN UNIONS c /\ a dot y < a dot x
     ==> y IN closure (UNIONS c INTER {z | a dot y < a dot z})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `--a:real^3`; `y:real^3`; `x:real^3`]
    MOI_SFB_IN_CLOSURE_LT) THEN
  ASM_SIMP_TAC[MOI_SFB_SADDLE_FREE_NEG; DOT_LNEG; REAL_LT_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* 7. The paragraph after Moise Lemma 3: if a level meets the sphere in one  *)
(* polygon and the sphere has points on both sides of the level, the level *)
(* meets the filled sphere in the plane 2-cell bounded by the polygon.      *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_PLANAR2 = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> pl_cell_with_boundary 2 (j UNION inside j) j /\
         connected (inside j) /\ connected (outside j) /\ ~bounded (outside j) /\
         inside j INTER outside j = {} /\ inside j UNION outside j = (:real^2) DIFF j`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `polygonal_path (p:(real^2)list)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_ball 2 (j UNION inside j:real^2->bool)` MP_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k1:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k1:real^2->bool`; `j UNION inside j:real^2->bool`;
                 `f:real^2->real^2`; `g:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `polygonal_path (p:(real^2)list)` MOI_PL2_FRONTIER_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let MOI_SFB_PHI_CONT = prove
 (`!(l:real^3->real^3) q s. linear l ==> (\u. q + l (moi_scx_e u)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  MP_TAC(ISPECL [`moi_scx_e`; `l:real^3->real^3`] LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[MOI_SCX_EP; o_DEF]);;

let MOI_SFB_PSI_CONT = prove
 (`!(l':real^3->real^3) q s.
     linear l' ==> (\x. moi_scx_pr (l' (x - q))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. moi_scx_pr ((l':real^3->real^3) (x - q))) =
                (\y. moi_scx_pr (l' y)) o (\x. x - q)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`l':real^3->real^3`; `moi_scx_pr`] LINEAR_COMPOSE) THEN
    ASM_REWRITE_TAC[MOI_SCX_EP; o_DEF]]);;

let MOI_SFB_PLANE_JORDAN = prove
 (`!(a:real^3) t j.
     ~(a = vec 0) /\ pl_sphere 1 j /\ j SUBSET {x | a dot x = t}
     ==> ?pin pout. connected pin /\ connected pout /\ ~bounded pout /\
                    pl_cell_with_boundary 2 (j UNION pin) j /\
                    j INTER pin = {} /\ j INTER pout = {} /\ pin INTER pout = {} /\
                    j UNION pin UNION pout = {x | a dot x = t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t:real`] MOI_SCX_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `l':real^3->real^3`
    (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!u:real^2. a dot (q + (l:real^3->real^3) (moi_scx_e u)) = t`
  (LABEL_TAC "k1") THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[MOI_SCX_EP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^2. moi_scx_pr ((l':real^3->real^3) ((q + l (moi_scx_e u)) - q)) = u`
  (LABEL_TAC "k2") THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(q + v) - q:real^3 = v`; MOI_SCX_EP]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. a dot x = t ==> ((l':real^3->real^3) (x - q))$3 = &0`
  (LABEL_TAC "k0") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `(l':real^3->real^3) (x - q)` (ASSUME
      `!y:real^3. a dot (q + (l:real^3->real^3) y) = t + norm a * y$3`)) THEN
    REWRITE_TAC[ASSUME `!y:real^3. (l:real^3->real^3) (l' y) = y`;
                VECTOR_ARITH `q + (x - q):real^3 = x`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `t = t + n * y <=> n * y = &0`; REAL_ENTIRE; NORM_EQ_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. a dot x = t
               ==> q + (l:real^3->real^3) (moi_scx_e (moi_scx_pr (l' (x - q)))) = x`
  (LABEL_TAC "k3") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `moi_scx_e (moi_scx_pr ((l':real^3->real^3) (x - q))) = l' (x - q)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_SCX_EP_INV THEN
      USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `J2 = IMAGE (\x:real^3. moi_scx_pr ((l':real^3->real^3) (x - q))) j` THEN
  SUBGOAL_THEN `pl_sphere 1 (J2:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J2" THEN
    SUBGOAL_THEN
     `IMAGE (\x:real^3. moi_scx_pr ((l':real^3->real^3) (x - q))) j =
      IMAGE moi_scx_pr (IMAGE (\x. l' (x - q)) j)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 = &0}`; `(:real^2)`; `moi_scx_e`] THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL; MOI_SCX_PLANE_PLH] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`; `\y:real^3. q + (l:real^3->real^3) y`] THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; SUBSET_UNIV] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC MOI_SS2_AFFINE_PLH THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "k0" MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `J2:real^2->bool` MOI_SFB_PLANAR2) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) J2 = j` ASSUME_TAC THENL
   [EXPAND_TAC "J2" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN
    MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN REWRITE_TAC[o_THM] THEN
    REPEAT STRIP_TAC THEN USE_THEN "k3" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. q + (l:real^3->real^3) (moi_scx_e u) = q + l (moi_scx_e v) ==> u = v`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. moi_scx_pr ((l':real^3->real^3) (x - q))`) THEN
    REWRITE_TAC[] THEN USE_THEN "k2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2
      (IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) (J2 UNION inside J2))
      (IMAGE (\u. q + l (moi_scx_e u)) J2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN
    SUBGOAL_THEN `!X. IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) X =
                      IMAGE (\y. q + l y) (IMAGE moi_scx_e X)`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`; `\x:real^3. (l':real^3->real^3) (x - q)`] THEN
    REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC MOI_SS2_AFFINE_PLH THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `{x:real^3 | x$3 = &0}`; `moi_scx_pr`] THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    REWRITE_TAC[MOI_SCX_PLANE_PLH] THEN ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) (:real^2) =
                {x | a dot x = t}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^2` SUBST1_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      EXISTS_TAC `moi_scx_pr ((l':real^3->real^3) (x - q))` THEN
      CONV_TAC SYM_CONV THEN USE_THEN "k3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) (inside J2)` THEN
  EXISTS_TAC `IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) (outside J2)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `j:real^3->bool`)) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[MOI_SFB_PHI_CONT];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[MOI_SFB_PHI_CONT];
    DISCH_TAC THEN
    UNDISCH_TAC `~bounded(outside J2:real^2->bool)` THEN REWRITE_TAC[] THEN
    ABBREV_TAC `X = IMAGE (\u. q + (l:real^3->real^3) (moi_scx_e u)) (outside J2)` THEN
    SUBGOAL_THEN
     `outside J2 = IMAGE (\x:real^3. moi_scx_pr ((l':real^3->real^3) (x - q))) X`
    SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM IMAGE_ID] THEN
      MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN ASM_REWRITE_TAC[o_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\x:real^3. moi_scx_pr ((l':real^3->real^3) (x - q))) (closure X)` THEN
    SIMP_TAC[IMAGE_SUBSET; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[MOI_SFB_PSI_CONT; COMPACT_CLOSURE];
    ASM_REWRITE_TAC[GSYM IMAGE_UNION];
    MATCH_MP_TAC(SET_RULE
     `!f:real^2->real^3 s t. (!u v. f u = f v ==> u = v) /\ s INTER t = {}
                             ==> IMAGE f s INTER IMAGE f t = {}`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    MATCH_MP_TAC(SET_RULE
     `!f:real^2->real^3 s t. (!u v. f u = f v ==> u = v) /\ s INTER t = {}
                             ==> IMAGE f s INTER IMAGE f t = {}`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP];
    MATCH_MP_TAC(SET_RULE
     `!f:real^2->real^3 s t. (!u v. f u = f v ==> u = v) /\ s INTER t = {}
                             ==> IMAGE f s INTER IMAGE f t = {}`) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      aconv (rhs(concl th)) `{x:real^3 | a dot x = t}`)) THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `inside J2 UNION outside J2 = (:real^2) DIFF J2` THEN SET_TAC[]]);;

let MOI_SFB_CONNECTED_SPLIT = prove
 (`!c e1 e2:real^3->bool.
     connected c /\ open e1 /\ open e2 /\ c SUBSET e1 UNION e2 /\ e1 INTER e2 = {}
     ==> c SUBSET e1 \/ c SUBSET e2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
    concl th = `connected (c:real^3->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_SFB_INSIDE_MEETS_LEVEL = prove
 (`!s (a:real^3) t x1 x2.
     s homeomorphic sphere(vec 0:real^3,&1) /\ ~(a = vec 0) /\
     x1 IN s /\ a dot x1 < t /\ x2 IN s /\ t < a dot x2
     ==> ?z. z IN inside s /\ a dot z = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s SUBSET closure(inside s:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier(inside s:real^3->bool) = s` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`]) THEN
  MP_TAC(ISPECL [`inside s:real^3->bool`; `{x:real^3 | a dot x < t}`;
                 `{x:real^3 | a dot x > t}`] MOI_SFB_CONNECTED_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; real_gt] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; real_gt] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP SUBSET_CLOSURE)) THEN
  ASM_SIMP_TAC[CLOSURE_HALFSPACE_LT; CLOSURE_HALFSPACE_GT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THENL
   [DISCH_THEN(MP_TAC o SPEC `x2:real^3`); DISCH_THEN(MP_TAC o SPEC `x1:real^3`)] THEN
  ANTS_TAC THEN TRY(ASM SET_TAC[]) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SFB_FIBRE = prove
 (`!s (a:real^3) t j.
     s homeomorphic sphere(vec 0:real^3,&1) /\ ~(a = vec 0) /\ pl_sphere 1 j /\
     s INTER {x | a dot x = t} = j /\
     (?x. x IN s /\ a dot x < t) /\ (?x. x IN s /\ t < a dot x)
     ==> pl_cell_with_boundary 2 ((s UNION inside s) INTER {x | a dot x = t}) j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
                       (X_CHOOSE_THEN `x2:real^3` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`a:real^3`; `t:real`; `j:real^3->bool`] MOI_SFB_PLANE_JORDAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s INTER {x:real^3 | a dot x = t} = j` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pin:real^3->bool` (X_CHOOSE_THEN `pout:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `t:real`; `x1:real^3`; `x2:real^3`]
    MOI_SFB_INSIDE_MEETS_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pin INTER s:real^3->bool = {} /\ pout INTER s:real^3->bool = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`s INTER {x:real^3 | a dot x = t} = j`; `j INTER pin:real^3->bool = {}`;
      `j INTER pout:real^3->bool = {}`;
      `j UNION pin UNION pout = {x:real^3 | a dot x = t}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pout SUBSET outside s:real^3->bool` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pout:real^3->bool`; `inside s:real^3->bool`; `outside s:real^3->bool`]
      MOI_SFB_CONNECTED_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `pout INTER s:real^3->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded(pout:real^3->bool)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `inside s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN pin` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN inside s`; `a dot (z:real^3) = t`;
      `j UNION pin UNION pout = {x:real^3 | a dot x = t}`;
      `s INTER {x:real^3 | a dot x = t} = j`; `pout SUBSET outside s:real^3->bool`;
      `inside s INTER outside s:real^3->bool = {}`;
      `inside s UNION outside s:real^3->bool = (:real^3) DIFF s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pin SUBSET inside s:real^3->bool` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`pin:real^3->bool`; `inside s:real^3->bool`; `outside s:real^3->bool`]
      MOI_SFB_CONNECTED_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `pin INTER s:real^3->bool = {}` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN pin`; `(z:real^3) IN inside s`;
                           `pin SUBSET outside s:real^3->bool`;
                           `inside s INTER outside s:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s UNION inside s) INTER {x:real^3 | a dot x = t} = j UNION pin`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`j UNION pin UNION pout = {x:real^3 | a dot x = t}`;
      `s INTER {x:real^3 | a dot x = t} = j`; `pout SUBSET outside s:real^3->bool`;
      `pin SUBSET inside s:real^3->bool`; `inside s INTER outside s:real^3->bool = {}`;
      `inside s UNION outside s:real^3->bool = (:real^3) DIFF s`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 8. Moise Lemma 3: a level strictly between the extremes meets the sphere *)
(* in a single polygon (the polygon splits the sphere into two disks; the   *)
(* connected parts below and above lie in different disks and the level set *)
(* lies in the closures of both).                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_CONNECTED_CLOSED_SPLIT = prove
 (`!c e1 e2:real^3->bool.
     connected c /\ closed e1 /\ closed e2 /\ c SUBSET e1 UNION e2 /\
     e1 INTER e2 INTER c = {}
     ==> c SUBSET e1 \/ c SUBSET e2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED] o check (fun th ->
    concl th = `connected (c:real^3->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_SFB_LEVEL_EQ = prove
 (`!c (a:real^3) t j x1 x2.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     x1 IN UNIONS c /\ a dot x1 < t /\ x2 IN UNIONS c /\ t < a dot x2 /\
     pl_sphere 1 j /\ j SUBSET UNIONS c INTER {x | a dot x = t}
     ==> UNIONS c INTER {x | a dot x = t} = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `j:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (d1:real^3->bool) /\ ~(d1 DIFF j = {}) /\
                closed (d2:real^3->bool) /\ ~(d2 DIFF j = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d1:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    MP_TAC(ISPECL [`d2:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected (UNIONS c INTER {x:real^3 | a dot x < t}) /\
    connected (UNIONS c INTER {x:real^3 | t < a dot x})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SFB_SUBLEVEL_CONNECTED; MOI_SFB_SUPERLEVEL_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS c INTER {x:real^3 | a dot x = t} SUBSET
      closure (UNIONS c INTER {x:real^3 | a dot x < t}) /\
    UNIONS c INTER {x:real^3 | a dot x = t} SUBSET
      closure (UNIONS c INTER {x:real^3 | t < a dot x})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `y:real^3`; `x1:real^3`]
        MOI_SFB_IN_CLOSURE_LT) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `y:real^3`; `x2:real^3`]
        MOI_SFB_IN_CLOSURE_GT) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS c = (UNIONS c INTER {x:real^3 | a dot x < t}) UNION
               (UNIONS c INTER {x:real^3 | t < a dot x}) UNION
               (UNIONS c INTER {x:real^3 | a dot x = t})`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN UNIONS c` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(UNIONS c INTER {x:real^3 | a dot x < t}) INTER j = {} /\
    (UNIONS c INTER {x:real^3 | t < a dot x}) INTER j = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `j SUBSET UNIONS c INTER {x:real^3 | a dot x = t}` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS c INTER {x:real^3 | a dot x < t}` THEN
  ABBREV_TAC `W = UNIONS c INTER {x:real^3 | t < a dot x}` THEN
  ABBREV_TAC `L = UNIONS c INTER {x:real^3 | a dot x = t}` THEN
  SUBGOAL_THEN `(U SUBSET d1 \/ U SUBSET d2) /\ (W SUBSET d1 \/ W SUBSET (d2:real^3->bool))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SFB_CONNECTED_CLOSED_SPLIT THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`U INTER j:real^3->bool = {}`; `W INTER j:real^3->bool = {}`;
      `d1 UNION d2:real^3->bool = UNIONS c`; `d1 INTER d2:real^3->bool = j`;
      `UNIONS c:real^3->bool = U UNION W UNION L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^3->bool. closed e ==> (U SUBSET e ==> closure U SUBSET e) /\
                                  (W SUBSET e ==> closure W SUBSET e)`
  ASSUME_TAC THENL [MESON_TAC[CLOSURE_MINIMAL]; ALL_TAC] THEN
  MP_TAC(MATCH_MP (SPEC `d1:real^3->bool` (ASSUME
    `!e:real^3->bool. closed e ==> (U SUBSET e ==> closure U SUBSET e) /\
                                   (W SUBSET e ==> closure W SUBSET e)`))
    (ASSUME `closed (d1:real^3->bool)`)) THEN
  MP_TAC(MATCH_MP (SPEC `d2:real^3->bool` (ASSUME
    `!e:real^3->bool. closed e ==> (U SUBSET e ==> closure U SUBSET e) /\
                                   (W SUBSET e ==> closure W SUBSET e)`))
    (ASSUME `closed (d2:real^3->bool)`)) THEN
  MAP_EVERY UNDISCH_TAC
   [`d1 UNION d2:real^3->bool = UNIONS c`; `d1 INTER d2:real^3->bool = j`;
    `~(d1 DIFF j:real^3->bool = {})`; `~(d2 DIFF j:real^3->bool = {})`;
    `UNIONS c:real^3->bool = U UNION W UNION L`;
    `L SUBSET closure (U:real^3->bool)`; `L SUBSET closure (W:real^3->bool)`;
    `j SUBSET (L:real^3->bool)`] THEN
  SET_TAC[]);;

let MOI_SFB_FIBRED_FROM_POLYGONS = prove
 (`!c (a:real^3).
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     (!t x1 x2. x1 IN UNIONS c /\ a dot x1 < t /\ x2 IN UNIONS c /\ t < a dot x2
                ==> ?j. pl_sphere 1 j /\ j SUBSET UNIONS c INTER {x | a dot x = t})
     ==> ?lo hi. moi_sch3_fibred (UNIONS c) a lo hi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "poly"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`] MOI_SFB_EXTREMES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a dot (p:real^3)`; `a dot (q:real^3)`] THEN
  REWRITE_TAC[moi_sch3_fibred] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS c /\ (q:real^3) IN UNIONS c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `{p:real^3}`; EXISTS_TAC `{q:real^3}`] THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?j:real^3->bool. pl_sphere 1 j /\ j SUBSET UNIONS c INTER {x | a dot x = t}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "poly" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS c INTER {x:real^3 | a dot x = t} = j` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFB_LEVEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SFB_FIBRE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. A level strictly between the extremes contains a level polygon: the   *)
(* level complex is a graph of degree 2 off the vertex at that level         *)
(* (pc_moi_sch3_lev at a vertex level; the general-level analogues below,    *)
(* adapted from the lemmas MOI_SLV_LEVEL_CARRIER, MOI_SLV_TRI_CROSS,         *)
(* MOI_SLV_LEVEL_EDGES_AT of pc_moi_sch3_lev with the level t in place of    *)
(* the height of a vertex), and it has an edge; then MOI_SLV_G2_COVER.  The  *)
(* main theorem.                                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SFB_GL_CARRIER = prove
 (`!c (a:real^3) t s p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     (!w. {w} IN c ==> ~(a dot w = t)) /\ s IN c /\
     s INTER {x | a dot x = t} = {p}
     ==> ?w1 w2. segment[w1,w2] IN c /\ a dot w1 < t /\ t < a dot w2 /\
                 segment[w1,w2] INTER {x | a dot x = t} = {p} /\
                 p IN segment(w1,w2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN s /\ a dot p = t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s INTER {x:real^3 | a dot x = t} = {p}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `p:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `e INTER {x:real^3 | a dot x = t} = {p}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `e:real^3->bool`] FACE_OF_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s INTER {x:real^3 | a dot x = t}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(e:A->bool) SUBSET s ==> e INTER h SUBSET s INTER h`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUBSET_REFL]];
      ASM_REWRITE_TAC[SING_SUBSET; IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(e:real^3->bool) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(e:real^3->bool) <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` SUBST_ALL_TAC) THEN
      ASM_MESON_TAC[IN_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(e:real^3->bool) = &2)` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^3->bool`; `a:real^3`; `t:real`; `p:real^3`]
        MOI_SLV_RELINT_SLICE_TWO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[INT_LE_REFL] THEN ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `e INTER {x:real^3 | a dot x = t} = {p}` THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:real^3->bool` AFF_DIM_GE) THEN
    SPEC_TAC(`aff_dim(e:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN segment(w1,w2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN relative_interior(segment[w1,w2])` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (w1:real^3) = t) /\ ~(a dot (w2:real^3) = t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?u. &0 < u /\ u < &1 /\ p = (&1 - u) % w1 + u % (w2:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN segment(w1,w2)` THEN
    REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = t`
  ASSUME_TAC THENL
   [UNDISCH_TAC `a dot (p:real^3) = t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  ASM_CASES_TAC `a dot (w1:real^3) < t` THENL
   [MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `a dot (w1:real^3)`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`w2:real^3`; `w1:real^3`] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--c < --y ==> y < c`) THEN
      MATCH_MP_TAC MOI_SLV_CONVEX_SIGN THEN
      MAP_EVERY EXISTS_TAC [`u:real`; `--(a dot (w1:real^3))`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(&1 - u) * a dot (w1:real^3) + u * a dot w2 = t` THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;
let MOI_SFB_GL_TRI_CROSS = prove
 (`!c (a:real^3) t w1 w2 tau p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     (!w. {w} IN c ==> ~(a dot w = t)) /\
     segment[w1,w2] IN c /\ a dot w1 < t /\ t < a dot w2 /\
     segment[w1,w2] INTER {x | a dot x = t} = {p} /\
     tau IN c /\ aff_dim tau = &2 /\ segment[w1,w2] SUBSET tau
     ==> aff_dim(tau INTER {x | a dot x = t}) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(p:real^3) IN segment[w1,w2] /\ a dot p = t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                 `tau:real^3->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w3:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `segment[w1:real^3,w3] IN c /\ segment[w3,w2] IN c /\ {w3} IN c`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `(face_of):(real^3->bool)->(real^3->bool)->bool`))
        (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THENL
     [EXISTS_TAC `{w1:real^3,w3}`; EXISTS_TAC `{w3:real^3,w2}`;
      EXISTS_TAC `{w3:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING]] THEN
    REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?q:real^3. ~(q = p) /\ q IN tau /\ a dot q = t`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a dot (w3:real^3) = t` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `a dot (w3:real^3) < t` THENL
     [MP_TAC(ISPECL [`a:real^3`; `t:real`; `w3:real^3`; `w2:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w3,w2] /\ a dot q = t`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w3:real^3,w2] INTER {z | a dot z = t} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w3:real^3`; `w2:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w1:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(q:real^3) IN segment[w3,w2]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      MP_TAC(ISPECL [`a:real^3`; `t:real`; `w1:real^3`; `w3:real^3`]
        MOI_SLV_CROSS_SING) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:real^3` THEN
      SUBGOAL_THEN `(q:real^3) IN segment[w1,w3] /\ a dot q = t`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w1:real^3,w3] INTER {z | a dot z = t} = {q}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                       `w1:real^3`; `w3:real^3`] MOI_SLV_SEGMENTS_INTER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `w2:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(q:real^3) IN segment[w1,w3]` THEN
        SPEC_TAC(`q:real^3`,`q:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a <= &1 ==> a:int = &1`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{p:real^3,q}`; `tau INTER {x:real^3 | a dot x = t}`]
      AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ASM_REWRITE_TAC[AFF_DIM_2] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC[INT_LE_REFL]];
    MATCH_MP_TAC MOI_SLV_LEVEL_DIM THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]);;
let MOI_SFB_GL_EDGES_AT = prove
 (`!c (a:real^3) t p.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     (!w. {w} IN c ==> ~(a dot w = t)) /\
     {p} IN {s INTER {x | a dot x = t} | s IN c}
     ==> {s | s IN {s INTER {x | a dot x = t} | s IN c} /\
              aff_dim s = &1 /\ p IN s} HAS_SIZE 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_SLV_SPHERE_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s0:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM)) o
    REWRITE_RULE[IN_ELIM_THM] o check (fun th -> aconv (concl th)
      `{p:real^3} IN {s INTER {x | a dot x = t} | s IN c}`)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`;
                 `s0:real^3->bool`; `p:real^3`] MOI_SFB_GL_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(w1:real^3 = w2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{tr:real^3->bool | tr IN c /\ aff_dim tr = &2 /\ segment[w1,w2] SUBSET tr} HAS_SIZE 2` ASSUME_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN {s INTER {x | a dot x = t} | s IN c} /\
         aff_dim s = &1 /\ p IN s} =
    IMAGE (\tr:real^3->bool. tr INTER {x | a dot x = t})
      {tr:real^3->bool | tr IN c /\ aff_dim tr = &2 /\ segment[w1,w2] SUBSET tr}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `sig:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool`
        STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[w1:real^3,w2] SUBSET s` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `p:real^3`] THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM_MESON_TAC[IN_INTER];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(s:real^3->bool) <= &2` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= aff_dim(s:real^3->bool)` MP_TAC THENL
       [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `s:real^3->bool`] AFF_DIM_SUBSET) THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(aff_dim(s:real^3->bool) = &1)` MP_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `segment[w1:real^3,w2] = s` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
          EXISTS_TAC `c:(real^3->bool)->bool` THEN
          ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
          ALL_TAC] THEN
        UNDISCH_TAC `aff_dim (s INTER {x:real^3 | a dot x = t}) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`aff_dim(s:real^3->bool)`,`d:int`) THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `tr:real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `sig:real^3->bool`)) THEN
      CONJ_TAC THENL [EXISTS_TAC `tr:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SFB_GL_TRI_CROSS THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`;
                              `w2:real^3`; `p:real^3`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
        UNDISCH_TAC `segment[w1:real^3,w2] SUBSET tr` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^3->bool`; `t2:real^3->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(t1 INTER {x:real^3 | a dot x = t}) = &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SFB_GL_TRI_CROSS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`;
                          `w2:real^3`; `p:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `t1:real^3->bool`; `t2:real^3->bool`]
    MOI_SLV_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 INTER t2:real^3->bool = segment[w1,w2]` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT] THEN
    MATCH_MP_TAC(INT_ARITH `&1 <= a /\ a < &2 ==> &1 = a:int`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`segment[w1:real^3,w2]`; `t1 INTER t2:real^3->bool`]
        AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_INTER; AFF_DIM_SEGMENT];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `aff_dim(t1:real^3->bool) = &2`)) THEN
      MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(t1:real^3->bool = t2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t1 INTER t2:real^3->bool = t1` THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `aff_dim(t1 INTER {x:real^3 | a dot x = t}) = &1` THEN
  SUBGOAL_THEN `t1 INTER {x:real^3 | a dot x = t} = {p}` SUBST1_TAC THENL
   [UNDISCH_TAC `t1 INTER {x:real^3 | a dot x = t} =
                 t2 INTER {x | a dot x = t}` THEN
    UNDISCH_TAC `t1 INTER t2:real^3->bool = segment[w1,w2]` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] INTER {x | a dot x = t} = {p}` THEN
    UNDISCH_TAC `segment[w1:real^3,w2] SUBSET t1` THEN SET_TAC[];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_SFB_GL_GRAPH2 = prove
 (`!c (a:real^3) t v.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     (!w. {w} IN c ==> ~(a dot w = t))
     ==> moi_slv_graph2 {s INTER {x | a dot x = t} | s IN c} v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_slv_graph2] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFB_GL_EDGES_AT THEN ASM_REWRITE_TAC[]);;

let MOI_SFB_SPHERE_DELETE_CONNECTED = prove
 (`!s v:real^3. s homeomorphic sphere(vec 0:real^3,&1) ==> connected (s DELETE v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `(v:real^3) IN s` THENL
   [SUBGOAL_THEN `s DELETE (v:real^3) =
                  IMAGE (g:real^3->real^3) (sphere(vec 0:real^3,&1) DELETE f v)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      REWRITE_TAC[CONNECTED_PUNCTURED_SPHERE; DIMINDEX_3; ARITH]];
    ASM_SIMP_TAC[SET_RULE `~((v:real^3) IN s) ==> s DELETE v = s`] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`] CONNECTED_SPHERE) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    ASM_MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]]);;

let MOI_SFB_LEVEL_EDGE = prove
 (`!c (a:real^3) t y.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\
     y IN UNIONS c /\ a dot y = t /\ ~({y} IN c)
     ==> ?s0. s0 IN {s INTER {x | a dot x = t} | s IN c} /\ aff_dim s0 = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN sg INTER {x | a dot x = t}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim (sg INTER {x:real^3 | a dot x = t}) = &1` THENL
   [EXISTS_TAC `sg INTER {x:real^3 | a dot x = t}` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `sg:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg INTER {x:real^3 | a dot x = t} = {y}` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim (sg INTER {x:real^3 | a dot x = t}) = &0` MP_TAC THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`; `sg:real^3->bool`]
        MOI_SLV_LEVEL_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(aff_dim (sg INTER {x:real^3 | a dot x = t}) = -- &1)` MP_TAC THENL
       [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(aff_dim (sg INTER {x:real^3 | a dot x = t}) = &1)` THEN
      MP_TAC(ISPEC `sg INTER {x:real^3 | a dot x = t}` AFF_DIM_GE) THEN
      SPEC_TAC(`aff_dim (sg INTER {x:real^3 | a dot x = t})`,`d:int`) THEN INT_ARITH_TAC;
      REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `y':real^3`) THEN
      UNDISCH_TAC `(y:real^3) IN sg INTER {x | a dot x = t}` THEN
      ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w1 w2. segment[w1,w2] IN c /\ a dot w1 < t /\ t < a dot w2 /\
            segment[w1,w2] INTER {x:real^3 | a dot x = t} = {y}`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?v:real^3. {v} IN c /\ a dot v = t` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        concl th = `a dot (v:real^3) = t`)) THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `v:real^3`;
                     `sg:real^3->bool`; `y:real^3`] MOI_SLV_LEVEL_CARRIER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
        MESON_TAC[]];
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`;
                     `sg:real^3->bool`; `y:real^3`] MOI_SFB_GL_CARRIER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `segment[w1:real^3,w2]`] MOI_SCF_SURF_PURE) THEN
  ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tau INTER {x:real^3 | a dot x = t}` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?v:real^3. {v} IN c /\ a dot v = t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `a dot (v:real^3) = t`)) THEN
    MATCH_MP_TAC MOI_SLV_TRI_CROSS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                          `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SFB_GL_TRI_CROSS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `w1:real^3`; `w2:real^3`;
                          `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_SFB_LEVEL_POLYGON = prove
 (`!c (a:real^3) t x1 x2.
     moi_sch3_saddle_free c a /\ pl_sphere 2 (UNIONS c) /\
     x1 IN UNIONS c /\ a dot x1 < t /\ x2 IN UNIONS c /\ t < a dot x2
     ==> ?j. pl_sphere 1 j /\ j SUBSET UNIONS c INTER {x | a dot x = t}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_saddle_free]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SFB_SPHERE_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?y:real^3. y IN UNIONS c /\ a dot y = t /\ ~({y} IN c)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?v:real^3. {v} IN c /\ a dot v = t` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `connected (UNIONS c DELETE (v:real^3)) /\ ~(x1:real^3 = v) /\
                    ~(x2:real^3 = v) /\ a dot x1 <= t /\ t <= a dot (x2:real^3)`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MOI_SFB_SPHERE_DELETE_CONNECTED THEN ASM_REWRITE_TAC[];
          DISCH_THEN SUBST_ALL_TAC THEN
          MAP_EVERY UNDISCH_TAC [`a dot (v:real^3) = t`; `a dot (v:real^3) < t`] THEN
          REAL_ARITH_TAC;
          DISCH_THEN SUBST_ALL_TAC THEN
          MAP_EVERY UNDISCH_TAC [`a dot (v:real^3) = t`; `t < a dot (v:real^3)`] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`UNIONS c DELETE (v:real^3)`; `x1:real^3`; `x2:real^3`;
                     `a:real^3`; `t:real`] CONNECTED_IVT_HYPERPLANE) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `x1:real^3`; `x2:real^3`;
                     `a:real^3`; `t:real`] CONNECTED_IVT_HYPERPLANE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `t:real`; `y:real^3`]
    MOI_SFB_LEVEL_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?v0:real^3. moi_slv_graph2 {s INTER {x | a dot x = t} | s IN c} v0 /\
                {v0} IN {s INTER {x | a dot x = t} | s IN c}`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?v:real^3. {v} IN c /\ a dot v = t` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `v:real^3` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        concl th = `a dot (v:real^3) = t`)) THEN
      MATCH_MP_TAC MOI_SLV_LEVEL_GRAPH2 THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = t} | s IN c}`; `s0:real^3->bool`]
        MOI_SLV_EDGE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u0:real^3` (X_CHOOSE_THEN `w0:real^3`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `u0:real^3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SFB_GL_GRAPH2 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = t} | s IN c}`; `v0:real^3`;
                 `s0:real^3->bool`] MOI_SLV_G2_COVER) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `q SUBSET UNIONS {s INTER {x:real^3 | a dot x = t} | s IN c}` THEN
  ASM_REWRITE_TAC[]);;

let SADDLE_FREE_FIBRED = prove
 (MOI_SCH3_SADDLE_FREE_FIBRED,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SFB_FIBRED_FROM_POLYGONS THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_SFB_LEVEL_POLYGON THEN
  MAP_EVERY EXISTS_TAC [`x1:real^3`; `x2:real^3`] THEN ASM_REWRITE_TAC[]);;

