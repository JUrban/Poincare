(* ========================================================================= *)
(* pc_moi_sch3_amb2: the ambient PL Schoenflies theorem in the plane with a  *)
(* prescribed vertex (Moise GTM 47, Sec 3, Thms 3.4 and 3.7, pp.28-29).  A   *)
(* PL 1-sphere s with s UNION inside s in an open w is carried onto the      *)
(* boundary of a 2-simplex by a PL homeomorphism of the plane that is the    *)
(* identity off w, a given point of s going to a vertex.  Route: s is a      *)
(* polygon (PL_SPHERE_1_POLYGON); a polygon with at least 4 vertices has an  *)
(* ear (a vertex v whose triangle with its neighbours lies in the closed     *)
(* region and meets the polygon in the two edges at v); the ear is removed   *)
(* by a conewise PL homeomorphism supported in a thin convex quadrilateral   *)
(* around the ear triangle (Moise p.28, Case 2); induction on the number of  *)
(* vertices; a last ear removal moves the given point to a vertex.  Main     *)
(* theorem AMB2_VERTEX.                                                      *)
(*                                                                           *)
(* First, list infrastructure for polygons.                                 *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_cone.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Adapted, with their proofs, from earlier HOL Light work (list_edge,       *)
(* polygon_region, AG_ROTATE, AG_SPLIT_AT, AG_SPLIT_LONG, AG_DECOMPOSE_HD,   *)
(* AG_DECOMPOSE, AG_LENGTH_GE_4, AG_LENGTH_4, AG_CARD_VERTICES and           *)
(* helpers), under the names moi_sa2_... and MOI_SA2_....  Changes:          *)
(* MOI_SA2_DECOMPOSE_HD and MOI_SA2_DECOMPOSE have extra conclusions (the    *)
(* diagonal, the path images, the intersection of the two closed regions,    *)
(* the converse edge facts); MOI_SA2_ROTATE1 is MOI_SA2_ROTATE with          *)
(* ROTATE_LIST_TO_FRONT_1.                                                   *)
(* ------------------------------------------------------------------------- *)

let moi_sa2_edge = define
 `(moi_sa2_edge ([]:A list) u w <=> F) /\
  (moi_sa2_edge [a:A] u w <=> F) /\
  (moi_sa2_edge (CONS (a:A) (CONS b t)) u w <=>
        (u = a /\ w = b \/ u = b /\ w = a) \/ moi_sa2_edge (CONS b t) u w)`;;

let MOI_SA2_EDGE_CONS = prove
 (`!(a:A) t u w.
        ~(t = [])
        ==> (moi_sa2_edge (CONS a t) u w <=>
             (u = a /\ w = HD t \/ u = HD t /\ w = a) \/ moi_sa2_edge t u w)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[moi_sa2_edge; HD; NOT_CONS_NIL]);;

let MOI_SA2_EDGE_SYM = prove
 (`!l (u:A) w. moi_sa2_edge l u w <=> moi_sa2_edge l w u`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[moi_sa2_edge] THEN
  X_GEN_TAC `a:A` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[moi_sa2_edge] THEN ASM_MESON_TAC[]);;

let MOI_SA2_EDGE_IMP_MEM = prove
 (`!l (u:A) w. moi_sa2_edge l u w ==> MEM u l /\ MEM w l`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[moi_sa2_edge] THEN
  X_GEN_TAC `a:A` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[moi_sa2_edge; MEM] THEN ASM_MESON_TAC[MEM]);;

let MOI_SA2_EDGE_APPEND = prove
 (`!q r (u:A) w.
        ~(q = []) /\ ~(r = []) /\ LAST q = HD r
        ==> (moi_sa2_edge (APPEND q (TL r)) u w <=>
             moi_sa2_edge q u w \/ moi_sa2_edge r u w)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `x:A` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[APPEND; LAST; moi_sa2_edge] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `CONS (x:A) (TL r) = r` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `~(r:A list = [])` THEN UNDISCH_TAC `x:A = HD r` THEN
    SPEC_TAC(`r:A list`,`r:A list`) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[HD; TL; NOT_CONS_NIL] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`y:A`; `t:A list`] THEN
    REPEAT DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`r:A list`; `u:A`; `w:A`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:A list`; `u:A`; `w:A`] o
      check (fun th -> free_in `y:A` (concl th) && not(free_in `x:A` (concl th)))) THEN
    UNDISCH_TAC `LAST (CONS (x:A) (CONS y t)) = HD r` THEN
    REWRITE_TAC[LAST; NOT_CONS_NIL; APPEND; moi_sa2_edge] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DISJ_ACI]]);;

let MOI_SA2_EDGE_SNOC = prove
 (`!t (z:A) u w.
        ~(t = [])
        ==> (moi_sa2_edge (APPEND t [z]) u w <=>
             moi_sa2_edge t u w \/ (u = LAST t /\ w = z \/ u = z /\ w = LAST t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:A list`; `[LAST t:A; z]`; `u:A`; `w:A`] MOI_SA2_EDGE_APPEND) THEN
  ASM_REWRITE_TAC[TL; HD; NOT_CONS_NIL; moi_sa2_edge]);;

let MOI_SA2_EDGE_ROTATE = prove
 (`!l (u:A) w.
        2 <= LENGTH l /\ LAST l = HD l
        ==> (moi_sa2_edge (APPEND (TL l) [HD(TL l)]) u w <=> moi_sa2_edge l u w)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[HD; TL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t:A list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SA2_EDGE_SNOC; MOI_SA2_EDGE_CONS] THEN
  UNDISCH_TAC `LAST (CONS (h:A) t) = h` THEN ASM_REWRITE_TAC[LAST] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* The closed region of a polygon.                                           *)
(* ------------------------------------------------------------------------- *)

let moi_sa2_region = new_definition
 `moi_sa2_region (p:(real^2)list) =
        inside(path_image(polygonal_path p)) UNION path_image(polygonal_path p)`;;

let MOI_SA2_LENGTH_GE_4 = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)
        ==> 4 <= LENGTH p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
  X_GEN_TAC `a:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
  X_GEN_TAC `b:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                PATHFINISH_LINEPATH] THEN
    ASM_CASES_TAC `c:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

let MOI_SA2_TRIANGLE_REGION = prove
 (`!a b c:real^2. moi_sa2_region [a;b;c;a] = convex hull {a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sa2_region; polygonal_path] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[INSIDE_OF_TRIANGLE; GSYM FRONTIER_OF_TRIANGLE; frontier] THEN
  SUBGOAL_THEN `closure(convex hull {a,b,c}) = convex hull {a,b,c:real^2}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    MP_TAC(ISPEC `convex hull {a,b,c:real^2}` INTERIOR_SUBSET) THEN SET_TAC[]]);;

let MOI_SA2_TRIANGLE_DISTINCT = prove
 (`!a b c:real^2.
        simple_path(polygonal_path [a;b;c;a])
        ==> ~(a = b) /\ ~(b = c) /\ ~(c = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polygonal_path] THEN
  SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; ARC_JOIN_EQ;
           ARC_LINEPATH_EQ]);;


let MOI_SA2_ROTATE = prove
 (`!p a:real^2.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p /\ MEM a p
        ==> ?p'. HD p' = a /\
                 LENGTH p' = LENGTH p /\
                 path_image(polygonal_path p') = path_image(polygonal_path p) /\
                 set_of_list p' = set_of_list p /\
                 simple_path(polygonal_path p') /\
                 pathfinish(polygonal_path p') = pathstart(polygonal_path p') /\
                 (!u w. moi_sa2_edge p' u w <=> moi_sa2_edge p u w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(a:real^2) IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0:num` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_SA2_EDGE_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;



let MOI_SA2_ROTATE1 = prove
 (`!p a:real^2.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p /\ MEM a p
        ==> ?p'. EL 1 p' = a /\
                 LENGTH p' = LENGTH p /\
                 path_image(polygonal_path p') = path_image(polygonal_path p) /\
                 set_of_list p' = set_of_list p /\
                 simple_path(polygonal_path p') /\
                 pathfinish(polygonal_path p') = pathstart(polygonal_path p') /\
                 (!u w. moi_sa2_edge p' u w <=> moi_sa2_edge p u w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ROTATE_LIST_TO_FRONT_1 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(a:real^2) IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0:num` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_SA2_EDGE_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Splitting a simple polygonal path at an interior vertex b, keeping the    *)
(* list structure: p = APPEND q (TL r). (The inner induction of the proof    *)
(* of PICK in 100/pick.ml, with the list equation added.)                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_SPLIT_AT = prove
 (`!b p:(real^2)list.
        simple_path(polygonal_path p) /\
        2 <= LENGTH p /\ MEM (b:real^2) p /\
        ~(pathstart(polygonal_path p) = b) /\
        ~(pathfinish(polygonal_path p) = b)
        ==> ?q r. APPEND q (TL r) = p /\
                  2 <= LENGTH q /\ 2 <= LENGTH r /\
                  LENGTH q + LENGTH r = LENGTH p + 1 /\
                  set_of_list q UNION set_of_list r = set_of_list p /\
                  pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
                  pathfinish(polygonal_path q) = (b:real^2) /\
                  pathstart(polygonal_path r) = b /\
                  pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
                  simple_path(polygonal_path q ++ polygonal_path r) /\
                  path_image(polygonal_path q ++ polygonal_path r) =
                  path_image(polygonal_path p)`,
  GEN_TAC THEN GEN_TAC THEN
WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  MEM] THEN
      MESON_TAC[];
      REWRITE_TAC[LENGTH; ARITH]] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `l:(real^2)list`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN DISCH_TAC THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `a:real^2 = b` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `x:real^2 = b` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN STRIP_TAC THEN
      EXISTS_TAC `[a:real^2;b]` THEN
      EXISTS_TAC `CONS (b:real^2) (CONS y l)` THEN
      CONJ_TAC THENL [REWRITE_TAC[APPEND; TL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[polygonal_path; LENGTH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (x:real^2) (CONS y l)`) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`] THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC n)`] THEN
      ONCE_REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      SIMP_TAC[PATHFINISH_LINEPATH; ARC_IMP_SIMPLE_PATH];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`CONS (a:real^2) q`; `r:(real^2)list`] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[APPEND]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; HD] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_of_list; SET_RULE
       `((a:real^2) INSERT s) UNION t = a INSERT (s UNION t)`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pathfinish(polygonal_path q) = (b:real^2)` THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL] THEN
      UNDISCH_TAC `2 <= LENGTH(q:(real^2)list)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))`;
        `2 <= LENGTH(q:(real^2)list)`] THEN
      SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
      SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) SIMPLE_PATH_ASSOC o snd) THEN
      ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))` THEN
      ASM_CASES_TAC `pathfinish(polygonal_path r) = (a:real^2)` THENL
       [SUBGOAL_THEN
         `pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_MESON_TAC[ARC_LINEPATH_EQ];
        SUBGOAL_THEN
         `~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHSTART_LINEPATH;
                     PATHFINISH_JOIN] THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
        REWRITE_TAC[ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `arc(polygonal_path q ++ polygonal_path r:real^1->real^2)`
        MP_TAC THENL
         [ALL_TAC;
          ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN]] THEN
        MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL]];
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD;
               PATHSTART_POLYGONAL_PATH] THEN
      UNDISCH_THEN
       `path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))`
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Small facts about polygonal paths of lists.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_PP_CONS = prove
 (`!x:real^2 l.
        2 <= LENGTH l
        ==> polygonal_path (CONS x l) = linepath(x,HD l) ++ polygonal_path l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH; HD] THEN
  DISCH_TAC THEN MATCH_MP_TAC POLYGONAL_PATH_CONS_CONS THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC);;

let MOI_SA2_LENGTH2_SEGMENT = prove
 (`!l:(real^2)list.
        LENGTH l = 2
        ==> path_image(polygonal_path l) =
            segment[pathstart(polygonal_path l),pathfinish(polygonal_path l)]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH]);;

let MOI_SA2_SPLIT_LONG = prove
 (`!q r a b:real^2.
        2 <= LENGTH q /\ 2 <= LENGTH r /\ ~(a = b) /\
        pathstart(polygonal_path q) = a /\ pathfinish(polygonal_path q) = b /\
        pathstart(polygonal_path r) = b /\ pathfinish(polygonal_path r) = a /\
        segment(a,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))
        ==> 3 <= LENGTH q /\ 3 <= LENGTH r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image(polygonal_path q ++ polygonal_path r) =
    path_image(polygonal_path q) UNION
    path_image(polygonal_path (r:(real^2)list))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_JOIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(segment(a:real^2,b) SUBSET
      path_image(polygonal_path q ++ polygonal_path r))`
  MP_TAC THENL
   [MP_TAC(ISPEC `path_image(polygonal_path q ++ polygonal_path r):real^2->bool`
      INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC
     `segment(a:real^2,b) SUBSET
      inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`] (CONJUNCT2 SEGMENT_EQ_EMPTY)) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
  MP_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  ASM_CASES_TAC `LENGTH(q:(real^2)list) = 2` THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SA2_LENGTH2_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(r:(real^2)list) = 2` THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SA2_LENGTH2_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Cutting a polygon whose first vertex a sees b through the interior along  *)
(* the diagonal [a,b] into two smaller polygons CONS b q and CONS a r.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_MEM_HD_LAST = prove
 (`!l:A list. ~(l = []) ==> MEM (HD l) l /\ MEM (LAST l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; LAST; MEM] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MEM]);;

let MOI_SA2_DECOMPOSE_HD = prove
 (`!p a b:real^2.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p /\ HD p = a /\ ~(a = b) /\ MEM b p /\
        segment(a,b) SUBSET inside(path_image(polygonal_path p))
        ==> ?p1 p2.
             (LENGTH p1 < LENGTH p /\ LENGTH p2 < LENGTH p /\
              simple_path(polygonal_path p1) /\
              pathfinish(polygonal_path p1) = pathstart(polygonal_path p1) /\
              simple_path(polygonal_path p2) /\
              pathfinish(polygonal_path p2) = pathstart(polygonal_path p2) /\
              moi_sa2_region p1 SUBSET moi_sa2_region p /\
              moi_sa2_region p2 SUBSET moi_sa2_region p /\
              moi_sa2_region p SUBSET moi_sa2_region p1 UNION moi_sa2_region p2 /\
              (!v. MEM v p <=> MEM v p1 \/ MEM v p2) /\
              (!v. MEM v p1 /\ MEM v p2 ==> v = a \/ v = b) /\
              moi_sa2_edge p1 a b /\ moi_sa2_edge p2 a b /\
              (!u w. moi_sa2_edge p u w ==> moi_sa2_edge p1 u w \/ moi_sa2_edge p2 u w)) /\
              (~(a = b) /\
               segment(a,b) SUBSET inside(path_image(polygonal_path p)) /\
               path_image(polygonal_path p) SUBSET
               path_image(polygonal_path p1) UNION path_image(polygonal_path p2) /\
               moi_sa2_region p1 INTER moi_sa2_region p2 = segment[a,b] /\
               (!u w. moi_sa2_edge p1 u w
                      ==> moi_sa2_edge p u w \/ (u = a /\ w = b) \/ (u = b /\ w = a)) /\
               (!u w. moi_sa2_edge p2 u w
                      ==> moi_sa2_edge p u w \/ (u = a /\ w = b) \/ (u = b /\ w = a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p:(real^2)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart(polygonal_path p) = (a:real^2) /\
    pathfinish(polygonal_path p) = a`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^2`; `p:(real^2)list`] MOI_SA2_SPLIT_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `3 <= LENGTH(q:(real^2)list) /\ 3 <= LENGTH(r:(real^2)list)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SA2_SPLIT_LONG THEN
    MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:(real^2)list = []) /\ ~(r:(real^2)list = [])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `HD q = (a:real^2) /\ LAST q = b /\ HD r = b /\ LAST r = a`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ISPEC t PATHSTART_POLYGONAL_PATH) THEN
                        MP_TAC(ISPEC t PATHFINISH_POLYGONAL_PATH))
     [`q:(real^2)list`; `r:(real^2)list`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `arc(polygonal_path q:real^1->real^2) /\
    arc(polygonal_path r:real^1->real^2) /\
    path_image(polygonal_path q) INTER path_image(polygonal_path r) SUBSET
    {a:real^2,b}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r:real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path p) =
    path_image(polygonal_path q) UNION
    path_image(polygonal_path (r:(real^2)list))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `path_image(polygonal_path q ++ polygonal_path r) =
      path_image(polygonal_path (p:(real^2)list))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment(a:real^2,b) INTER path_image(polygonal_path q) = {} /\
    segment(a,b) INTER path_image(polygonal_path r) = {} /\
    segment(a,b) SUBSET
    inside(path_image(polygonal_path q) UNION path_image(polygonal_path r)) /\
    ~(segment(a,b) = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `path_image(polygonal_path p):real^2->bool`
      INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC
     `segment(a:real^2,b) SUBSET inside(path_image(polygonal_path p))` THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:real^2) IN path_image(polygonal_path q) /\
    b IN path_image(polygonal_path q) /\
    a IN path_image(polygonal_path r) /\
    b IN path_image(polygonal_path r)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q /\
    polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SA2_PP_CONS; ARITH_RULE `3 <= n ==> 2 <= n`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS (b:real^2) q)) =
    path_image(polygonal_path q) UNION segment[a,b] /\
    path_image(polygonal_path(CONS (a:real^2) r)) =
    path_image(polygonal_path r) UNION segment[a,b]`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    MP_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `simple_path(polygonal_path(CONS (b:real^2) q)) /\
    pathfinish(polygonal_path(CONS b q)) =
    pathstart(polygonal_path(CONS b q)) /\
    simple_path(polygonal_path(CONS (a:real^2) r)) /\
    pathfinish(polygonal_path(CONS a r)) =
    pathstart(polygonal_path(CONS a r))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                    PATHFINISH_LINEPATH] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`] SEGMENT_CLOSED_OPEN) THEN
    MP_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    MAP_EVERY UNDISCH_TAC
     [`~(a:real^2 = b)`;
      `segment(a:real^2,b) INTER path_image(polygonal_path q) = {}`;
      `segment(a:real^2,b) INTER path_image(polygonal_path r) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q`
   (K ALL_TAC) THEN
  UNDISCH_THEN
   `polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
   (K ALL_TAC) THEN
  MP_TAC(ISPECL [`polygonal_path q:real^1->real^2`;
                 `reversepath(polygonal_path r):real^1->real^2`;
                 `linepath(a:real^2,b)`; `a:real^2`; `b:real^2`]
        SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  SIMPLE_PATH_LINEPATH_EQ; PATH_IMAGE_REVERSEPATH;
                  PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH; SIMPLE_PATH_REVERSEPATH] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `b:real^2`] SEGMENT_CLOSED_OPEN) THEN
    MAP_EVERY UNDISCH_TAC
     [`segment(a:real^2,b) INTER path_image(polygonal_path q) = {}`;
      `segment(a:real^2,b) INTER path_image(polygonal_path r) = {}`;
      `segment(a:real^2,b) SUBSET
       inside(path_image(polygonal_path q) UNION
              path_image(polygonal_path r))`;
      `~(segment(a:real^2,b) = {})`;
      `path_image(polygonal_path q) INTER path_image(polygonal_path r)
       SUBSET {a:real^2,b}`;
      `(a:real^2) IN path_image(polygonal_path q)`;
      `(b:real^2) IN path_image(polygonal_path q)`;
      `(a:real^2) IN path_image(polygonal_path r)`;
      `(b:real^2) IN path_image(polygonal_path r)`] THEN
    SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!v:real^2. MEM v p <=> MEM v q \/ MEM v r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
    UNDISCH_TAC
     `set_of_list q UNION set_of_list r = set_of_list (p:(real^2)list)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (a:real^2) q /\ MEM (b:real^2) q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SA2_MEM_HD_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u w:real^2. moi_sa2_edge p u w <=> moi_sa2_edge q u w \/ moi_sa2_edge r u w`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_THEN `APPEND q (TL r) = (p:(real^2)list)` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_SA2_EDGE_APPEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `CONS (b:real^2) q` THEN EXISTS_TAC `CONS (a:real^2) r` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[moi_sa2_region] THEN
    MP_TAC(ISPEC `path_image(polygonal_path q) UNION
                  path_image(polygonal_path (r:(real^2)list))`
      INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `path_image(polygonal_path q) UNION segment[a:real^2,b]`
      INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `path_image(polygonal_path r) UNION segment[a:real^2,b]`
      INSIDE_NO_OVERLAP) THEN
    REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`inside(path_image(polygonal_path q) UNION segment[a,b]) UNION
         inside(path_image(polygonal_path r) UNION segment[a,b]) UNION
         (segment[a,b] DIFF {a,b}) =
         inside(path_image(polygonal_path q) UNION
                path_image(polygonal_path (r:(real^2)list)))`;
        `inside(path_image(polygonal_path q) UNION segment[a,b]) INTER
         inside(path_image(polygonal_path r) UNION segment[a,b]) =
         {}:real^2->bool`;
        `inside(path_image(polygonal_path q) UNION
                path_image(polygonal_path (r:(real^2)list))) INTER
         (path_image(polygonal_path q) UNION path_image(polygonal_path r)) =
         {}`;
        `inside(path_image(polygonal_path q) UNION segment[a:real^2,b]) INTER
         (path_image(polygonal_path q) UNION segment[a,b]) = {}`;
        `inside(path_image(polygonal_path r) UNION segment[a:real^2,b]) INTER
         (path_image(polygonal_path r) UNION segment[a,b]) = {}`;
        `path_image(polygonal_path q) INTER path_image(polygonal_path r)
         SUBSET {a:real^2,b}`] THEN
      MP_TAC(ISPECL [`a:real^2`; `b:real^2`] ENDS_IN_SEGMENT) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      ASM_SIMP_TAC[MOI_SA2_EDGE_CONS] THEN MESON_TAC[];
      ASM_SIMP_TAC[MOI_SA2_EDGE_CONS] THEN MESON_TAC[]]] THEN
  ASM_REWRITE_TAC[LENGTH; moi_sa2_region] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC
     [`inside(path_image(polygonal_path q) UNION segment[a,b]) UNION
       inside(path_image(polygonal_path r) UNION segment[a,b]) UNION
       (segment[a,b] DIFF {a,b}) =
       inside(path_image(polygonal_path q) UNION
              path_image(polygonal_path (r:(real^2)list)))`;
      `(a:real^2) IN path_image(polygonal_path q)`;
      `(b:real^2) IN path_image(polygonal_path q)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`inside(path_image(polygonal_path q) UNION segment[a,b]) UNION
       inside(path_image(polygonal_path r) UNION segment[a,b]) UNION
       (segment[a,b] DIFF {a,b}) =
       inside(path_image(polygonal_path q) UNION
              path_image(polygonal_path (r:(real^2)list)))`;
      `(a:real^2) IN path_image(polygonal_path r)`;
      `(b:real^2) IN path_image(polygonal_path r)`] THEN
    SET_TAC[];
    UNDISCH_TAC
     `inside(path_image(polygonal_path q) UNION segment[a,b]) UNION
      inside(path_image(polygonal_path r) UNION segment[a,b]) UNION
      (segment[a,b] DIFF {a,b}) =
      inside(path_image(polygonal_path q) UNION
             path_image(polygonal_path (r:(real^2)list)))` THEN
    SET_TAC[];
    REWRITE_TAC[MEM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEM] THEN X_GEN_TAC `v:real^2` THEN
    ASM_CASES_TAC `v:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `v:real^2 = b` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `q:(real^2)list` VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
    MP_TAC(ISPEC `r:(real^2)list` VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `path_image(polygonal_path q) INTER path_image(polygonal_path r)
      SUBSET {a:real^2,b}` THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[MOI_SA2_EDGE_CONS];
    ASM_SIMP_TAC[MOI_SA2_EDGE_CONS];
    ASM_SIMP_TAC[MOI_SA2_EDGE_CONS] THEN MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Decomposition along some diagonal (after rotating the list).              *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_DECOMPOSE = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?p1 p2 a b.
             (LENGTH p1 < LENGTH p /\ LENGTH p2 < LENGTH p /\
              simple_path(polygonal_path p1) /\
              pathfinish(polygonal_path p1) = pathstart(polygonal_path p1) /\
              simple_path(polygonal_path p2) /\
              pathfinish(polygonal_path p2) = pathstart(polygonal_path p2) /\
              moi_sa2_region p1 SUBSET moi_sa2_region p /\
              moi_sa2_region p2 SUBSET moi_sa2_region p /\
              moi_sa2_region p SUBSET moi_sa2_region p1 UNION moi_sa2_region p2 /\
              (!v. MEM v p <=> MEM v p1 \/ MEM v p2) /\
              (!v. MEM v p1 /\ MEM v p2 ==> v = a \/ v = b) /\
              moi_sa2_edge p1 a b /\ moi_sa2_edge p2 a b /\
              (!u w. moi_sa2_edge p u w ==> moi_sa2_edge p1 u w \/ moi_sa2_edge p2 u w)) /\
              (~(a = b) /\
               segment(a,b) SUBSET inside(path_image(polygonal_path p)) /\
               path_image(polygonal_path p) SUBSET
               path_image(polygonal_path p1) UNION path_image(polygonal_path p2) /\
               moi_sa2_region p1 INTER moi_sa2_region p2 = segment[a,b] /\
               (!u w. moi_sa2_edge p1 u w
                      ==> moi_sa2_edge p u w \/ (u = a /\ w = b) \/ (u = b /\ w = a)) /\
               (!u w. moi_sa2_edge p2 u w
                      ==> moi_sa2_edge p u w \/ (u = a /\ w = b) \/ (u = b /\ w = a)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:(real^2)list` POLYGON_CHOP_IN_TWO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(real^2)list`; `a:real^2`] MOI_SA2_ROTATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':(real^2)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!v:real^2. MEM v p' <=> MEM v p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_sa2_region p' = moi_sa2_region p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_sa2_region]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p':(real^2)list`; `a:real^2`; `b:real^2`]
    MOI_SA2_DECOMPOSE_HD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:(real^2)list`
    (X_CHOOSE_THEN `p2:(real^2)list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`p1:(real^2)list`; `p2:(real^2)list`; `a:real^2`; `b:real^2`] THEN
  ASM_REWRITE_TAC[]);;



let MOI_SA2_LENGTH_4 = prove
 (`!p:A list. LENGTH p = 4 ==> ?a b c d. p = [a;b;c;d]`,
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; LENGTH_EQ_CONS;
              LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let MOI_SA2_HAS_EDGE = prove
 (`!p:(real^2)list. 2 <= LENGTH p ==> ?u w. moi_sa2_edge p u w`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH] THEN
  POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`t:(real^2)list`,`t:(real^2)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH; moi_sa2_edge] THEN
  MESON_TAC[]);;

let MOI_SA2_CARD_VERTICES = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)
        ==> CARD(set_of_list p) = LENGTH p - 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 <= LENGTH(p:(real^2)list)` MP_TAC THENL
   [MATCH_MP_TAC MOI_SA2_LENGTH_GE_4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(t:(real^2)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `arc(polygonal_path(t:(real^2)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `simple_path(polygonal_path(CONS (h:real^2) t))` THEN
    SUBGOAL_THEN `2 <= LENGTH(t:(real^2)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_SA2_PP_CONS] THEN
    SUBGOAL_THEN `pathfinish(polygonal_path t) = (h:real^2)` ASSUME_TAC THENL
     [UNDISCH_TAC
       `pathfinish(polygonal_path(CONS (h:real^2) t)) =
        pathstart(polygonal_path(CONS h t))` THEN
      ASM_SIMP_TAC[MOI_SA2_PP_CONS; PATHFINISH_JOIN; PATHSTART_JOIN;
                   PATHSTART_LINEPATH];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ARC_POLYGONAL_PATH_IMP_DISTINCT) THEN
  REWRITE_TAC[GSYM HAS_SIZE_SET_OF_LIST; HAS_SIZE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `set_of_list(CONS (h:real^2) t) = set_of_list t`
  SUBST1_TAC THENL
   [REWRITE_TAC[set_of_list] THEN MATCH_MP_TAC(SET_RULE
     `(x:real^2) IN s ==> x INSERT s = s`) THEN
    REWRITE_TAC[IN_SET_OF_LIST] THEN
    SUBGOAL_THEN `h:real^2 = LAST t` SUBST1_TAC THENL
     [UNDISCH_TAC
       `pathfinish(polygonal_path(CONS (h:real^2) t)) =
        pathstart(polygonal_path(CONS h t))` THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                      NOT_CONS_NIL; HD; LAST] THEN
      MESON_TAC[];
      ASM_MESON_TAC[MOI_SA2_MEM_HD_LAST]];
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Facts about simple closed polygonal paths (edges in the                  *)
(* path image, path images as finite unions of segments, the neighbours of  *)
(* the second vertex, triangles).                                            *)
(* ------------------------------------------------------------------------- *)

(* Adapted, with its proof, from AG_PATH_IMAGE_CONS of earlier HOL Light      *)
(* work.                                                                      *)

let MOI_SA2_PATH_IMAGE_CONS = prove
 (`!a:real^2 l.
        ~(l = [])
        ==> path_image(polygonal_path(CONS a l)) =
            segment[a,HD l] UNION path_image(polygonal_path l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD] THEN
  ASM_CASES_TAC `t:(real^2)list = []` THENL
   [ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    MP_TAC(ISPECL [`a:real^2`; `h:real^2`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; PATH_IMAGE_JOIN;
                 PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL;
                 HD; PATH_IMAGE_LINEPATH]]);;

let MOI_SA2_EDGE_SUBSET_PATH = prove
 (`!p (a:real^2) b.
        moi_sa2_edge p a b ==> segment[a,b] SUBSET path_image(polygonal_path p)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[moi_sa2_edge] THEN
  ASM_CASES_TAC `t:(real^2)list = []` THEN ASM_REWRITE_TAC[moi_sa2_edge] THEN
  ASM_SIMP_TAC[MOI_SA2_EDGE_CONS; MOI_SA2_PATH_IMAGE_CONS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^2`; `HD t:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `b:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_SA2_PATH_SEGMENTS = prove
 (`!p:(real^2)list.
        ?c. FINITE c /\ path_image(polygonal_path p) = UNIONS c /\
            !k. k IN c ==> ?x y:real^2. k = segment[x,y]`,
  LIST_INDUCT_TAC THENL
   [EXISTS_TAC `{segment[vec 0:real^2,vec 0]}` THEN
    REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; FINITE_SING; UNIONS_1;
                IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:(real^2)list = []` THENL
   [EXISTS_TAC `{segment[h:real^2,h]}` THEN
    ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; FINITE_SING;
                    UNIONS_1; IN_SING] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(segment[h:real^2,HD t]) INSERT c` THEN
  ASM_SIMP_TAC[MOI_SA2_PATH_IMAGE_CONS; FINITE_INSERT; UNIONS_INSERT;
               FORALL_IN_INSERT] THEN
  MESON_TAC[]);;

(* The second vertex of a simple closed polygon with at least four vertices  *)
(* occurs once, and its only neighbours are the first and the third vertex.  *)

let MOI_SA2_EL1_FACTS = prove
 (`!x v y (l:(real^2)list).
        simple_path(polygonal_path(CONS x (CONS v (CONS y l)))) /\
        pathfinish(polygonal_path(CONS x (CONS v (CONS y l)))) =
        pathstart(polygonal_path(CONS x (CONS v (CONS y l)))) /\
        5 <= LENGTH(CONS x (CONS v (CONS y l)))
        ==> ~(l = []) /\ LAST l = x /\ MEM x l /\
            ~MEM v (CONS y l) /\ ~(x = y) /\ ~(v = x) /\ ~(v = y) /\
            (!u. moi_sa2_edge (CONS x (CONS v (CONS y l))) u v <=>
                 u = x \/ u = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(l:(real^2)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LAST l = (x:real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `pathfinish(polygonal_path(CONS x (CONS v (CONS y l)))) =
      pathstart(polygonal_path(CONS (x:real^2) (CONS v (CONS y l))))` THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                    NOT_CONS_NIL; HD; LAST];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (x:real^2) l` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SA2_MEM_HD_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(set_of_list(CONS (x:real^2) (CONS v (CONS y l)))) = LENGTH l + 2`
  MP_TAC THENL
   [MP_TAC(ISPEC `CONS (x:real^2) (CONS v (CONS y l))` MOI_SA2_CARD_VERTICES) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:(real^2)list` CARD_SET_OF_LIST_LE) THEN
  SUBGOAL_THEN `FINITE(set_of_list(l:(real^2)list))` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_SET_OF_LIST]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN set_of_list l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
  REWRITE_TAC[set_of_list] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; IN_INSERT] THEN
  ASM_CASES_TAC `y:real^2 = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(y:real^2) IN set_of_list l` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v:real^2 = y` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v:real^2 = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(v:real^2) IN set_of_list l` THEN ASM_REWRITE_TAC[] THEN
  TRY ARITH_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[MEM; GSYM IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:real^2` THEN REWRITE_TAC[moi_sa2_edge] THEN
  SUBGOAL_THEN `~moi_sa2_edge (CONS (y:real^2) l) u v` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP MOI_SA2_EDGE_IMP_MEM) THEN
    ASM_REWRITE_TAC[MEM; GSYM IN_SET_OF_LIST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Three-vertex polygons: the vertices are not collinear, and any edge has  *)
(* a third vertex opposite to it.                                            *)

let MOI_SA2_TRIANGLE_PATH_IMAGE = prove
 (`!a b c:real^2.
        path_image(polygonal_path [a;b;c;a]) =
        segment[a,b] UNION segment[b,c] UNION segment[c,a]`,
  REWRITE_TAC[polygonal_path] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH]);;

let MOI_SA2_TRIANGLE_NONCOLLINEAR = prove
 (`!a b c:real^2. simple_path(polygonal_path [a;b;c;a]) ==> ~collinear{a,b,c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `polygonal_path [a:real^2;b;c;a]` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                  NOT_CONS_NIL; HD; LAST] THEN
  REWRITE_TAC[MOI_SA2_TRIANGLE_PATH_IMAGE; INSIDE_OF_TRIANGLE] THEN
  MATCH_MP_TAC(TAUT `p ==> ~(~p /\ q)`) THEN
  MATCH_MP_TAC NEGLIGIBLE_EMPTY_INTERIOR THEN
  MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
  ASM_REWRITE_TAC[COLLINEAR_CONVEX_HULL_COLLINEAR]);;

let MOI_SA2_TRIANGLE_THIRD = prove
 (`!x0 x1 x2 a b:real^2.
        simple_path(polygonal_path [x0;x1;x2;x0]) /\
        moi_sa2_edge [x0;x1;x2;x0] a b
        ==> ?z. ~(z = a) /\ ~(z = b) /\ MEM z [x0;x1;x2;x0] /\
                moi_sa2_edge [x0;x1;x2;x0] a z /\
                moi_sa2_edge [x0;x1;x2;x0] z b /\
                ~collinear{a,z,b} /\
                moi_sa2_region [x0;x1;x2;x0] = convex hull {a,z,b} /\
                path_image(polygonal_path [x0;x1;x2;x0]) =
                segment[a,z] UNION segment[z,b] UNION segment[a,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SA2_TRIANGLE_NONCOLLINEAR) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SA2_TRIANGLE_DISTINCT) THEN
  REWRITE_TAC[MOI_SA2_TRIANGLE_REGION; MOI_SA2_TRIANGLE_PATH_IMAGE;
              moi_sa2_edge; MEM] THEN
  MP_TAC(ISPECL [`x0:real^2`;`x1:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  MP_TAC(ISPECL [`x1:real^2`;`x2:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  MP_TAC(ISPECL [`x2:real^2`;`x0:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(x1:real^2 = x0) /\ ~(x2:real^2 = x1) /\ ~(x0:real^2 = x2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  MAP_FIRST (fun t -> EXISTS_TAC t THEN ASM_REWRITE_TAC[] THEN
                      REWRITE_TAC[INSERT_AC] THEN ASM_REWRITE_TAC[] THEN
                      ASM SET_TAC[] THEN NO_TAC)
   [`x0:real^2`; `x1:real^2`; `x2:real^2`]);;

(* ------------------------------------------------------------------------- *)
(* Ears.  An ear of a polygon p at the vertex z: the triangle               *)
(* of z and its two neighbours u, w is not degenerate, lies in the closed    *)
(* region of p, and meets the polygon exactly in the two edges at z.  Every *)
(* polygon with at least four vertices has an ear away from the ends of any *)
(* given edge (the two-ears argument of Meisters, as in the proof of        *)
(* Moise Thm 3.3, p.27, with the diagonal splitting of MOI_SA2_DECOMPOSE).  *)
(* ------------------------------------------------------------------------- *)

let moi_sa2_ear = new_definition
 `moi_sa2_ear (p:(real^2)list) (z:real^2) <=>
    ?u w. moi_sa2_edge p u z /\ moi_sa2_edge p z w /\ ~collinear{u,z,w} /\
          convex hull {u,z,w} SUBSET moi_sa2_region p /\
          path_image(polygonal_path p) INTER convex hull {u,z,w} =
          segment[u,z] UNION segment[z,w]`;;

let MOI_SA2_EAR_SIDE = prove
 (`!p p1 p2 (a:real^2) b.
     simple_path(polygonal_path p1) /\
     pathfinish(polygonal_path p1) = pathstart(polygonal_path p1) /\
     moi_sa2_region p1 SUBSET moi_sa2_region p /\
     moi_sa2_edge p1 a b /\
     segment(a,b) SUBSET inside(path_image(polygonal_path p)) /\
     path_image(polygonal_path p) SUBSET
     path_image(polygonal_path p1) UNION path_image(polygonal_path p2) /\
     moi_sa2_region p1 INTER moi_sa2_region p2 = segment[a,b] /\
     (!u w. moi_sa2_edge p1 u w
            ==> moi_sa2_edge p u w \/ (u = a /\ w = b) \/ (u = b /\ w = a)) /\
     (5 <= LENGTH p1 ==> ?z. moi_sa2_ear p1 z /\ ~(z = a) /\ ~(z = b))
     ==> ?z. moi_sa2_ear p z /\ MEM z p1 /\ ~(z = a) /\ ~(z = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^2. x IN path_image(polygonal_path p) /\ x IN moi_sa2_region p1
               ==> x IN path_image(polygonal_path p1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[a:real^2,b] SUBSET path_image(polygonal_path p1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SA2_EDGE_SUBSET_PATH THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `path_image(polygonal_path(p:(real^2)list))`
      INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`] SEGMENT_CLOSED_OPEN) THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_sa2_region p1 INTER moi_sa2_region p2 = segment[a:real^2,b]`;
      `path_image(polygonal_path p) SUBSET
       path_image(polygonal_path p1) UNION
       path_image(polygonal_path (p2:(real^2)list))`;
      `segment(a:real^2,b) SUBSET inside(path_image(polygonal_path p))`;
      `(x:real^2) IN path_image(polygonal_path p)`;
      `(x:real^2) IN moi_sa2_region p1`;
      `segment[a:real^2,b] SUBSET path_image(polygonal_path p1)`] THEN
    REWRITE_TAC[moi_sa2_region] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u z w:real^2.
        moi_sa2_edge p u z /\ moi_sa2_edge p z w
        ==> segment[u,z] UNION segment[z,w] SUBSET
            path_image(polygonal_path p) INTER convex hull {u,z,w}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[UNION_SUBSET; SUBSET_INTER] THEN
    ASM_SIMP_TAC[MOI_SA2_EDGE_SUBSET_PATH] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `5 <= LENGTH(p1:(real^2)list)` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_sa2_ear p1 (z:real^2)` THEN REWRITE_TAC[moi_sa2_ear] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `w:real^2`
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOI_SA2_EDGE_IMP_MEM]] THEN
    SUBGOAL_THEN `moi_sa2_edge p (u:real^2) z /\ moi_sa2_edge p z (w:real^2)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:real^2`; `w:real^2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC
     `path_image(polygonal_path p1) INTER convex hull {u:real^2,z,w} =
      segment[u,z] UNION segment[z,w]` THEN
    UNDISCH_TAC `convex hull {u:real^2,z,w} SUBSET moi_sa2_region p1` THEN
    UNDISCH_TAC
     `!x:real^2. x IN path_image(polygonal_path p) /\ x IN moi_sa2_region p1
                 ==> x IN path_image(polygonal_path p1)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(p1:(real^2)list) = 4` MP_TAC THENL
   [MP_TAC(ISPEC `p1:(real^2)list` MOI_SA2_LENGTH_GE_4) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SA2_LENGTH_4) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x0:real^2`; `x1:real^2`; `x2:real^2`; `x3:real^2`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `x3:real^2 = x0` SUBST_ALL_TAC THENL
   [UNDISCH_TAC
     `pathfinish(polygonal_path [x0;x1;x2;x3]) =
      pathstart(polygonal_path [x0:real^2;x1;x2;x3])` THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                NOT_CONS_NIL; HD; LAST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x0:real^2`; `x1:real^2`; `x2:real^2`; `a:real^2`; `b:real^2`]
    MOI_SA2_TRIANGLE_THIRD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[moi_sa2_ear] THEN
  SUBGOAL_THEN `moi_sa2_edge p (a:real^2) z /\ moi_sa2_edge p z (b:real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; SUBSET_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPEC `path_image(polygonal_path(p:(real^2)list))`
    INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`] SEGMENT_CLOSED_OPEN) THEN
  MP_TAC(ISPECL [`a:real^2`; `z:real^2`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`z:real^2`; `b:real^2`] ENDS_IN_SEGMENT) THEN
  UNDISCH_TAC
   `!x:real^2. x IN path_image(polygonal_path p) /\
               x IN moi_sa2_region [x0; x1; x2; x0]
               ==> x IN path_image(polygonal_path [x0; x1; x2; x0])` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `segment(a:real^2,b) SUBSET inside(path_image(polygonal_path p))` THEN
  SET_TAC[]);;

let MOI_SA2_EAR_EXISTS = prove
 (`!n (p:(real^2)list) a b.
     LENGTH p = n /\
     simple_path(polygonal_path p) /\
     pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
     5 <= LENGTH p /\ moi_sa2_edge p a b
     ==> ?z. moi_sa2_ear p z /\ ~(z = a) /\ ~(z = b)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:(real^2)list`; `a0:real^2`; `b0:real^2`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `p:(real^2)list` MOI_SA2_DECOMPOSE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p1:(real^2)list`; `p2:(real^2)list`; `a:real^2`; `b:real^2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!q:(real^2)list.
       LENGTH q < LENGTH(p:(real^2)list) /\ simple_path(polygonal_path q) /\
       pathfinish(polygonal_path q) = pathstart(polygonal_path q) /\
       moi_sa2_edge q a b
       ==> 5 <= LENGTH q ==> ?z. moi_sa2_ear q z /\ ~(z = a) /\ ~(z = b)`
  (LABEL_TAC "ih2") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH(q:(real^2)list)`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ASSUME
   `!u w:real^2. moi_sa2_edge p u w
                 ==> moi_sa2_edge p1 u w \/ moi_sa2_edge p2 u w`)) THENL
   [MP_TAC(ISPECL [`p:(real^2)list`; `p2:(real^2)list`; `p1:(real^2)list`;
                   `a:real^2`; `b:real^2`] MOI_SA2_EAR_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "ih2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC];
    MP_TAC(ISPECL [`p:(real^2)list`; `p1:(real^2)list`; `p2:(real^2)list`;
                   `a:real^2`; `b:real^2`] MOI_SA2_EAR_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ih2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_EDGE_IMP_MEM) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Affine coordinates relative to a triangle u v w, and the                  *)
(* thin convex quadrilateral moi_sa2_quad u v w e around the triangle: its   *)
(* vertices are u, w, a point just beyond v and a point just beyond the      *)
(* midpoint of [u,w] (Moise p.28, Figure 3.3).                              *)
(* ------------------------------------------------------------------------- *)

let moi_sa2_det = new_definition
 `moi_sa2_det (a:real^2) (b:real^2) = a$1 * b$2 - a$2 * b$1`;;

let moi_sa2_ca = new_definition
 `moi_sa2_ca (u:real^2) v w z =
    moi_sa2_det (z - u) (w - u) / moi_sa2_det (v - u) (w - u)`;;

let moi_sa2_cb = new_definition
 `moi_sa2_cb (u:real^2) v w z =
    moi_sa2_det (v - u) (z - u) / moi_sa2_det (v - u) (w - u)`;;

let moi_sa2_quad = new_definition
 `moi_sa2_quad (u:real^2) v w e =
    convex hull {u, v + e % (v - midpoint(u,w)), w,
                 midpoint(u,w) + e % (midpoint(u,w) - v)}`;;

let MOI_SA2_DET_NONCOLLINEAR = prove
 (`!u v w:real^2. ~collinear{u,v,w} <=> ~(moi_sa2_det (v - u) (w - u) = &0)`,
  REWRITE_TAC[COLLINEAR_3_2D; moi_sa2_det; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_SA2_COORDS = prove
 (`!u v w z:real^2.
        ~collinear{u,v,w}
        ==> z = u + moi_sa2_ca u v w z % (v - u) + moi_sa2_cb u v w z % (w - u)`,
  REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR; moi_sa2_ca; moi_sa2_cb; moi_sa2_det] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

let MOI_SA2_CA_AFFINE = prove
 (`!u v w x y:real^2 s t.
        s + t = &1
        ==> moi_sa2_ca u v w (s % x + t % y) =
            s * moi_sa2_ca u v w x + t * moi_sa2_ca u v w y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sa2_ca; real_div] THEN
  SUBGOAL_THEN
   `moi_sa2_det ((s % x + t % y) - u) (w - u) =
    s * moi_sa2_det (x - u) (w - u) + t * moi_sa2_det ((y:real^2) - u) (w - u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_sa2_det; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `s + t = &1` THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

let MOI_SA2_CB_AFFINE = prove
 (`!u v w x y:real^2 s t.
        s + t = &1
        ==> moi_sa2_cb u v w (s % x + t % y) =
            s * moi_sa2_cb u v w x + t * moi_sa2_cb u v w y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sa2_cb; real_div] THEN
  SUBGOAL_THEN
   `moi_sa2_det (v - u) ((s % x + t % y) - u) =
    s * moi_sa2_det (v - u) (x - u) + t * moi_sa2_det (v - u) ((y:real^2) - u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_sa2_det; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `s + t = &1` THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

let MOI_SA2_CA_RAY = prove
 (`!u v w x:real^2 t.
        moi_sa2_ca u v w (u + t % (x - u)) = t * moi_sa2_ca u v w x /\
        moi_sa2_cb u v w (u + t % (x - u)) = t * moi_sa2_cb u v w x`,
  REWRITE_TAC[moi_sa2_ca; moi_sa2_cb; moi_sa2_det; real_div;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_SA2_COORD_VALUES = prove
 (`!u v w:real^2 e.
        ~collinear{u,v,w}
        ==> moi_sa2_ca u v w u = &0 /\ moi_sa2_cb u v w u = &0 /\
            moi_sa2_ca u v w v = &1 /\ moi_sa2_cb u v w v = &0 /\
            moi_sa2_ca u v w w = &0 /\ moi_sa2_cb u v w w = &1 /\
            moi_sa2_ca u v w (midpoint(u,w)) = &0 /\
            moi_sa2_cb u v w (midpoint(u,w)) = inv(&2) /\
            moi_sa2_ca u v w (v + e % (v - midpoint(u,w))) = &1 + e /\
            moi_sa2_cb u v w (v + e % (v - midpoint(u,w))) = --(e / &2) /\
            moi_sa2_ca u v w (midpoint(u,w) + e % (midpoint(u,w) - v)) = --e /\
            moi_sa2_cb u v w (midpoint(u,w) + e % (midpoint(u,w) - v)) =
            (&1 + e) / &2`,
  REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR; moi_sa2_ca; moi_sa2_cb; moi_sa2_det;
              midpoint; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

let MOI_SA2_IN_TRIANGLE = prove
 (`!u v w z:real^2.
        ~collinear{u,v,w} /\
        &0 <= moi_sa2_ca u v w z /\ &0 <= moi_sa2_cb u v w z /\
        moi_sa2_ca u v w z + moi_sa2_cb u v w z <= &1
        ==> z IN convex hull {u,v,w}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`&1 - moi_sa2_ca u v w z - moi_sa2_cb u v w (z:real^2)`;
    `moi_sa2_ca u v w (z:real^2)`; `moi_sa2_cb u v w (z:real^2)`] THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [SPEC `z:real^2` (MATCH_MP MOI_SA2_COORDS th)]) THEN
  VECTOR_ARITH_TAC);;

let MOI_SA2_TRIANGLE_COORDS = prove
 (`!u v w z:real^2.
        ~collinear{u,v,w} /\ z IN convex hull {u,v,w}
        ==> &0 <= moi_sa2_ca u v w z /\ &0 <= moi_sa2_cb u v w z /\
            moi_sa2_ca u v w z + moi_sa2_cb u v w z <= &1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `a % u + b % v + c % w:real^2 = u + b % (v - u) + c % (w - u)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `a = &1 - b - c` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sa2_ca u v w (u + b % (v - u) + c % (w - u)) = b /\
    moi_sa2_cb u v w (u + b % (v - u) + c % (w - u)) = c`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `~collinear{u:real^2,v,w}` THEN
    REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR; moi_sa2_ca; moi_sa2_cb; moi_sa2_det;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_FIELD;
    ASM_REAL_ARITH_TAC]);;
let MOI_SA2_QUAD_HALFPLANES = prove
 (`!u v w e z:real^2.
        ~collinear{u,v,w} /\ &0 <= e /\ z IN moi_sa2_quad u v w e
        ==> &0 <= (&1 + e) * moi_sa2_ca u v w z +
                  (&2 * e) * moi_sa2_cb u v w z /\
            &0 <= e * moi_sa2_ca u v w z +
                  (&2 * (&1 + e)) * moi_sa2_cb u v w z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k1 k2. &0 <= k1 * moi_sa2_ca u v w u + k2 * moi_sa2_cb u v w (u:real^2) /\
            &0 <= k1 * moi_sa2_ca u v w (v + e % (v - midpoint(u,w))) +
                  k2 * moi_sa2_cb u v w (v + e % (v - midpoint(u,w))) /\
            &0 <= k1 * moi_sa2_ca u v w w + k2 * moi_sa2_cb u v w w /\
            &0 <= k1 * moi_sa2_ca u v w (midpoint(u,w) + e % (midpoint(u,w) - v)) +
                  k2 * moi_sa2_cb u v w (midpoint(u,w) + e % (midpoint(u,w) - v))
            ==> moi_sa2_quad u v w e SUBSET
                {z:real^2 | &0 <= k1 * moi_sa2_ca u v w z +
                                  k2 * moi_sa2_cb u v w z}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[moi_sa2_quad] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[convex; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `s:real`; `t:real`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_SA2_CA_AFFINE; MOI_SA2_CB_AFFINE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= s * (k1 * a1 + k2 * b1) + t * (k1 * a2 + k2 * b2) /\
      k1 * (s * a1 + t * a2) + k2 * (s * b1 + t * b2) =
      s * (k1 * a1 + k2 * b1) + t * (k1 * a2 + k2 * b2)
      ==> &0 <= k1 * (s * a1 + t * a2) + k2 * (s * b1 + t * b2)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SA2_COORD_VALUES) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&1 + e`; `&2 * e`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `&2 * (&1 + e)`])] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM SET_TAC[]);;
let MOI_SA2_QUAD_SYM = prove
 (`!u v w:real^2 e. moi_sa2_quad u v w e = moi_sa2_quad w v u e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sa2_quad] THEN
  SUBST1_TAC(ISPECL [`w:real^2`; `u:real^2`] MIDPOINT_SYM) THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let MOI_SA2_MIDPOINT_IN_TRIANGLE = prove
 (`!u v w:real^2. midpoint(u,w) IN convex hull {u,v,w}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(SET_RULE `!t. (x:real^2) IN t /\ t SUBSET s ==> x IN s`) THEN
  EXISTS_TAC `segment[u:real^2,w]` THEN
  REWRITE_TAC[MIDPOINT_IN_SEGMENT; SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let MOI_SA2_QUAD_NEAR = prove
 (`!u v w:real^2 e z.
        &0 <= e /\ z IN moi_sa2_quad u v w e
        ==> ?t. t IN convex hull {u,v,w} /\
                dist(z,t) <= e * norm(v - midpoint(u,w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_sa2_quad u v w e SUBSET
    {x + y:real^2 | x IN convex hull {u,v,w} /\
                    y IN cball(vec 0,e * norm(v - midpoint(u,w)))}`
  MP_TAC THENL
   [REWRITE_TAC[moi_sa2_quad] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[CONVEX_SUMS; CONVEX_CONVEX_HULL; CONVEX_CBALL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `(u:real^2) IN convex hull {u,v,w} /\ v IN convex hull {u,v,w} /\
      w IN convex hull {u,v,w} /\ midpoint(u,w) IN convex hull {u,v,w}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MOI_SA2_MIDPOINT_IN_TRIANGLE] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `vec 0 IN cball(vec 0:real^2,e * norm(v - midpoint(u,w)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[CENTRE_IN_CBALL] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u:real^2`; `vec 0:real^2`] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC [`v:real^2`; `e % (v - midpoint(u:real^2,w))`] THEN
      ASM_REWRITE_TAC[IN_CBALL_0; NORM_MUL; real_abs; REAL_LE_REFL];
      MAP_EVERY EXISTS_TAC [`w:real^2`; `vec 0:real^2`] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RID];
      MAP_EVERY EXISTS_TAC
       [`midpoint(u:real^2,w)`; `e % (midpoint(u:real^2,w) - v)`] THEN
      ASM_REWRITE_TAC[IN_CBALL_0; NORM_MUL; real_abs] THEN
      MESON_TAC[NORM_SUB; REAL_LE_REFL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[dist] THEN
    UNDISCH_TAC `y IN cball(vec 0:real^2,e * norm(v - midpoint(u,w)))` THEN
    REWRITE_TAC[IN_CBALL_0] THEN
    REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^2 = y`]]);;
let MOI_SA2_POS_NEG_MUL = prove
 (`!t c. &0 < t /\ c < &0 ==> t * c < &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`t:real`; `--c:real`] REAL_LT_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SA2_QUAD_CONE = prove
 (`!u v w x:real^2.
        ~collinear{u,v,w} /\
        segment[u,x] INTER convex hull {u,v,w} SUBSET {u}
        ==> ?e0. &0 < e0 /\
                 !e. &0 < e /\ e < e0
                     ==> segment[u,x] INTER moi_sa2_quad u v w e SUBSET {u}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:real^2 = u` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[SEGMENT_REFL; REAL_LT_01] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = moi_sa2_ca u v w (x:real^2)` THEN
  ABBREV_TAC `b = moi_sa2_cb u v w (x:real^2)` THEN
  SUBGOAL_THEN `a < &0 \/ b < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < a + b + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `?t. &0 < t /\ t * a + t * b <= &1 /\ t <= &1 /\
                      &0 <= t * a /\ &0 <= t * b`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `inv(a + b + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_INV; REAL_LE_MUL; REAL_LE_INV; REAL_LT_IMP_LE;
                   REAL_INV_LE_1;
                   REAL_ARITH `&0 <= a /\ &0 <= b ==> &1 <= a + b + &1`] THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `u + t % (x - u) IN segment[u:real^2,x] INTER convex hull {u,v,w}`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC MOI_SA2_IN_TRIANGLE THEN
        ASM_REWRITE_TAC[MOI_SA2_CA_RAY]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `(z:real^2) IN s ==> s SUBSET {u} ==> z = u`)) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `u + t % (x - u):real^2 = u <=>
                                  t % (x - u) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs a + &2 * abs b + &1` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e z:real^2. &0 < e /\ z IN segment[u,x] /\ z IN moi_sa2_quad u v w e
                 ==> ?t. &0 <= t /\ t <= &1 /\ z = u + t % (x - u) /\
                         &0 <= t * ((&1 + e) * a + (&2 * e) * b) /\
                         &0 <= t * (e * a + (&2 * (&1 + e)) * b)`
  (LABEL_TAC "seg") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^2) IN segment[u,x]` THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_THEN `z:real^2 = (&1 - t) % u + t % x` SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH
     `(&1 - t) % u + t % x:real^2 = u + t % (x - u)`]) THEN
    EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `(&1 - t) % u + t % x:real^2 = u + t % (x - u)`] THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`;
                   `u + t % (x - u):real^2`] MOI_SA2_QUAD_HALFPLANES) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; MOI_SA2_CA_RAY] THEN
    MATCH_MP_TAC(TAUT `(p <=> p') /\ (q <=> q') ==> p /\ q ==> p' /\ q'`) THEN
    CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> e * a <= e * abs a /\ e * b <= e * abs b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [EXISTS_TAC `--a / (abs a + &2 * abs b + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `a < &0 ==> &0 < --a`] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(&1 + e) * a + (&2 * e) * b < &0` ASSUME_TAC THENL
     [UNDISCH_TAC `e < --a / (abs a + &2 * abs b + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC];
    EXISTS_TAC `--(&2 * b) / (abs a + &2 * abs b + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `b < &0 ==> &0 < --(&2 * b)`] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `e * a + (&2 * (&1 + e)) * b < &0` ASSUME_TAC THENL
     [UNDISCH_TAC `e < --(&2 * b) / (abs a + &2 * abs b + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  USE_THEN "seg" (MP_TAC o SPECL [`e:real`; `z:real^2`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `u + t % (x - u):real^2 = u <=>
                                t % (x - u) = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= t /\ ~(&0 < t) ==> t = &0`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_MESON_TAC[MOI_SA2_POS_NEG_MUL; REAL_NOT_LE]);;
let MOI_SA2_QUAD_CONE_W = prove
 (`!u v w x:real^2.
        ~collinear{u,v,w} /\
        segment[w,x] INTER convex hull {u,v,w} SUBSET {w}
        ==> ?e0. &0 < e0 /\
                 !e. &0 < e /\ e < e0
                     ==> segment[w,x] INTER moi_sa2_quad u v w e SUBSET {w}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MOI_SA2_QUAD_SYM] THEN
  MATCH_MP_TAC MOI_SA2_QUAD_CONE THEN
  SUBGOAL_THEN `{w:real^2,v,u} = {u,v,w}` SUBST1_TAC THENL
   [SET_TAC[]; ASM_REWRITE_TAC[]]);;

let MOI_SA2_QUAD_SEGMENT = prove
 (`!u v w x y:real^2.
        ~collinear{u,v,w} /\
        segment[x,y] INTER convex hull {u,v,w} SUBSET {u,w}
        ==> ?e0. &0 < e0 /\
                 !e. &0 < e /\ e < e0
                     ==> segment[x,y] INTER moi_sa2_quad u v w e SUBSET {u,w}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(u:real^2 = w)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~collinear{w:real^2,v,w}` THEN
    REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^2) IN segment[x,y] /\ w IN segment[x,y])`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `midpoint(u:real^2,w) IN segment[x,y] INTER convex hull {u,v,w}`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER; MOI_SA2_MIDPOINT_IN_TRIANGLE] THEN
      MATCH_MP_TAC(SET_RULE `!t. (z:real^2) IN t /\ t SUBSET s ==> z IN s`) THEN
      EXISTS_TAC `segment[u:real^2,w]` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT; SUBSET_SEGMENT];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `~(z = u) /\ ~(z = w) /\ s SUBSET {u:real^2,w} ==> (z IN s ==> F)`) THEN
    ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT];
    ALL_TAC] THEN
  ASM_CASES_TAC `(u:real^2) IN segment[x,y]` THENL
   [SUBGOAL_THEN
     `segment[u:real^2,x] INTER convex hull {u,v,w} SUBSET {u} /\
      segment[u:real^2,y] INTER convex hull {u,v,w} SUBSET {u}`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `segment[u:real^2,x] SUBSET segment[x,y] /\
                    segment[u:real^2,y] SUBSET segment[x,y]`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `x:real^2`]
      MOI_SA2_QUAD_CONE) THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `y:real^2`]
      MOI_SA2_QUAD_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `segment[x:real^2,y] = segment[u,x] UNION segment[u,y]`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`x:real^2`; `u:real^2`; `y:real^2`] UNION_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SEGMENT_SYM];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^2) IN segment[x,y]` THENL
   [SUBGOAL_THEN
     `segment[w:real^2,x] INTER convex hull {u,v,w} SUBSET {w} /\
      segment[w:real^2,y] INTER convex hull {u,v,w} SUBSET {w}`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `segment[w:real^2,x] SUBSET segment[x,y] /\
                    segment[w:real^2,y] SUBSET segment[x,y]`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `x:real^2`]
      MOI_SA2_QUAD_CONE_W) THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `y:real^2`]
      MOI_SA2_QUAD_CONE_W) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `segment[x:real^2,y] = segment[w,x] UNION segment[w,y]`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`x:real^2`; `w:real^2`; `y:real^2`] UNION_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SEGMENT_SYM];
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^2,y] INTER convex hull {u,v,w} = {}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[x:real^2,y]`; `convex hull {u:real^2,v,w}`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_SEGMENT; COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL;
               FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / (norm(v - midpoint(u:real^2,w)) + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LE;
               REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`; `z:real^2`]
    MOI_SA2_QUAD_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `t:real^2`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e * norm(v - midpoint(u:real^2,w))` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `e < d / (norm(v - midpoint(u:real^2,w)) + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; NORM_POS_LE;
               REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
  MP_TAC(ISPEC `v - midpoint(u:real^2,w)` NORM_POS_LE) THEN
  SUBGOAL_THEN `e * norm(v - midpoint(u:real^2,w)) <=
                e * (norm(v - midpoint(u,w)) + &1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;
let MOI_SA2_EAR_GEOM = prove
 (`!u v w (c:(real^2->bool)->bool) W.
        ~collinear{u,v,w} /\ open W /\ convex hull {u,v,w} SUBSET W /\
        FINITE c /\ (!k. k IN c ==> ?x y. k = segment[x,y]) /\
        UNIONS c INTER convex hull {u,v,w} SUBSET {u,w}
        ==> ?e. &0 < e /\ moi_sa2_quad u v w e SUBSET W /\
                UNIONS c INTER moi_sa2_quad u v w e SUBSET {u,w}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?e0. &0 < e0 /\
         !e. &0 < e /\ e < e0
             ==> UNIONS c INTER moi_sa2_quad u v w e SUBSET {u:real^2,w}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS c INTER convex hull {u:real^2,v,w} SUBSET {u,w}` THEN
    UNDISCH_TAC `!k. k IN c ==> ?x y:real^2. k = segment[x,y]` THEN
    UNDISCH_TAC `FINITE (c:(real^2->bool)->bool)` THEN
    SPEC_TAC(`c:(real^2->bool)->bool`,`c:(real^2->bool)->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REPEAT DISCH_TAC THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; UNIONS_0] THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^2->bool`; `c:(real^2->bool)->bool`] THEN
    REWRITE_TAC[FORALL_IN_INSERT; UNIONS_INSERT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `y:real^2`
      SUBST_ALL_TAC)) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `x:real^2`; `y:real^2`]
      MOI_SA2_QUAD_SEGMENT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ih" (MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (is_forall o concl))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {u:real^2,v,w}`; `(:real^2) DIFF W`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT; FINITE_INSERT;
               FINITE_EMPTY; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < d / (norm(v - midpoint(u:real^2,w)) + &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LE;
                 REAL_ARITH `&0 <= x ==> &0 < x + &1`];
    ALL_TAC] THEN
  EXISTS_TAC `min e0 (d / (norm(v - midpoint(u:real^2,w)) + &1)) / &2` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF] THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF] THEN ASM_REAL_ARITH_TAC] THEN
  ABBREV_TAC `e = min e0 (d / (norm(v - midpoint(u:real^2,w)) + &1)) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ e * (norm(v - midpoint(u:real^2,w)) + &1) < d`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_SIMP_TAC[REAL_LT_MIN; REAL_HALF] THEN
    SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_POS_LE;
             REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`; `z:real^2`]
    MOI_SA2_QUAD_NEAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^2`; `z:real^2`] o
    check (fun th -> is_forall(concl th) &&
                     length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[TAUT `(p ==> F) <=> ~p`; REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e * norm(v - midpoint(u:real^2,w))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `e * (norm(v - midpoint(u:real^2,w)) + &1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The conewise PL homeomorphism that removes an ear.  On the                *)
(* thin quadrilateral Q it is the cone map from v over the frontier of Q to  *)
(* the cone from the midpoint of [u,w] (Moise p.28, Case 2, with Thm 3.1);  *)
(* it is the identity off the interior of Q.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_LP_POLYHEDRON = prove
 (`!s:real^N->bool. polyhedron s ==> locally_polyhedral s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{s INTER interval[x - vec 1:real^N,x + vec 1]}`;
    `interval(x - vec 1:real^N,x + vec 1)`] THEN
  REWRITE_TAC[FINITE_SING; OPEN_INTERVAL; FORALL_IN_INSERT; NOT_IN_EMPTY;
              UNIONS_1] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`x - vec 1:real^N`; `x + vec 1:real^N`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN SET_TAC[];
    ASM_SIMP_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON; POLYHEDRON_INTER;
                 POLYHEDRON_INTERVAL; BOUNDED_INTER; BOUNDED_INTERVAL];
    SET_TAC[]]);;

let MOI_SA2_LP_UNIONS = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ (!k. k IN c ==> closed k /\ locally_polyhedral k)
        ==> locally_polyhedral (UNIONS c)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [REWRITE_TAC[locally_polyhedral; NOT_IN_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `c:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun th' ->
    MP_TAC(MATCH_MP th (CONJUNCT2 th')) THEN ASSUME_TAC th')) THEN
  DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed(UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_SA2_LP_COMPLEMENT_INTERIOR = prove
 (`!s:real^N->bool.
        polyhedron s ==> locally_polyhedral ((:real^N) DIFF interior s)`,
  GEN_TAC THEN REWRITE_TAC[polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[INTERIOR_FINITE_INTERS] THEN
  SUBGOAL_THEN
   `(:real^N) DIFF INTERS (IMAGE interior f) =
    UNIONS (IMAGE (\h. (:real^N) DIFF interior h) f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_INTERS; IN_UNIONS;
                FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SA2_LP_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE] THEN
  SUBGOAL_THEN `(:real^N) DIFF {x | a dot x < b} = {x | a dot x >= b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[CLOSED_HALFSPACE_GE; MOI_SA2_LP_POLYHEDRON;
           POLYHEDRON_HALFSPACE_GE]);;

let MOI_SA2_PLH_EXTEND_ID = prove
 (`!k:real^N->bool f g.
        polytope k /\ pl_homeomorphism (k,k) (f,g) /\
        (!x. x IN k /\ ~(x IN interior k) ==> f x = x)
        ==> pl_homeomorphism ((:real^N),(:real^N))
              ((\x. if x IN k then f x else x),(\x. if x IN k then g x else x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF interior k`;
                 `k:real^N->bool`; `(:real^N) DIFF interior k`;
                 `f:real^N->real^N`; `g:real^N->real^N`;
                 `(\x:real^N. x)`; `(\x:real^N. x)`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  SUBGOAL_THEN `k UNION ((:real^N) DIFF interior k) = (:real^N)`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED; GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_SIMP_TAC[MOI_SA2_LP_COMPLEMENT_INTERIOR; POLYTOPE_IMP_POLYHEDRON];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = x) ==> IMAGE f s = (s:real^N->bool)`) THEN
  REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[]);;

let MOI_SA2_POLYTOPE_RF_POLYHEDRON = prove
 (`!k:real^N->bool. polytope k ==> pl_polyhedron (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{f:real^N->bool | f facet_of k}` THEN
  ASM_SIMP_TAC[FINITE_POLYTOPE_FACETS; IN_ELIM_THM;
               RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; facet_of]);;

let MOI_SA2_CONE_PLH = prove
 (`!k:real^N->bool v m.
        polytope k /\ v IN interior k /\ m IN interior k
        ==> ?h g. pl_homeomorphism (k,k) (h,g) /\
                  (!x. x IN relative_frontier k ==> h x = x) /\
                  (!x r. x IN relative_frontier k /\ &0 <= r /\ r <= &1
                         ==> h (v + r % (x - v)) = m + r % (x - m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `relative_interior k = interior(k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(k:real^N->bool) /\ compact k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier k:real^N->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN STRIP_TAC THEN
    UNDISCH_TAC `(v:real^N) IN interior k` THEN
    ASM_REWRITE_TAC[INTERIOR_EMPTY; INTERIOR_SING; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron(relative_frontier k:real^N->bool)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[MOI_SA2_POLYTOPE_RF_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k,relative_frontier k)
                     ((\x:real^N. x),(\x. x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b:real^N.
      b IN interior k
      ==> ~(b IN relative_frontier k) /\
          (!x y. x IN relative_frontier k /\ y IN relative_frontier k /\
                 y IN segment[b,x] ==> y = x) /\
          UNIONS {segment[b,x] | x IN relative_frontier k} = k`
  (LABEL_TAC "rays") THENL
   [X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[relative_frontier; IN_DIFF];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `b:real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "rays" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(v:real^N) IN interior k`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `(m:real^N) IN interior k`))) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`;
                 `relative_frontier k:real^N->bool`;
                 `v:real^N`; `m:real^N`; `(\x:real^N. x)`; `(\x:real^N. x)`]
    MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`moi_con_conemap (relative_frontier k) (v:real^N) (m:real^N) (\x. x)`;
    `moi_con_conemap (relative_frontier k) (m:real^N) (v:real^N) (\x. x)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `v:real^N`; `m:real^N`;
                 `(\x:real^N. x)`; `x:real^N`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[]);;
let MOI_SA2_QUAD_NOT_INTERIOR = prove
 (`!u v w:real^2 e.
        ~collinear{u,v,w} /\ &0 < e
        ==> ~(u IN interior(moi_sa2_quad u v w e))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(v:real^2 = u)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~collinear{u:real^2,u,w}` THEN
    REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(v - u:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `?s. &0 < s /\ s * norm(v - u:real^2) < r` STRIP_ASSUME_TAC
  THENL
   [EXISTS_TAC `r / (&2 * norm(v - u:real^2))` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + --s % (v - u:real^2) IN moi_sa2_quad u v w e` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `u - (u + x):real^2 = --x`] THEN
    ASM_REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_NEG] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`;
                 `u + --s % (v - u:real^2)`] MOI_SA2_QUAD_HALFPLANES) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; MOI_SA2_CA_RAY; MOI_SA2_COORD_VALUES] THEN
  REWRITE_TAC[TAUT `(p /\ q ==> F) <=> ~(p /\ q)`] THEN
  MATCH_MP_TAC(TAUT `~p ==> ~(p /\ q)`) THEN
  REWRITE_TAC[REAL_NOT_LE; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC MOI_SA2_POS_NEG_MUL THEN ASM_REAL_ARITH_TAC);;
let MOI_SA2_QUAD_FACTS = prove
 (`!u v w:real^2 e.
        ~collinear{u,v,w} /\ &0 < e
        ==> polytope(moi_sa2_quad u v w e) /\
            convex(moi_sa2_quad u v w e) /\
            compact(moi_sa2_quad u v w e) /\
            v IN interior(moi_sa2_quad u v w e) /\
            midpoint(u,w) IN interior(moi_sa2_quad u v w e) /\
            convex hull {u,v,w} SUBSET moi_sa2_quad u v w e /\
            ~(u IN interior(moi_sa2_quad u v w e)) /\
            ~(w IN interior(moi_sa2_quad u v w e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope(moi_sa2_quad u v w e)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sa2_quad] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT] THEN
  ASM_SIMP_TAC[MOI_SA2_QUAD_NOT_INTERIOR] THEN
  SUBGOAL_THEN `~collinear{w:real^2,v,u}` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{w:real^2,v,u} = {u,v,w}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w IN interior(moi_sa2_quad u v w e))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MOI_SA2_QUAD_SYM] THEN
    ASM_SIMP_TAC[MOI_SA2_QUAD_NOT_INTERIOR];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(u:real^2) IN moi_sa2_quad u v w e /\ w IN moi_sa2_quad u v w e /\
    v + e % (v - midpoint(u,w)) IN moi_sa2_quad u v w e /\
    midpoint(u,w) + e % (midpoint(u,w) - v) IN moi_sa2_quad u v w e`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_sa2_quad] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_INC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v IN interior(moi_sa2_quad u v w e)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!t. (x:real^2) IN t /\ t SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `interior(convex hull {u:real^2, v + e % (v - midpoint(u,w)), w})` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[moi_sa2_quad] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]] THEN
    SUBGOAL_THEN `~collinear{u:real^2, v + e % (v - midpoint(u,w)), w}`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `moi_sa2_det ((v + e % (v - midpoint(u,w))) - u) (w - u) =
        (&1 + e) * moi_sa2_det (v - u) ((w:real^2) - u)`
      ASSUME_TAC THENL
       [REWRITE_TAC[moi_sa2_det; midpoint; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~collinear{u:real^2,v,w}` THEN
      ASM_REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR; REAL_ENTIRE; DE_MORGAN_THM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`e / (&2 * (&1 + e))`; `inv(&1 + e)`; `e / (&2 * (&1 + e))`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_INV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH;
                 REAL_ARITH `&0 < e ==> &0 < &1 + e`] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; midpoint] THEN
    UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`moi_sa2_quad u v w e`; `v:real^2`;
                   `midpoint(u:real^2,w) + e % (midpoint(u,w) - v)`]
      IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^2) IN s ==> s SUBSET t ==> x IN t`) THEN
    SUBGOAL_THEN `~(v:real^2 = midpoint(u,w))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`]
        MOI_SA2_COORD_VALUES) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `v = m + e % (m - v) <=> (&1 + e) % (v - m):real^2 = vec 0`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `inv(&1 + e)` THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_ARITH `&0 < e ==> &0 < &1 + e`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[moi_sa2_quad] THEN MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
    ASM_REWRITE_TAC[GSYM moi_sa2_quad];
    MATCH_MP_TAC HULL_INC THEN SET_TAC[]]);;
let MOI_SA2_IMAGE_SEGMENT_RAY = prove
 (`!(f:real^N->real^N) a b c.
        (!r. &0 <= r /\ r <= &1 ==> f (a + r % (b - a)) = c + r % (b - c))
        ==> IMAGE f (segment[a,b]) = segment[c,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - t) % a + t % b:real^N = a + t % (b - a)`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a + t % (b - a):real^N` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

let MOI_SA2_EAR_PLH_GEN = prove
 (`!Q u v w:real^2.
        polytope Q /\ v IN interior Q /\ midpoint(u,w) IN interior Q /\
        u IN Q /\ w IN Q /\ ~(u IN interior Q) /\ ~(w IN interior Q)
        ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
                  (!x. ~(x IN interior Q) ==> h x = x) /\
                  IMAGE h (segment[u,v] UNION segment[v,w]) = segment[u,w]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:real^2->bool`; `v:real^2`; `midpoint(u:real^2,w)`]
    MOI_SA2_CONE_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^2->real^2` (X_CHOOSE_THEN `g0:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex(Q:real^2->bool) /\ compact Q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN Q /\ ~(x IN interior Q) ==> x IN relative_frontier Q`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN
    SUBGOAL_THEN `relative_interior Q = interior(Q:real^2->bool)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2) IN Q` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^2,u] SUBSET Q /\ segment[v,w] SUBSET Q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^2) IN relative_frontier Q /\ w IN relative_frontier Q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. if x IN Q then h0 x else x`;
    `\x:real^2. if x IN Q then g0 x else x`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SA2_PLH_EXTEND_ID THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^2,v] = segment[v,u]` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. if x IN Q then h0 x else x)
          (segment[v,u] UNION segment[v,w]) =
    IMAGE h0 (segment[v,u] UNION segment[v,w])`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!z. z IN s ==> f z = g z) ==> IMAGE f s = IMAGE (g:real^2->real^2) s`) THEN
    REWRITE_TAC[IN_UNION] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  MP_TAC(ISPECL [`h0:real^2->real^2`; `v:real^2`; `u:real^2`;
                 `midpoint(u:real^2,w)`] MOI_SA2_IMAGE_SEGMENT_RAY) THEN
  MP_TAC(ISPECL [`h0:real^2->real^2`; `v:real^2`; `w:real^2`;
                 `midpoint(u:real^2,w)`] MOI_SA2_IMAGE_SEGMENT_RAY) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBST1_TAC(ISPECL [`midpoint(u:real^2,w)`; `u:real^2`]
    (CONJUNCT1 SEGMENT_SYM)) THEN
  MATCH_MP_TAC UNION_SEGMENT THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT]);;

let MOI_SA2_EAR_PLH = prove
 (`!u v w:real^2 e.
        ~collinear{u,v,w} /\ &0 < e
        ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
                  (!x. ~(x IN interior(moi_sa2_quad u v w e)) ==> h x = x) /\
                  IMAGE h (segment[u,v] UNION segment[v,w]) = segment[u,w]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_QUAD_FACTS) THEN
  MATCH_MP_TAC MOI_SA2_EAR_PLH_GEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
    check (fun th -> is_binary "SUBSET" (concl th))) THEN
  MATCH_MP_TAC HULL_INC THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Removing an ear of a polygon by a PL homeomorphism of the                 *)
(* plane that is the identity off a given open set (Moise Thm 3.4, Case 2), *)
(* and the induction on the number of vertices (Moise Thms 3.4 and 3.7).    *)
(* ------------------------------------------------------------------------- *)

(* Plane versions of MOI_SCD_PL_HOMEO_ID, MOI_SCD_PL_HOMEO_UNIV and         *)
(* MOI_SCD_FIX_OFF of pc_moi_sch3_stmt.ml, which are stated in real^3.      *)

let MOI_SA2_PLH_ID = prove
 (`pl_homeomorphism ((:real^2),(:real^2)) ((\x. x),(\x. x))`,
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
              GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]);;

let MOI_SA2_PLH_UNIV = prove
 (`!(f:real^2->real^2) g.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g)
     ==> homeomorphism ((:real^2),(:real^2)) (f,g) /\
         (!x. g (f x) = x) /\ (!y. f (g y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SA2_FIX_OFF = prove
 (`!(f:real^2->real^2) g w s.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
     (!x. ~(x IN w) ==> f x = x)
     ==> (!x. ~(x IN w) ==> g x = x) /\
         (s SUBSET w ==> IMAGE f s SUBSET w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^2) x = x` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let MOI_SA2_REGION_IMAGE = prove
 (`!(f:real^2->real^2) g p q.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
     IMAGE f (path_image(polygonal_path p)) = path_image(polygonal_path q)
     ==> IMAGE f (moi_sa2_region p) = moi_sa2_region q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sa2_region; IMAGE_UNION] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`;
                 `path_image(polygonal_path(p:(real^2)list))`]
    MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* Removing the ear at the second vertex v of CONS u (CONS v (CONS w l)).   *)

let MOI_SA2_EAR_REMOVE = prove
 (`!u v w (l:(real^2)list) W.
     simple_path(polygonal_path(CONS u (CONS v (CONS w l)))) /\
     pathfinish(polygonal_path(CONS u (CONS v (CONS w l)))) =
     pathstart(polygonal_path(CONS u (CONS v (CONS w l)))) /\
     5 <= LENGTH(CONS u (CONS v (CONS w l))) /\
     ~collinear{u,v,w} /\
     convex hull {u,v,w} SUBSET moi_sa2_region (CONS u (CONS v (CONS w l))) /\
     path_image(polygonal_path(CONS u (CONS v (CONS w l)))) INTER
     convex hull {u,v,w} = segment[u,v] UNION segment[v,w] /\
     open W /\ moi_sa2_region (CONS u (CONS v (CONS w l))) SUBSET W
     ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
               (!x. ~(x IN W) ==> h x = x) /\
               simple_path(polygonal_path(CONS u (CONS w l))) /\
               pathfinish(polygonal_path(CONS u (CONS w l))) =
               pathstart(polygonal_path(CONS u (CONS w l))) /\
               IMAGE h (path_image(polygonal_path(CONS u (CONS v (CONS w l))))) =
               path_image(polygonal_path(CONS u (CONS w l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l:(real^2)list`]
    MOI_SA2_EL1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= LENGTH(CONS (w:real^2) l)` ASSUME_TAC THENL
   [UNDISCH_TAC `5 <= LENGTH(CONS (u:real^2) (CONS v (CONS w l)))` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS u (CONS v (CONS w l))) =
    linepath(u,v) ++ (linepath(v,w) ++ polygonal_path(CONS (w:real^2) l)) /\
    polygonal_path(CONS u (CONS w l)) =
    linepath(u,w) ++ polygonal_path(CONS (w:real^2) l)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^2`; `CONS (v:real^2) (CONS w l)`]
      MOI_SA2_PP_CONS) THEN
    MP_TAC(ISPECL [`v:real^2`; `CONS (w:real^2) l`] MOI_SA2_PP_CONS) THEN
    MP_TAC(ISPECL [`u:real^2`; `CONS (w:real^2) l`] MOI_SA2_PP_CONS) THEN
    ASM_REWRITE_TAC[HD] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN ANTS_TAC THENL
     [UNDISCH_TAC `2 <= LENGTH(CONS (w:real^2) l)` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart(polygonal_path(CONS (w:real^2) l)) = w /\
    pathfinish(polygonal_path(CONS (w:real^2) l)) = u`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                    NOT_CONS_NIL; HD; LAST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `arc(polygonal_path(CONS (w:real^2) l)) /\
    (segment[u,v] UNION segment[v,w]) INTER
    path_image(polygonal_path(CONS w l)) SUBSET {u,w}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `simple_path(polygonal_path(CONS u (CONS v (CONS (w:real^2) l))))` THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SIMPLE_PATH_ASSOC o
      lhand o snd) THEN
    ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATHSTART_JOIN] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH;
                 PATH_IMAGE_LINEPATH] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS u (CONS v (CONS w l)))) =
    (segment[u,v] UNION segment[v,w]) UNION
    path_image(polygonal_path(CONS (w:real^2) l))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH;
                 PATHSTART_JOIN; PATH_IMAGE_LINEPATH] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS (w:real^2) l)) INTER convex hull {u,v,w}
    SUBSET {u,w}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image(polygonal_path(CONS u (CONS v (CONS (w:real^2) l)))) INTER
       convex hull {u,v,w} = segment[u,v] UNION segment[v,w]`;
      `(segment[u,v] UNION segment[v,w]) INTER
       path_image(polygonal_path(CONS w l)) SUBSET {u:real^2,w}`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^2,w] SUBSET convex hull {u,v,w}` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `simple_path(polygonal_path(CONS u (CONS w l))) /\
    pathfinish(polygonal_path(CONS u (CONS w l))) =
    pathstart(polygonal_path(CONS u (CONS (w:real^2) l)))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `CONS (w:real^2) l` MOI_SA2_PATH_SEGMENTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`;
                 `c:(real^2->bool)->bool`; `W:real^2->bool`] MOI_SA2_EAR_GEOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS];
      UNDISCH_TAC
       `path_image(polygonal_path(CONS (w:real^2) l)) INTER
        convex hull {u,v,w} SUBSET {u,w}` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS (w:real^2) l)) INTER moi_sa2_quad u v w e
    SUBSET {u,w}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_THEN `path_image(polygonal_path(CONS (w:real^2) l)) = UNIONS c`
    (K ALL_TAC) THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`]
    MOI_SA2_QUAD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2`; `v:real^2`; `w:real^2`; `e:real`]
    MOI_SA2_EAR_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`h:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `moi_sa2_quad u v w e` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN path_image(polygonal_path(CONS w l)) ==> h x = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `moi_sa2_quad u v w e` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(linepath(u,w) ++ polygonal_path(CONS (w:real^2) l)) =
    segment[u,w] UNION path_image(polygonal_path(CONS w l))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  UNDISCH_THEN
   `path_image(polygonal_path(CONS u (CONS v (CONS w l)))) =
    (segment[u,v] UNION segment[v,w]) UNION
    path_image(polygonal_path(CONS (w:real^2) l))` SUBST1_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE h s = t /\ (!x. x IN r ==> h x = x)
    ==> IMAGE h (s UNION r) = t UNION (r:real^2->bool)`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The induction on the number of vertices (Moise Thm 3.4 with               *)
(* the support condition of Thm 3.7): a polygon whose closed region lies in *)
(* an open set W is carried onto the boundary of a triangle by a PL         *)
(* homeomorphism of the plane that is the identity off W.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_LIST3 = prove
 (`!q:A list. 3 <= LENGTH q ==> ?x y z l. q = CONS x (CONS y (CONS z l))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(q:A list) = SUC(SUC(SUC(LENGTH q - 3)))` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_EQ_CONS] THEN MESON_TAC[]);;

let MOI_SA2_AMB2_POLY = prove
 (`!n (p:(real^2)list) W.
     LENGTH p = n /\ simple_path(polygonal_path p) /\
     pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
     open W /\ moi_sa2_region p SUBSET W
     ==> ?t h g. &2 simplex t /\
                 pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
                 (!x. ~(x IN W) ==> h x = x) /\
                 IMAGE h (path_image(polygonal_path p)) = relative_frontier t`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:(real^2)list`; `W:real^2->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `5 <= LENGTH(p:(real^2)list)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `LENGTH(p:(real^2)list) = 4` MP_TAC THENL
     [MP_TAC(ISPEC `p:(real^2)list` MOI_SA2_LENGTH_GE_4) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_SA2_LENGTH_4) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `d:real^2 = a` SUBST_ALL_TAC THENL
     [UNDISCH_TAC
       `pathfinish(polygonal_path [a;b;c;d]) =
        pathstart(polygonal_path [a:real^2;b;c;d])` THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                  NOT_CONS_NIL; HD; LAST];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SA2_TRIANGLE_NONCOLLINEAR) THEN
    MAP_EVERY EXISTS_TAC
     [`convex hull {a:real^2,b,c}`; `\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[MOI_SA2_PLH_ID; IMAGE_ID; MOI_SA2_TRIANGLE_PATH_IMAGE] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[]] THEN
  MP_TAC(ISPEC `p:(real^2)list` MOI_SA2_HAS_EDGE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a0:real^2`; `b0:real^2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`LENGTH(p:(real^2)list)`; `p:(real^2)list`; `a0:real^2`;
                 `b0:real^2`] MOI_SA2_EAR_EXISTS) THEN
  ASM_REWRITE_TAC[moi_sa2_ear] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p:(real^2)list`; `z:real^2`] MOI_SA2_ROTATE1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SA2_EDGE_IMP_MEM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^2)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `q:(real^2)list` MOI_SA2_LIST3) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `z':real^2`; `y:real^2`; `l:(real^2)list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `z':real^2 = z` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `EL 1 (CONS x (CONS z' (CONS y l))) = (z:real^2)` THEN
    REWRITE_TAC[num_CONV `1`; EL; HD; TL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2`; `z:real^2`; `y:real^2`; `l:(real^2)list`]
    MOI_SA2_EL1_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `moi_sa2_region (CONS x (CONS z (CONS y l))) = moi_sa2_region p`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_sa2_region]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a = x /\ b = y) \/ (a = y /\ (b:real^2) = x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(a = x \/ a = y) /\ (b = x \/ (b:real^2) = y)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SA2_EDGE_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a:real^2 = b)` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~collinear{b:real^2,z,b}` THEN
      REWRITE_TAC[INSERT_AC; COLLINEAR_2];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~collinear{x:real^2,z,y} /\
    convex hull {x,z,y} SUBSET moi_sa2_region (CONS x (CONS z (CONS y l))) /\
    path_image(polygonal_path(CONS x (CONS z (CONS y l)))) INTER
    convex hull {x,z,y} = segment[x,z] UNION segment[z,y]`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) o
      check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^2,z,y} = {y,z,x}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x:real^2`; `z:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    MP_TAC(ISPECL [`z:real^2`; `y:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2`; `z:real^2`; `y:real^2`; `l:(real^2)list`;
                 `W:real^2->bool`] MOI_SA2_EAR_REMOVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `g1:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH(CONS (x:real^2) (CONS y l))`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `LENGTH(CONS (x:real^2) (CONS z (CONS y l))) = LENGTH(p:(real^2)list)` THEN
    REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`CONS (x:real^2) (CONS y l)`; `W:real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h1:real^2->real^2`; `g1:real^2->real^2`;
                   `CONS x (CONS z (CONS y l)):(real^2)list`;
                   `CONS x (CONS y l):(real^2)list`] MOI_SA2_REGION_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h1:real^2->real^2`; `g1:real^2->real^2`; `W:real^2->bool`;
                   `moi_sa2_region p`] MOI_SA2_FIX_OFF) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `h2:real^2->real^2`
    (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`t:real^2->bool`; `(h2:real^2->real^2) o (h1:real^2->real^2)`;
    `(g1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC
   `path_image(polygonal_path(CONS x (CONS z (CONS y l)))) =
    path_image(polygonal_path(p:(real^2)list))` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moving a given point of the boundary of a triangle to a                   *)
(* vertex (one more ear removal: the corner a of the polygon c, a, z, b      *)
(* when z lies inside the edge [a,b]), and the main theorem AMB2_VERTEX.    *)
(* ------------------------------------------------------------------------- *)

let MOI_SA2_VERTEX_FACE = prove
 (`!a b c:real^2. ~collinear{a,b,c} ==> {a} face_of convex hull {a,b,c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACE_OF_SING] THEN
  SUBGOAL_THEN `~affine_dependent{a:real^2,b,c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  SET_TAC[]);;

let MOI_SA2_CORNER_MOVE = prove
 (`!a b c z:real^2 W.
     ~collinear{a,b,c} /\ z IN segment(a,b) /\
     open W /\ convex hull {a,b,c} SUBSET W
     ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
               (!x. ~(x IN W) ==> h x = x) /\ h z = z /\
               ~collinear{c,z,b} /\
               IMAGE h (segment[a,b] UNION segment[b,c] UNION segment[c,a]) =
               segment[c,z] UNION segment[z,b] UNION segment[b,c]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real^2 = b)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~collinear{b:real^2,b,c}` THEN
    REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^2) IN segment(a,b)` THEN
  ASM_REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(moi_sa2_det (a - c) (b - c:real^2) = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
    ONCE_REWRITE_TAC[SET_RULE `{a:real^2,b,c} = {c,a,b}`] THEN
    REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sa2_det (a - c) (z - c:real^2) = s * moi_sa2_det (a - c) (b - c) /\
    moi_sa2_det (z - c) (b - c:real^2) = (&1 - s) * moi_sa2_det (a - c) (b - c)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_sa2_det; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VECTOR_SUB_COMPONENT] THEN
    CONJ_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{c:real^2,a,z} /\ ~collinear{c:real^2,z,b}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SA2_DET_NONCOLLINEAR] THEN
    UNDISCH_TAC
     `moi_sa2_det (a - c) (z - c:real^2) = s * moi_sa2_det (a - c) (b - c)` THEN
    UNDISCH_TAC
     `moi_sa2_det (z - c) (b - c:real^2) = (&1 - s) * moi_sa2_det (a - c) (b - c)` THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    UNDISCH_TAC `~(moi_sa2_det (a - c) (b - c:real^2) = &0)` THEN
    UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `s < &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN segment[a,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {c:real^2,a,z} SUBSET convex hull {a,b,c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HULL_INC THEN SET_TAC[]) THEN
    MATCH_MP_TAC(SET_RULE `!t. (z:real^2) IN t /\ t SUBSET s ==> z IN s`) THEN
    EXISTS_TAC `segment[a:real^2,b]` THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sa2_ca c a z (b:real^2) = --((&1 - s) / s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`; `a:real^2`; `b:real^2`;
                   `&1 - s`; `s:real`] MOI_SA2_CA_AFFINE) THEN
    REWRITE_TAC[REAL_ARITH `(&1 - s) + s = &1`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> rand(concl th) = `(&1 - s) % a + s % b:real^2`)) THEN
    MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`; `&0`]
      MOI_SA2_COORD_VALUES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_THEN `z:real^2 = (&1 - s) % a + s % b` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `(segment[z,b] UNION segment[c,b]) INTER convex hull {c:real^2,a,z}
    SUBSET {c,z}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT1 o
      MATCH_MP MOI_SA2_TRIANGLE_COORDS o
      CONJ (ASSUME `~collinear{c:real^2,a,z}`))) THEN
    REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[GSYM IMP_IMP] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[MOI_SA2_CA_AFFINE; REAL_ARITH `(&1 - r) + r = &1`] THEN
    MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`; `&0`]
      MOI_SA2_COORD_VALUES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
    DISCH_TAC THEN
    (SUBGOAL_THEN `r = &0` SUBST_ALL_TAC THENL
      [SUBGOAL_THEN `&0 < (&1 - s) / s` ASSUME_TAC THENL
        [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC(REAL_ARITH `&0 <= r /\ ~(&0 < r) ==> r = &0`) THEN
       ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
       MP_TAC(ISPECL [`r:real`; `--((&1 - s) / s)`] MOI_SA2_POS_NEG_MUL) THEN
       ASM_REAL_ARITH_TAC;
       REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                   VECTOR_ADD_RID] THEN MESON_TAC[]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`;
                 `{segment[z:real^2,b], segment[c,b]}`; `W:real^2->bool`]
    MOI_SA2_EAR_GEOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; UNIONS_2] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`; `e:real`]
    MOI_SA2_QUAD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `z:real^2`; `e:real`]
    MOI_SA2_EAR_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!x:real^2. x IN segment[z,b] UNION segment[c,b] ==> h x = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `moi_sa2_quad c a z e` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`h:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `interior:(real^2->bool)->real^2->bool`)) (concl th))) THEN
    MP_TAC(ISPEC `moi_sa2_quad c a z e` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_sa2_quad c a z e SUBSET W` THEN
    UNDISCH_TAC `~((x:real^2) IN W)` THEN SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
    (segment[c,a] UNION segment[a,z]) UNION
    (segment[z,b] UNION segment[c,b:real^2])`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`a:real^2`; `z:real^2`; `b:real^2`] UNION_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`b:real^2`; `c:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBST1_TAC(ISPECL [`b:real^2`; `c:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE h s = t /\ (!x. x IN r ==> h x = x)
    ==> IMAGE (h:real^2->real^2) (s UNION r) = t UNION r`) THEN
  ASM_REWRITE_TAC[]);;
let MOI_SA2_EDGE_POINT_VERTEX = prove
 (`!a b c z:real^2 W.
     ~collinear{a,b,c} /\ z IN segment(a,b) /\
     open W /\ convex hull {a,b,c} SUBSET W
     ==> ?t' h g. &2 simplex t' /\
                  pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
                  (!x. ~(x IN W) ==> h x = x) /\
                  IMAGE h (segment[a,b] UNION segment[b,c] UNION segment[c,a]) =
                  relative_frontier t' /\
                  {h z} face_of t'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`; `z:real^2`; `W:real^2->bool`]
    MOI_SA2_CORNER_MOVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {c:real^2,z,b}`; `h:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  CONJ_TAC THENL [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{c:real^2,z,b} = {z,c,b}`] THEN
  MATCH_MP_TAC MOI_SA2_VERTEX_FACE THEN
  ONCE_REWRITE_TAC[SET_RULE `{z:real^2,c,b} = {c,z,b}`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SA2_TRIANGLE_VERTEX = prove
 (`!t W z:real^2.
     &2 simplex t /\ open W /\ t SUBSET W /\ z IN relative_frontier t
     ==> ?t' h g. &2 simplex t' /\
                  pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
                  (!x. ~(x IN W) ==> h x = x) /\
                  IMAGE h (relative_frontier t) = relative_frontier t' /\
                  {h z} face_of t'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` (X_CHOOSE_THEN `c:real^2`
     STRIP_ASSUME_TAC)) o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2])
   STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `(z:real^2) IN relative_frontier(convex hull {a,b,c})` THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `z:real^2 = a \/ z = b \/ z = c` THENL
   [MAP_EVERY EXISTS_TAC
     [`convex hull {a:real^2,b,c}`; `\x:real^2. x`; `\x:real^2. x`] THEN
    ASM_SIMP_TAC[MOI_SA2_PLH_ID; IMAGE_ID; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    CONJ_TAC THENL [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [ASM_SIMP_TAC[MOI_SA2_VERTEX_FACE];
      ONCE_REWRITE_TAC[SET_RULE `{a:real^2,b,c} = {b,a,c}`] THEN
      MATCH_MP_TAC MOI_SA2_VERTEX_FACE THEN
      ONCE_REWRITE_TAC[SET_RULE `{b:real^2,a,c} = {a,b,c}`] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[SET_RULE `{a:real^2,b,c} = {c,a,b}`] THEN
      MATCH_MP_TAC MOI_SA2_VERTEX_FACE THEN
      ONCE_REWRITE_TAC[SET_RULE `{c:real^2,a,b} = {a,b,c}`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(z:real^2) IN segment(a,b) \/ z IN segment(b,c) \/ z IN segment(c,a)`
  MP_TAC THENL
   [UNDISCH_TAC
     `(z:real^2) IN segment[a,b] UNION segment[b,c] UNION segment[c,a]` THEN
    UNDISCH_TAC `~(z:real^2 = a \/ z = b \/ z = c)` THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SA2_EDGE_POINT_VERTEX THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `a:real^2`; `z:real^2`;
                   `W:real^2->bool`] MOI_SA2_EDGE_POINT_VERTEX);
    MP_TAC(ISPECL [`c:real^2`; `a:real^2`; `b:real^2`; `z:real^2`;
                   `W:real^2->bool`] MOI_SA2_EDGE_POINT_VERTEX)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL
    [CONJ_TAC THENL
      [RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
       REWRITE_TAC[INSERT_AC] THEN ASM_REWRITE_TAC[];
       RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
       REWRITE_TAC[INSERT_AC] THEN ASM_REWRITE_TAC[]];
     ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^2->bool` (X_CHOOSE_THEN `h:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`t':real^2->bool`; `h:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rand(concl th) = `relative_frontier (t':real^2->bool)`)) THEN
  AP_TERM_TAC THEN SET_TAC[]);;
let AMB2_VERTEX = prove
 (`!s w (p:real^2).
     pl_sphere 1 s /\ open w /\ s UNION inside s SUBSET w /\ p IN s
     ==> ?(t:real^2->bool) f g.
           &2 simplex t /\ pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
           (!x. ~(x IN w) ==> f x = x) /\ IMAGE f s = relative_frontier t /\
           {f p} face_of t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `L:(real^2)list` STRIP_ASSUME_TAC o
    MATCH_MP PL_SPHERE_1_POLYGON) THEN
  MP_TAC(ISPECL [`LENGTH(L:(real^2)list)`; `L:(real^2)list`; `w:real^2->bool`]
    MOI_SA2_AMB2_POLY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[moi_sa2_region] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `h1:real^2->real^2`
    (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `t SUBSET (w:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (h1:real^2->real^2) (s UNION inside s) = t`
    (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[IMAGE_UNION] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
      MP_TAC(ISPECL [`h1:real^2->real^2`; `g1:real^2->real^2`;
                     `s:real^2->bool`] MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&2 simplex (t:real^2->bool)` THEN
      REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
        (X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC))) THEN
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
      REWRITE_TAC[MOI_PL2_TRIANGLE_CLOSED_INSIDE];
      MP_TAC(ISPECL [`h1:real^2->real^2`; `g1:real^2->real^2`;
                     `w:real^2->bool`; `s UNION inside(s:real^2->bool)`]
        MOI_SA2_FIX_OFF) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `w:real^2->bool`; `(h1:real^2->real^2) p`]
    MOI_SA2_TRIANGLE_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `IMAGE (h1:real^2->real^2) s = relative_frontier t`
      (SUBST1_TAC o SYM) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^2->bool` (X_CHOOSE_THEN `h2:real^2->real^2`
    (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`t':real^2->bool`; `(h2:real^2->real^2) o (h1:real^2->real^2)`;
    `(g1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

