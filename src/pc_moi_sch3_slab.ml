(* ========================================================================= *)
(* pc_moi_sch3_slab: MOI_SSL_FIBRED_FROM_SLAB : |- MOI_SSL_SLAB_STMT ==>     *)
(* MOI_SCH3_FIBRED_SIMPLE (Moise GTM 47, Sec 17, proof of 17.12, Lemmas      *)
(* 4-6 and the final gluing, pp.124-125): a fibred PL 2-sphere whose filling *)
(* is triangulated with a generic height is simply imbedded, given the slab  *)
(* lemma MOI_SSL_SLAB_STMT (proved in pc_moi_sch3_slabb from the star lemma  *)
(* MOI_SSL_STAR_STMT, which pc_moi_sch3_slabc proves).  The statement        *)
(* MOI_SCH3_FIBRED_SIMPLE is in pc_moi_sch3_stmt.ml.                         *)
(* The first section gives generic facts and the abstract deletion (push)    *)
(* step.                                                                     *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_glue.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_sch3_cvx.ml";;

prioritize_real();;
type_invention_error := true;;

(* The slab lemma (Moise p.124, Lemma 6, adapted: one vertex v strictly     *)
(* inside the slab [t1,t2]).  This file proves MOI_SSL_SLAB_STMT ==>        *)
(* MOI_SCH3_FIBRED_SIMPLE; the slab statement itself is proved in           *)
(* pc_moi_sch3_slabb.                                                       *)

let MOI_SSL_SLAB_STMT =
 `!(s:real^3->bool) (a:real^3) (lo:real) (hi:real) (k:(real^3->bool)->bool)
   (v:real^3) (t1:real) (t2:real).
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!x y. {x} IN k /\ {y} IN k /\ a dot x = a dot y ==> x = y) /\
     lo < t1 /\ t1 < a dot v /\ a dot v < t2 /\ t2 < hi /\ {v} IN k /\
     (!w. {w} IN k /\ t1 <= a dot w /\ a dot w <= t2 ==> w = v)
     ==> moi_sch3_simple (((s UNION inside s) INTER {x:real^3 | a dot x = t1}) UNION
                          ((s UNION inside s) INTER {x:real^3 | a dot x = t2}) UNION
                          (s INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}))`;;

(* ------------------------------------------------------------------------- *)
(* Convex cells: a polytope with nonempty interior is simply imbedded and    *)
(* filled by its frontier.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_CELL_FACTS = prove
 (`!c:real^3->bool.
     polytope c /\ ~(interior c = {})
     ==> compact c /\ closed c /\ convex c /\ bounded c /\
         closure(interior c) = c /\
         frontier c = c DIFF interior c /\
         frontier c UNION inside(frontier c) = c /\
         moi_sch3_simple (frontier c) /\ pl_sphere 2 (frontier c)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (c:real^3->bool) /\ convex c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (c:real^3->bool) /\ bounded c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_sch3_simple (frontier c:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SCD_CONVEX_SIMPLE STAR_SIMPLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SCD_SIMPLE_IMP_SPHERE; CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED;
               INSIDE_FRONTIER_EQ_INTERIOR] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The abstract deletion step (Moise p.124, "delete C^3 by a PLH"): a       *)
(* convex cell c of a compact region r is deleted when the attaching set e  *)
(* = frontier c INTER closure(r DIFF c) is a PL 2-cell whose boundary je    *)
(* lies on the frontier of r and whose other points are interior to r.      *)
(* If the frontier of the smaller region is simply imbedded, so is the      *)
(* frontier of r (MOI_SCD_PUSH_SIMPLE with the push property of the convex  *)
(* cell from SIMPLEX_PUSH and STAR_SIMPLE).                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_PUSH_DELETE = prove
 (`!(r:real^3->bool) c je.
     compact r /\ polytope c /\ ~(interior c = {}) /\ c SUBSET r /\
     pl_cell_with_boundary 2 (frontier c INTER closure(r DIFF c)) je /\
     (frontier c INTER closure(r DIFF c)) DIFF je SUBSET interior r /\
     je SUBSET frontier r /\
     moi_sch3_simple (frontier (closure (r DIFF c)))
     ==> moi_sch3_simple (frontier r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r' = closure((r:real^3->bool) DIFF c)` THEN
  ABBREV_TAC `e = frontier c INTER (r':real^3->bool)` THEN
  MP_TAC(ISPEC `c:real^3->bool` MOI_SSL_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (r:real^3->bool) /\ bounded r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `(r':real^3->bool) SUBSET r /\ closed r' /\ r DIFF c SUBSET r'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c INTER (r':real^3->bool) = {}` ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN
    SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(je:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real^3->bool`; `je:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET frontier c /\ e SUBSET r' /\ e SUBSET c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    UNDISCH_TAC `frontier c = (c:real^3->bool) DIFF interior c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c SUBSET interior (r:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior r' SUBSET interior (r:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier r = (r:real^3->bool) DIFF interior r /\
                frontier r' = (r':real^3->bool) DIFF interior r'`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN interior r /\ ~(x IN r') ==> x IN interior c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(interior r INTER ((:real^3) DIFF r')) SUBSET interior c`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; GSYM closed] THEN
      MP_TAC(ISPEC `r:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(r:real^3->bool) DIFF c SUBSET r'` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN interior r` THEN
      UNDISCH_TAC `~((x:real^3) IN r')` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN interior r /\ ~(x IN c) ==> x IN interior r'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(interior r INTER ((:real^3) DIFF c)) SUBSET interior r'`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; GSYM closed] THEN
      MP_TAC(ISPEC `r:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(r:real^3->bool) DIFF c SUBSET r'` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN interior r` THEN
      UNDISCH_TAC `~((x:real^3) IN c)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN e ==> ~(x IN interior r')` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN interior r'` THEN
    GEN_REWRITE_TAC LAND_CONV [IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) IN closure(interior c)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e:real^3->bool) SUBSET c` THEN
      UNDISCH_TAC `(x:real^3) IN e` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN r'` MP_TAC THENL
     [UNDISCH_TAC `ball(x:real^3,d) SUBSET r'` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      UNDISCH_TAC `interior c INTER (r':real^3->bool) = {}` THEN
      UNDISCH_TAC `(y:real^3) IN interior c` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier r INTER c = (frontier c DIFF e) UNION (je:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_DIFF] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_CASES_TAC `(x:real^3) IN je` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN r /\ ~(x IN interior r)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN frontier r` THEN ASM_REWRITE_TAC[IN_DIFF];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN
        UNDISCH_TAC `interior c SUBSET interior (r:real^3->bool)` THEN
        UNDISCH_TAC `~((x:real^3) IN interior r)` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      UNDISCH_TAC `e DIFF je SUBSET interior (r:real^3->bool)` THEN
      UNDISCH_TAC `~((x:real^3) IN interior r)` THEN
      UNDISCH_TAC `~((x:real^3) IN je)` THEN UNDISCH_TAC `(x:real^3) IN e` THEN
      SET_TAC[];
      STRIP_TAC THENL
       [ALL_TAC;
        CONJ_TAC THENL
         [UNDISCH_TAC `(je:real^3->bool) SUBSET frontier r` THEN
          UNDISCH_TAC `(x:real^3) IN je` THEN SET_TAC[];
          UNDISCH_TAC `(je:real^3->bool) SUBSET e` THEN
          UNDISCH_TAC `(e:real^3->bool) SUBSET c` THEN
          UNDISCH_TAC `(x:real^3) IN je` THEN SET_TAC[]]] THEN
      SUBGOAL_THEN `~((x:real^3) IN r')` ASSUME_TAC THENL
       [UNDISCH_TAC `~((x:real^3) IN e)` THEN EXPAND_TAC "e" THEN
        UNDISCH_TAC `(x:real^3) IN frontier c` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN c /\ ~(x IN interior c)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN frontier c` THEN ASM_REWRITE_TAC[IN_DIFF];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `c SUBSET (r:real^3->bool)` THEN
        UNDISCH_TAC `(x:real^3) IN c` THEN SET_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier r' = (frontier r DIFF c) UNION (e:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN r' /\ ~(x IN interior r')` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN frontier r'` THEN ASM_REWRITE_TAC[IN_DIFF];
        ALL_TAC] THEN
      ASM_CASES_TAC `(x:real^3) IN c` THEN ASM_REWRITE_TAC[] THENL
       [EXPAND_TAC "e" THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[IN_DIFF] THEN
        UNDISCH_TAC `interior c INTER (r':real^3->bool) = {}` THEN
        UNDISCH_TAC `(x:real^3) IN r'` THEN SET_TAC[];
        ALL_TAC] THEN
      DISJ1_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(r':real^3->bool) SUBSET r` THEN
        UNDISCH_TAC `(x:real^3) IN r'` THEN SET_TAC[];
        ASM_MESON_TAC[]];
      STRIP_TAC THENL
       [SUBGOAL_THEN `(x:real^3) IN r /\ ~(x IN interior r)` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(x:real^3) IN frontier r` THEN ASM_REWRITE_TAC[IN_DIFF];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(r:real^3->bool) DIFF c SUBSET r'` THEN
          UNDISCH_TAC `(x:real^3) IN r` THEN UNDISCH_TAC `~((x:real^3) IN c)` THEN
          SET_TAC[];
          UNDISCH_TAC `interior r' SUBSET interior (r:real^3->bool)` THEN
          UNDISCH_TAC `~((x:real^3) IN interior r)` THEN SET_TAC[]];
        ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(e:real^3->bool) SUBSET r'` THEN
          UNDISCH_TAC `(x:real^3) IN e` THEN SET_TAC[];
          ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCD_PUSH_SIMPLE THEN
  MAP_EVERY EXISTS_TAC
   [`c:real^3->bool`; `(frontier c DIFF e) UNION (je:real^3->bool)`;
    `je:real^3->bool`] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 ((frontier c DIFF e) UNION (je:real^3->bool)) je`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`frontier c:real^3->bool`;
                   `(frontier c DIFF e) UNION (je:real^3->bool)`; `je:real^3->bool`]
      (MATCH_MP MOI_SCD_SIMPLE_PUSH SIMPLEX_PUSH)) THEN
    REWRITE_TAC[ASSUME `frontier c UNION inside (frontier c) = (c:real^3->bool)`;
      ASSUME `pl_cell_with_boundary 2 ((frontier c DIFF e) UNION (je:real^3->bool)) je`;
      ASSUME `moi_sch3_simple (frontier c:real^3->bool)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(je:real^3->bool) SUBSET e` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET frontier c` THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    SET_TAC[];
    UNDISCH_TAC `frontier r INTER c = (frontier c DIFF e) UNION (je:real^3->bool)` THEN
    SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^3->bool` THEN
    ASM_SIMP_TAC[SUBSET_CONVEX_HULL_FRONTIER];
    SUBGOAL_THEN
     `(frontier r DIFF ((frontier c DIFF e) UNION je)) UNION je =
      (frontier r' DIFF e) UNION (je:real^3->bool)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `frontier r' = (frontier r DIFF c) UNION (e:real^3->bool)` THEN
      UNDISCH_TAC `frontier r INTER c = (frontier c DIFF e) UNION (je:real^3->bool)` THEN
      UNDISCH_TAC `(je:real^3->bool) SUBSET e` THEN
      UNDISCH_TAC `(e:real^3->bool) SUBSET c` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`frontier r':real^3->bool`; `e:real^3->bool`;
                   `je:real^3->bool`] DISK_COMPLEMENT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SCD_SIMPLE_IMP_SPHERE THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `frontier r' = (frontier r DIFF c) UNION (e:real^3->bool)` THEN
        SET_TAC[]];
      MESON_TAC[MOI_SS2_FSA_OF_CELL; MOI_SS2_FSA_POLYHEDRON]];
    UNDISCH_TAC `frontier r INTER c = (frontier c DIFF e) UNION (je:real^3->bool)` THEN
    SET_TAC[];
    SUBGOAL_THEN
     `(frontier r DIFF ((frontier c DIFF e) UNION je)) UNION
      (frontier c DIFF ((frontier c DIFF e) UNION je)) UNION je =
      frontier (r':real^3->bool)`
    SUBST1_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `frontier r' = (frontier r DIFF c) UNION (e:real^3->bool)` THEN
    UNDISCH_TAC `frontier r INTER c = (frontier c DIFF e) UNION (je:real^3->bool)` THEN
    UNDISCH_TAC `(je:real^3->bool) SUBSET e` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET frontier c` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET c` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The filled fibred sphere M = s UNION inside s.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_FIB_FACTS = prove
 (`!s (a:real^3) lo hi.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi
     ==> compact s /\ compact (s UNION inside s) /\ closed (s UNION inside s) /\
         frontier (s UNION inside s) = s /\
         interior (s UNION inside s) = inside s /\ open (inside s) /\
         ~(a = vec 0) /\ lo < hi /\
         (!x. x IN s UNION inside s ==> lo <= a dot x /\ a dot x <= hi) /\
         (!x. x IN inside s ==> lo < a dot x /\ a dot x < hi) /\
         (?p. (s UNION inside s) INTER {x | a dot x = lo} = {p} /\ p IN s) /\
         (?q. (s UNION inside s) INTER {x | a dot x = hi} = {q} /\ q IN s) /\
         (!t. lo < t /\ t < hi
              ==> pl_cell_with_boundary 2 ((s UNION inside s) INTER {x | a dot x = t})
                                          (s INTER {x | a dot x = t}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_fibred] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (s UNION inside s) = (s:real^3->bool) /\
                interior (s UNION inside s) = inside s /\
                closed (s UNION inside s)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
    MATCH_MP_TAC OPEN_OUTSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (inside s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_INSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `inside s SUBSET {x:real^3 | a dot x >= lo} /\
                inside s SUBSET {x:real^3 | a dot x <= hi}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_HALFSPACE_GE; CONVEX_HALFSPACE_LE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge] THEN
    UNDISCH_TAC `!x:real^3. x IN s ==> lo <= a dot x /\ a dot x <= hi` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN inside s ==> lo < a dot x /\ a dot x < hi`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inside s SUBSET interior {x:real^3 | a dot x >= lo} /\
                  inside s SUBSET interior {x:real^3 | a dot x <= hi}`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[INTERIOR_HALFSPACE_GE; INTERIOR_HALFSPACE_LE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [REWRITE_TAC[BOUNDED_UNION] THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC BOUNDED_INSIDE THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `!x:real^3. x IN s ==> lo <= a dot x /\ a dot x <= hi` THEN
    UNDISCH_TAC `!x:real^3. x IN inside s ==> lo < a dot x /\ a dot x < hi` THEN
    MESON_TAC[REAL_LT_IMP_LE];
    EXISTS_TAC `p:real^3` THEN
    UNDISCH_TAC `s INTER {x:real^3 | a dot x = lo} = {p}` THEN
    UNDISCH_TAC `!x:real^3. x IN inside s ==> lo < a dot x /\ a dot x < hi` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_SING; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_REFL];
    EXISTS_TAC `q:real^3` THEN
    UNDISCH_TAC `s INTER {x:real^3 | a dot x = hi} = {q}` THEN
    UNDISCH_TAC `!x:real^3. x IN inside s ==> lo < a dot x /\ a dot x < hi` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_SING; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* A level plane (the points x with a dot x = t) is an affine copy of real^2 *)
(* (frame MOI_SCX_FRAME of pc_moi_sch3_cvx); a PL 2-cell lying in it has its *)
(* boundary as relative frontier.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_PLANE_FRAME = prove
 (`!(a:real^3) t.
     ~(a = vec 0)
     ==> ?(phi:real^2->real^3) (psi:real^3->real^2) (l:real^2->real^3) q.
           linear l /\ (!u v. l u = l v ==> u = v) /\ (!u. phi u = q + l u) /\
           (!u. a dot (phi u) = t) /\ (!u. psi (phi u) = u) /\
           (!x. a dot x = t ==> phi (psi x) = x) /\
           pl_homeomorphism ({x | a dot x = t},(:real^2)) (psi,phi)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t:real`] MOI_SCX_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:real^3->real^3` (X_CHOOSE_THEN `l3':real^3->real^3`
    (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC MOI_SCX_EP THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(a:real^3) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. a dot x = t ==>
               q + (l3:real^3->real^3) (moi_scx_e (moi_scx_pr (l3' (x - q)))) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `((l3':real^3->real^3) (x - q))$3 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(l3':real^3->real^3) (x - q)` o check
        (fun th -> is_forall(concl th) &&
                   can (find_term (fun t -> t = `norm(a:real^3)`)) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `q + x - q:real^3 = x`] THEN
      ASM_REWRITE_TAC[REAL_ARITH `t = t + n * y <=> n * y = &0`; REAL_ENTIRE];
      ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\u:real^2. q + (l3:real^3->real^3) (moi_scx_e u)`;
    `\x:real^3. moi_scx_pr ((l3':real^3->real^3) (x - q))`;
    `(l3:real^3->real^3) o moi_scx_e`; `q:real^3`] THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear (\u:real^2. (l3:real^3->real^3) (moi_scx_e u)) /\
                linear (\x:real^3. moi_scx_pr ((l3':real^3->real^3) x)) /\
                linear (\x:real^3. (moi_scx_pr o (l3':real^3->real^3)) x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM o_DEF; ETA_AX] THEN ASM_SIMP_TAC[LINEAR_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^2. a dot (q + (l3:real^3->real^3) (moi_scx_e u)) = t`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^2. moi_scx_pr ((l3':real^3->real^3) ((q + l3 (moi_scx_e u)) - q)) = u`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(q + x) - q:real^3 = x`]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_scx_e u = moi_scx_e v` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  SUBGOAL_THEN `locally_polyhedral {x:real^3 | a dot x = t}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SA2_LP_POLYHEDRON THEN REWRITE_TAC[POLYHEDRON_HYPERPLANE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. moi_scx_pr ((l3':real^3->real^3) (x - q)) =
               (moi_scx_pr o l3') x + --(moi_scx_pr (l3' q))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^2` THEN
    EXISTS_TAC `q + (l3:real^3->real^3) (moi_scx_e u)` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE];
    ASM_REWRITE_TAC[IN_UNIV];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `moi_scx_pr ((l3':real^3->real^3) (x - q))` THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_SIMP_TAC[LINEAR_COMPOSE];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. (moi_scx_pr o (l3':real^3->real^3)) x +
                           --(moi_scx_pr (l3' q))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\u:real^2. ((l3:real^3->real^3) o moi_scx_e) u + q` THEN
    REWRITE_TAC[o_THM; VECTOR_ADD_SYM] THEN MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE; MOI_SCX_LP_UNIV]]);;

let MOI_SSL_PLANE_CELL = prove
 (`!(a:real^3) t d j.
     ~(a = vec 0) /\ pl_cell_with_boundary 2 d j /\ d SUBSET {x | a dot x = t}
     ==> relative_frontier d = j /\ relative_interior d = d DIFF j /\
         j SUBSET d /\ compact d /\ ~(d DIFF j = {}) /\
         affine hull d = {x | a dot x = t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `t:real`] MOI_SSL_PLANE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^3` (X_CHOOSE_THEN `psi:real^3->real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `q:real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ compact d /\ ~(d DIFF j = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (psi:real^3->real^2) d) (IMAGE psi j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`{x:real^3 | a dot x = t}`; `(:real^2)`;
                          `phi:real^2->real^3`] THEN
    ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier (IMAGE (psi:real^3->real^2) d) = IMAGE psi j /\
    interior (IMAGE (psi:real^3->real^2) d) = IMAGE psi d DIFF IMAGE psi j /\
    ~(interior (IMAGE (psi:real^3->real^2) d) = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (psi:real^3->real^2) d`; `IMAGE (psi:real^3->real^2) j`]
      MOI_SFR_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      let ths = CONJUNCTS th in
      let find t = find (fun th -> concl th = t) ths in
      REWRITE_TAC[find `frontier (IMAGE (psi:real^3->real^2) d) = IMAGE psi j`;
                  find `interior (IMAGE (psi:real^3->real^2) d) =
                        inside (IMAGE psi j)`] THEN
      MP_TAC(find `IMAGE (psi:real^3->real^2) d =
                   IMAGE psi j UNION inside (IMAGE psi j)`) THEN
      MP_TAC(find `inside (IMAGE (psi:real^3->real^2) j) INTER IMAGE psi j = {}`) THEN
      MP_TAC(find `~(inside (IMAGE (psi:real^3->real^2) j) = {})`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN d ==> phi ((psi:real^3->real^2) x) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `d SUBSET {x:real^3 | a dot x = t}` THEN
    UNDISCH_TAC `(x:real^3) IN d` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET d ==> IMAGE (phi:real^2->real^3)
                                     (IMAGE psi s) = s`
  (LABEL_TAC "inv") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) s` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (f:real^3->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull d = {x:real^3 | a dot x = t}`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN
     `d = IMAGE (\x:real^3. q + x) (IMAGE (l:real^2->real^3) (IMAGE psi d))`
    SUBST1_TAC THENL
     [USE_THEN "inv" (fun th -> GEN_REWRITE_TAC LAND_CONV
        [GSYM(MATCH_MP th (ISPEC `d:real^3->bool` SUBSET_REFL))]) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[AFFINE_HULL_TRANSLATION;
      MATCH_MP AFFINE_HULL_LINEAR_IMAGE (ASSUME `linear (l:real^2->real^3)`);
      MATCH_MP AFFINE_HULL_NONEMPTY_INTERIOR
        (ASSUME `~(interior (IMAGE (psi:real^3->real^2) d) = {})`)] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `u:real^2` SUBST1_TAC))) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(l:real^2->real^3) ((psi:real^3->real^2) x)` THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier (d:real^3->bool) =
      IMAGE (phi:real^2->real^3) (relative_frontier (IMAGE psi d)) /\
    relative_interior (d:real^3->bool) =
      IMAGE (phi:real^2->real^3) (relative_interior (IMAGE psi d))`
  (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THENL
   [SUBGOAL_THEN `!s:real^2->bool. IMAGE (phi:real^2->real^3) s =
                                   IMAGE (\x. q + x) (IMAGE l s)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(phi:real^2->real^3) = (\u. q + l u)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF];
      ALL_TAC] THEN
    REMOVE_THEN "inv" (fun th -> GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP th (ISPEC `d:real^3->bool` SUBSET_REFL))]) THEN
    ASM_REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION; RELATIVE_INTERIOR_TRANSLATION] THEN
    MP_TAC(ISPECL [`l:real^2->real^3`; `IMAGE (psi:real^3->real^2) d`]
      RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
    MP_TAC(ISPECL [`l:real^2->real^3`; `IMAGE (psi:real^3->real^2) d`]
      RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE) THEN
    MATCH_MP_TAC(TAUT `p /\ (q /\ r ==> s) ==> (p ==> q) ==> (p ==> r) ==> s`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (psi:real^3->real^2) d` RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
  MP_TAC(ISPEC `IMAGE (psi:real^3->real^2) d` RELATIVE_INTERIOR_NONEMPTY_INTERIOR) THEN
  REWRITE_TAC[ASSUME `~(interior (IMAGE (psi:real^3->real^2) d) = {})`] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ASSUME `frontier (IMAGE (psi:real^3->real^2) d) = IMAGE psi j`;
              ASSUME `interior (IMAGE (psi:real^3->real^2) d) =
                      IMAGE psi d DIFF IMAGE psi j`] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^2) d DIFF IMAGE psi j =
                IMAGE psi (d DIFF j)` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
      `(!x y. x IN d /\ y IN d /\ (f:real^3->real^2) x = f y ==> x = y) /\
       (j:real^3->bool) SUBSET d
       ==> IMAGE f d DIFF IMAGE f j = IMAGE f (d DIFF j)`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REMOVE_THEN "inv" MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simplices of the complex, extreme vertices, radial maps and the bottom    *)
(* cone (Moise p.124, Lemma 4).                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_SIMPLEX_HULL = prove
 (`!k s:real^3->bool.
     simplicial_complex k /\ s IN k
     ==> ?c. FINITE c /\ ~affine_dependent c /\ s = convex hull c /\
             (!w. w IN c ==> {w} IN k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool` o check (fun th ->
    can (term_match [] `!s:real^3->bool. s IN k ==> ?n. n simplex s`) (concl th))) THEN
  ASM_REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `c:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!f s:real^3->bool. s IN k /\ f face_of s ==> f IN k`)
      (concl th))) THEN
  EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_SSL_HULL_GT = prove
 (`!c (a:real^3) t x.
     x IN convex hull c /\ (!w. w IN c ==> t < a dot w) ==> t < a dot x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull c SUBSET {y:real^3 | a dot y > t}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN ASM_MESON_TAC[]]);;

let MOI_SSL_HULL_LT = prove
 (`!c (a:real^3) t x.
     x IN convex hull c /\ (!w. w IN c ==> a dot w < t) ==> a dot x < t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull c SUBSET {y:real^3 | a dot y < t}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* A point of the polyhedron at its lowest level is a vertex, when vertex   *)
(* heights are distinct (the face of a simplex on a supporting plane).      *)

let MOI_SSL_EXTREME_VERTEX = prove
 (`!k (a:real^3) x.
     simplicial_complex k /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w) /\
     x IN UNIONS k /\ (!y. y IN UNIONS k ==> a dot x <= a dot y)
     ==> {x} IN k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN UNIONS k` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `s:real^3->bool`]
    MOI_SSL_SIMPLEX_HULL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET UNIONS k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `s = convex hull (c:real^3->bool)`)) THEN
  SUBGOAL_THEN
   `convex hull c INTER {y:real^3 | a dot y = a dot x} face_of convex hull c`
  MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; real_ge] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN convex hull c'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN c' ==> a dot w = a dot x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN convex hull c'` MP_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. c' = {w}` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `c':real^3->bool = {}` THENL
     [UNDISCH_TAC `(x:real^3) IN convex hull c'` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `w:real^3` o GEN_REWRITE_RULE I
      [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `w:real^3` THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!v w:real^3. {v} IN k /\ {w} IN k /\ a dot v = a dot w
                                         ==> v = w`) (concl th))) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ASM_MESON_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN convex hull c'` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* The radial projection from p onto a level, z |-> p + (r / (a.z - c))(z - p) *)
(* is continuous above the level c.                                         *)

let MOI_SSL_RADIAL_CONT = prove
 (`!(a:real^3) p c r.
     (\z. p + (r / (a dot z - c)) % (z - p)) continuous_on {z | c < a dot z}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[real_div; o_DEF; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MP_TAC(ISPECL [`\z:real^3. a dot z - c`; `{z:real^3 | c < a dot z}`]
    CONTINUOUS_ON_INV) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DOT];
    SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]);;


(* Below the level t the polyhedron is the cone from p over its section at  *)
(* t when p is the only vertex at height at most t (Moise p.124, Lemma 4).  *)

let MOI_SSL_CONE_REGION = prove
 (`!k (a:real^3) p t.
     simplicial_complex k /\ p IN UNIONS k /\ a dot p < t /\
     ~(UNIONS k INTER {x | a dot x = t} = {}) /\
     (!w. {w} IN k /\ a dot w <= t ==> w = p)
     ==> UNIONS k INTER {x | a dot x <= t} =
         UNIONS {segment[p,y] | y IN UNIONS k INTER {x | a dot x = t}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN k ==> ?c. FINITE c /\ ~affine_dependent c /\ s = convex hull c /\ (!w. w IN c ==> {w} IN k) /\ (!w. w IN c /\ ~(w = p) ==> t < a dot w)` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `s:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN UNDISCH_TAC `~(w:real^3 = p)` THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match [] `!w:real^3. {w} IN k /\ a dot w <= t ==> w = p`) (concl th))) THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN REWRITE_TAC[SUBSET] THENL
  [REWRITE_TAC[MOI_CON_IN_CONE] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t:real`; `x:real^3`]
        MOI_SSL_HULL_GT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
  ASM_CASES_TAC `c DELETE (p:real^3) = {}` THENL
   [SUBGOAL_THEN `c = {p:real^3}` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c DELETE (p:real^3) = {}` THEN UNDISCH_TAC `(p:real^3) IN c` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN convex hull {p}` THEN
    REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~(UNIONS k INTER {x:real^3 | a dot x = t} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`y:real^3`; `&0`] THEN
    REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN convex hull c` THEN
  SUBGOAL_THEN `c = (p:real^3) INSERT (c DELETE p)` SUBST1_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN c` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
      (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `t < (a:real^3) dot b` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SSL_HULL_GT THEN
      EXISTS_TAC `c DELETE (p:real^3)` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
  ABBREV_TAC `r = (t - (a:real^3) dot p) / (a dot b - a dot p)` THEN
    SUBGOAL_THEN `&0 < r /\ r < &1 /\ r * ((a:real^3) dot b - a dot p) = t - a dot p`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN
      SUBGOAL_THEN `&0 < (a:real^3) dot b - a dot p /\ &0 < t - a dot p`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3) IN convex hull c /\ (p:real^3) IN convex hull c`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(b:real^3) IN convex hull (c DELETE p)` THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^3) IN s ==> x IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p + r % (b - p):real^3`; `v / r`] THEN
  SUBGOAL_THEN `(a:real^3) dot x = a dot p + v * (a dot b - a dot p)` ASSUME_TAC
    THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `u + v = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `convex hull c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p + r % (b - p) = (&1 - r) % p + r % (b:real^3)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; REAL_LT_IMP_LE];
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
    UNDISCH_TAC `r * ((a:real^3) dot b - a dot p) = t - a dot p` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `(a:real^3) dot b - a dot p` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `r * ((a:real^3) dot b - a dot p) = t - a dot p` THEN
    UNDISCH_TAC `(a:real^3) dot x = a dot p + v * (a dot b - a dot p)` THEN
    UNDISCH_TAC `(a:real^3) dot x <= t` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_ARITH `(p + r % (b - p)) - p:real^3 = r % (b - p)`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `u + v = &1` THEN
    REWRITE_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC];
   REWRITE_TAC[MOI_CON_IN_CONE] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS k INTER {x | a dot x = t}` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t:real`; `y:real^3`]
      MOI_SSL_HULL_GT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `convex hull c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `p + m % (y - p):real^3 = (&1 - m) % p + m % y`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC];
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `m * (t - ap) <= &1 * (t - ap) ==> ap + m * (t - ap) <= t`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]);;

(* The frontier of the cone region: the section at t together with the    *)
(* cone from p over the boundary of the section.                           *)

let MOI_SSL_CONE_FRONTIER = prove
 (`!(m:real^3->bool) s (a:real^3) p t.
     closed m /\ frontier m = s /\ p IN s /\ a dot p < t /\
     m INTER {x | a dot x <= t} =
       UNIONS {segment[p,y] | y IN m INTER {x | a dot x = t}} /\
     relative_interior (m INTER {x | a dot x = t}) =
       (m INTER {x | a dot x = t}) DIFF (s INTER {x | a dot x = t}) /\
     affine hull (m INTER {x | a dot x = t}) = {x | a dot x = t} /\
     ~(s INTER {x | a dot x = t} = {})
     ==> (m INTER {x | a dot x = t}) UNION (s INTER {x | a dot x <= t}) =
         (m INTER {x | a dot x = t}) UNION
         UNIONS {segment[p,y] | y IN s INTER {x | a dot x = t}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = (m:real^3->bool) INTER {x | a dot x = t}` THEN
  ABBREV_TAC `j = (s:real^3->bool) INTER {x | a dot x = t}` THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET m /\ interior m = m DIFF s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `frontier m = (s:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED] THEN REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN MP_TAC(ISPEC `m:real^3->bool` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["j"; "d"] THEN UNDISCH_TAC `(s:real^3->bool) SUBSET m` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN m /\ a dot z <= t <=>
                 ?y r. y IN d /\ &0 <= r /\ r <= &1 /\ z = p + r % (y - p)`
  (LABEL_TAC "cone") THENL
   [GEN_TAC THEN
    MP_TAC(ASSUME `m INTER {x:real^3 | a dot x <= t} = UNIONS {segment[p,y] | y IN d}`) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_CON_IN_CONE] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN d ==>
     (~(y IN j) <=> ?e. &0 < e /\ !z. a dot z = t /\ dist(y,z) < e ==> z IN d)`
  (LABEL_TAC "ri") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `d:real^3->bool`] IN_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[IN_DIFF; SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; MOI_CON_IN_CONE] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
  [STRIP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISJ2_TAC THEN
  USE_THEN "cone" (MP_TAC o fst o EQ_IMP_RULE o SPEC `x:real^3`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `(y:real^3) IN j` THENL
   [MAP_EVERY EXISTS_TAC [`y:real^3`; `r:real`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [UNDISCH_TAC `~(j:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y0:real^3`) THEN
    MAP_EVERY EXISTS_TAC [`y0:real^3`; `&0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `(x:real^3) IN interior m` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[ASSUME `interior m = (m:real^3->bool) DIFF s`; IN_DIFF;
                ASSUME `(x:real^3) IN s`]] THEN
  SUBGOAL_THEN `(a:real^3) dot y = t /\ (y:real^3) IN m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN d` THEN EXPAND_TAC "d" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &1` THENL
   [UNDISCH_TAC `x = p + r % (y - p):real^3` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `p + y - p:real^3 = y`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    UNDISCH_TAC `~((y:real^3) IN j)` THEN EXPAND_TAC "j" THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  USE_THEN "ri" (MP_TAC o SPEC `y:real^3`) THEN
  REWRITE_TAC[ASSUME `(y:real^3) IN d`; ASSUME `~((y:real^3) IN j)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `f = \z:real^3. p + ((t - a dot p) / (a dot z - a dot p)) % (z - p)` THEN
  SUBGOAL_THEN `open {z:real^3 | z IN {z | a dot z > a dot p} INTER {z | a dot z < t} /\
                             (f:real^3->real^3) z IN ball(y,e)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_BALL] THEN
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
    EXPAND_TAC "f" THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | a dot p < a dot z}` THEN
    REWRITE_TAC[MOI_SSL_RADIAL_CONT] THEN SET_TAC[real_gt];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot x = a dot p + r * (t - a dot p)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB]; ALL_TAC] THEN
  SUBGOAL_THEN `{z:real^3 | z IN {z | a dot z > a dot p} INTER {z | a dot z < t} /\
                             (f:real^3->real^3) z IN ball(y,e)} SUBSET interior m`
  MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; IN_BALL; real_gt] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((a:real^3) dot z - a dot p = &0) /\ ~(t - (a:real^3) dot p = &0)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) z IN d` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z:real^3. a dot z = t /\ dist (y,z) < e ==> z IN d`)
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
      UNDISCH_TAC `~((a:real^3) dot z - a dot p = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN m /\ a dot z <= t` (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cone" (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`(f:real^3->real^3) z`;
                          `((a:real^3) dot z - a dot p) / (t - a dot p)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `a < t ==> &0 < t - a`] THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "f" THEN
      REWRITE_TAC[VECTOR_ARITH `(p + c % (z - p)) - p:real^3 = c % (z - p)`] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `((a:real^3) dot z - a dot p) / (t - a dot p) *
                    (t - a dot p) / (a dot z - a dot p) = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `~((a:real^3) dot z - a dot p = &0)` THEN
        UNDISCH_TAC `~(t - (a:real^3) dot p = &0)` THEN CONV_TAC REAL_FIELD;
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) (p + r % (y - p)) = y` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB; ASSUME `(a:real^3) dot y = t`] THEN
    REWRITE_TAC[VECTOR_ARITH `(p + r % (y - p)) - p:real^3 = r % (y - p)`;
                REAL_ARITH `(ap + r * (t - ap)) - ap = r * (t - ap)`;
                VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(t - (a:real^3) dot p) / (r * (t - a dot p)) * r = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(r = &0) /\ ~(c = &0) ==> c / (r * c) * r = &1`) THEN
      ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_BALL; real_gt] THEN
  ASM_REWRITE_TAC[DIST_REFL] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB; ASSUME `(a:real^3) dot y = t`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < r * (t - p) ==> p < p + r * (t - p)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `r * (t - p) < &1 * (t - p) ==> p + r * (t - p) < t`) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
   STRIP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x:real^3`)) THEN
  SUBGOAL_THEN `(y:real^3) IN d /\ (y:real^3) IN s /\ a dot y = t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN j` THEN UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN
    EXPAND_TAC "j" THEN SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &1` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `p + y - p:real^3 = y`];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `p + r % (y - p) IN m /\ (a:real^3) dot (p + r % (y - p)) <= t`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "cone" (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`y:real^3`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?del. &0 < del /\
                      !z:real^3. dist(p + r % (y - p),z) < del ==> z IN m`
  (X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `p + r % (y - p) IN interior (m:real^3->bool)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERIOR; SUBSET; IN_BALL];
    ALL_TAC] THEN
  USE_THEN "ri" (MP_TAC o SPEC `y:real^3`) THEN
  REWRITE_TAC[ASSUME `(y:real^3) IN d`; ASSUME `(y:real^3) IN j`] THEN
  EXISTS_TAC `del / r` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p + r % (z - p) IN m /\ (a:real^3) dot (p + r % (z - p)) <= t` MP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z:real^3. dist(p + r % (y - p),z) < del ==> z IN m`)
          (concl th))) THEN
      REWRITE_TAC[dist; VECTOR_ARITH
        `(p + r % (y - p)) - (p + r % (z - p)):real^3 = r % (y - z)`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      UNDISCH_TAC `dist(y:real^3,z) < del / r` THEN REWRITE_TAC[dist] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
      MATCH_MP_TAC(REAL_ARITH `r * (t - p) <= &1 * (t - p) ==> p + r * (t - p) <= t`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "cone" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^3) dot w = t` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN d` THEN EXPAND_TAC "d" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  UNDISCH_TAC `p + r % (z - p) = p + r' % (w - p):real^3` THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(AP_TERM `\v:real^3. (a:real^3) dot v` th)) THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_RCANCEL] THEN
  SUBGOAL_THEN `~(t - (a:real^3) dot p = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH `p + r % (z - p) = p + r % (w - p) <=> r % (z - w):real^3 = vec 0`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]]);;

(* The sphere below a level just above the lowest vertex is simply imbedded *)
(* (Moise p.124, Lemma 4, by Theorem 10 = CONE_DISK_SIMPLE).                *)

let MOI_SSL_CONE_BOTTOM = prove
 (`!s (a:real^3) lo hi k t.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w) /\
     lo < t /\ t < hi /\ (!w. {w} IN k /\ a dot w <= t ==> a dot w = lo)
     ==> moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = t}) UNION
                          (s INTER {x | a dot x <= t}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`]
    MOI_SSL_FIB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(SPEC `t:real` (last(CONJUNCTS th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `m = (s:real^3->bool) UNION inside s` THEN
  ABBREV_TAC `d = (m:real^3->bool) INTER {x | a dot x = t}` THEN
  ABBREV_TAC `j = (s:real^3->bool) INTER {x | a dot x = t}` THEN
  MP_TAC(ISPECL [`a:real^3`; `t:real`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_SSL_PLANE_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(j:real^3->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCX_CELL_SPHERE; MOI_SCD_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN m /\ a dot p = lo` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `m INTER {x:real^3 | a dot x = lo} = {p}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^3} IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SSL_EXTREME_VERTEX THEN EXISTS_TAC `a:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m INTER {x:real^3 | a dot x <= t} = UNIONS {segment[p,y] | y IN d}`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS k = (m:real^3->bool)`)) THEN
    MATCH_MP_TAC MOI_SSL_CONE_REGION THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN
      UNDISCH_TAC `~(j:real^3->bool = {})` THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!v w:real^3. {v} IN k /\ {w} IN k /\ a dot v = a dot w
                                         ==> v = w`) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `s:real^3->bool`; `a:real^3`; `p:real^3`;
                 `t:real`] MOI_SSL_CONE_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CONE_DISK_SIMPLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN EXPAND_TAC "d" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(a:real^3) dot y = t` THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      REWRITE_TAC[REAL_ARITH `(&1 - u) * l + u * t = t <=> (&1 - u) * (l - t) = &0`;
                  REAL_ENTIRE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

(* Reversing the height (a |-> --a) keeps the fibred structure; the top     *)
(* cone (Moise p.124, Lemma 5) follows from the bottom one.                 *)

let MOI_SSL_FIBRED_NEG = prove
 (`!s (a:real^3) lo hi.
     moi_sch3_fibred s a lo hi ==> moi_sch3_fibred s (--a) (--hi) (--lo)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_fibred; DOT_LNEG; VECTOR_NEG_EQ_0] THEN
  REWRITE_TAC[REAL_ARITH `--x = --y <=> x = y`; REAL_LT_NEG2; REAL_LE_NEG2] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--y = t <=> y = --t`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_SSL_CONE_TOP = prove
 (`!s (a:real^3) lo hi k t.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w) /\
     lo < t /\ t < hi /\ (!w. {w} IN k /\ t <= a dot w ==> a dot w = hi)
     ==> moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = t}) UNION
                          (s INTER {x | t <= a dot x}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `--a:real^3`; `--hi`; `--lo`; `k:(real^3->bool)->bool`;
                 `--t`] MOI_SSL_CONE_BOTTOM) THEN
  ASM_SIMP_TAC[MOI_SSL_FIBRED_NEG; DOT_LNEG; REAL_LT_NEG2; REAL_LE_NEG2;
               REAL_ARITH `--x = --y <=> x = y`] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The triangulation k of the filled sphere: local finiteness, pureness,     *)
(* carriers, the local halfspace at a facet, two cells sharing a facet, and  *)
(* the sphere as the union of the free facets.                               *)
(* ------------------------------------------------------------------------- *)

(* Copy of MOI_FMB_SC_LF (pc_moi_fnd_m3b.ml, not loaded here).              *)

let MOI_SSL_SC_LF = prove
 (`!c:(real^N->bool)->bool. simplicial_complex c ==> lf_simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT]);;

let MOI_SSL_FILLED_CLOSURE = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> closure(inside s) = s UNION inside s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]);;

(* Every point of a triangulated closed region (the closure of its interior) *)
(* lies in a 3-simplex of the triangulation; every simplex is contained in  *)
(* a 3-simplex.                                                              *)

let MOI_SSL_PURE = prove
 (`!k:(real^3->bool)->bool.
     simplicial_complex k /\ UNIONS k SUBSET closure(interior(UNIONS k))
     ==> (!x. x IN UNIONS k ==> ?t. t IN k /\ aff_dim t = &3 /\ x IN t) /\
         (!s. s IN k /\ ~(s = {}) ==> ?t. t IN k /\ aff_dim t = &3 /\ s SUBSET t)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN UNIONS k ==> ?t. t IN k /\ aff_dim t = &3 /\ x IN t`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (k:(real^3->bool)->bool) /\
                  !t:real^3->bool. t IN k ==> compact t`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closed (UNIONS {t:real^3->bool | t IN k /\ aff_dim t = &3})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?r. &0 < r /\
          ball(x:real^3,r) INTER UNIONS {t | t IN k /\ aff_dim t = &3} = {}`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `closed (UNIONS {t:real^3->bool | t IN k /\ aff_dim t = &3})` THEN
      REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?y:real^3. y IN interior(UNIONS k) /\ dist(y,x) < r`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS k SUBSET closure(interior(UNIONS k:real^3->bool))` THEN
      REWRITE_TAC[SUBSET; CLOSURE_APPROACHABLE] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `interior(UNIONS {t:real^3->bool | t IN k /\ ~(aff_dim t = &3)}) = {}`
    MP_TAC THENL
     [MATCH_MP_TAC NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED THEN
      ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; FINITE_RESTRICT; IN_ELIM_THM;
                   COMPACT_IMP_CLOSED] THEN
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~(aff_dim(t:real^3->bool) = &3)` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR) THEN
      ASM_REWRITE_TAC[DIMINDEX_3];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
    SUBGOAL_THEN
     `ball(x:real^3,r) INTER interior(UNIONS k) SUBSET
      interior(UNIONS {t:real^3->bool | t IN k /\ ~(aff_dim t = &3)})`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN
      SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `UNIONS k:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC
       `ball(x:real^3,r) INTER UNIONS {t | t IN k /\ aff_dim t = &3} = {}` THEN
      REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM;
                  NOT_IN_EMPTY] THEN
      MESON_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    MATCH_MP_TAC(MESON[RELATIVE_INTERIOR_EQ_EMPTY]
      `convex (s:real^3->bool) /\ ~(s = {}) ==> ~(relative_interior s = {})`) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    can (term_match [] `!x:real^3. x IN UNIONS k ==> ?t. t IN k /\ aff_dim t = &3 /\ x IN t`)
      (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `t INTER s:real^3->bool`; `s:real^3->bool`]
    SUBSET_OF_FACE_OF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL] THEN REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    SET_TAC[]]);;

(* The carrier of a point: the simplex of k containing it in its relative   *)
(* interior; it is a face of every simplex of k containing the point.       *)

let MOI_SSL_CARRIER = prove
 (`!k (x:real^3).
     simplicial_complex k /\ x IN UNIONS k
     ==> ?c. c IN k /\ x IN relative_interior c /\
             !t. t IN k /\ x IN t ==> c face_of t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN UNIONS k` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `x:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^3->bool) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER c:real^3->bool) face_of c /\ (t INTER c) face_of t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET t INTER c` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `c:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    DISCH_TAC THEN
    SUBGOAL_THEN `t INTER c:real^3->bool = c` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM SET_TAC[]]);;

(* Near a relative interior point of a facet, a full-dimensional polytope   *)
(* contains the inner half ball (radial projection from an interior point).  *)

let MOI_SSL_FACET_LOCAL = prove
 (`!c f (y:real^3) a b.
     polytope c /\ ~(interior c = {}) /\ f face_of c /\ aff_dim f = &2 /\
     ~(a = vec 0) /\ c SUBSET {x | a dot x <= b} /\ f SUBSET {x | a dot x = b} /\
     y IN relative_interior f
     ==> ?r. &0 < r /\ !x. x IN ball(y,r) /\ a dot x <= b ==> x IN c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (c:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull f = {x:real^3 | a dot x = b}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->bool`; `{x:real^3 | a dot x = b}`]
      AFF_DIM_EQ_AFFINE_HULL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC;
      SIMP_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z0:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(interior c = {}:real^3->bool)`)) THEN
  SUBGOAL_THEN `(a:real^3) dot z0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN interior c` THEN REWRITE_TAC[IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z0 + (e / &2 / norm(a:real^3)) % a IN c` MP_TAC THENL
     [UNDISCH_TAC `ball(z0:real^3,e) SUBSET c` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z:real^3,z + y) = norm y`] THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NUM;
                   REAL_DIV_RMUL; NORM_EQ_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `c SUBSET {x:real^3 | a dot x <= b}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(fun th -> DISCH_THEN
      (MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    SUBGOAL_THEN `&0 < e / &2 / norm(a:real^3) * (a dot a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_ARITH `&0 < e ==> &0 < e / &2`] THEN
      ASM_REWRITE_TAC[DOT_POS_LT];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^3) dot y = b /\ (y:real^3) IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `g = \x:real^3. z0 + ((b - a dot z0) / (a dot x - a dot z0)) % (x - z0)` THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous at y` MP_TAC THENL
   [MP_TAC(ISPECL [`a:real^3`; `z0:real^3`; `(a:real^3) dot z0`; `b - (a:real^3) dot z0`]
      MOI_SSL_RADIAL_CONT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `{x:real^3 | a dot z0 < a dot x}`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a < x <=> x > a`; OPEN_HALFSPACE_GT];
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^3->real^3) y = y` SUBST1_TAC THENL
   [EXPAND_TAC "g" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b - (a:real^3) dot z0 = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (min e ((b - (a:real^3) dot z0) / (&2 * norm a)))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_MUL; NORM_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^3) dot z0 < a dot x` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((a:real^3) dot x - a dot y) <= norm a * dist(y,x)` MP_TAC THENL
     [REWRITE_TAC[dist] THEN
      MP_TAC(ISPECL [`a:real^3`; `y - x:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
      REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `dist(y:real^3,x) < (b - a dot z0) / (&2 * norm(a:real^3))` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL; NORM_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN
    MP_TAC(ISPECL [`y:real^3`; `x:real^3`] DIST_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^3) dot x = b` THENL
   [SUBGOAL_THEN `(x:real^3) IN f` MP_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,e) INTER {x | a dot x = b} SUBSET f` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^3->real^3) x IN f` MP_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,e) INTER {x | a dot x = b} SUBSET f` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "g" THEN REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
        UNDISCH_TAC `(a:real^3) dot z0 < a dot x` THEN CONV_TAC REAL_FIELD];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x = z0 + ((a dot x - a dot z0) / (b - a dot z0)) % ((g:real^3->real^3) x - z0)`
  SUBST1_TAC THENL
   [EXPAND_TAC "g" THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + c % (x - z0)) - z0:real^3 = c % (x - z0)`;
                VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `((a:real^3) dot x - a dot z0) / (b - a dot z0) *
                  (b - a dot z0) / (a dot x - a dot z0) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(p = &0) /\ ~(q = &0) ==> p / q * q / p = &1`) THEN
      ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `z0 + r % (w - z0):real^3 = (&1 - r) % z0 + r % w`] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - (a:real^3) dot z0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE;
               REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

(* A face of a full-dimensional polytope is exposed by a nonzero normal.    *)

let MOI_SSL_FACE_EXPOSED = prove
 (`!c f:real^3->bool.
     polytope c /\ f face_of c /\ ~(f = {}) /\ ~(f = c)
     ==> ?a b. ~(a = vec 0) /\ c SUBSET {x | a dot x <= b} /\
               f = c INTER {x | a dot x = b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `f:real^3->bool`] EXPOSED_FACE_OF_POLYHEDRON) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN REWRITE_TAC[exposed_face_of] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `f = c INTER {x:real^3 | vec 0 dot x = b}` THEN
  REWRITE_TAC[DOT_LZERO] THEN ASM_CASES_TAC `&0 = b` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; INTER_EMPTY; UNIV_GSPEC; INTER_UNIV]);;

(* Two full-dimensional polytopes meeting exactly in a common 2-face cover  *)
(* a neighbourhood of each relative interior point of the face.             *)

let MOI_SSL_TWO_CELL = prove
 (`!c1 c2 f (y:real^3).
     polytope c1 /\ ~(interior c1 = {}) /\ polytope c2 /\ ~(interior c2 = {}) /\
     f face_of c1 /\ f face_of c2 /\ aff_dim f = &2 /\ c1 INTER c2 = f /\
     y IN relative_interior f
     ==> y IN interior(c1 UNION c2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(f:real^3->bool = {}) /\ ~(f = c1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `aff_dim({}:real^3->bool) = &2` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      MP_TAC(ISPEC `c1:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR) THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^3->bool`; `f:real^3->bool`] MOI_SSL_FACE_EXPOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `f SUBSET {x:real^3 | a dot x = b}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^3->bool`; `f:real^3->bool`; `y:real^3`; `a:real^3`; `b:real`]
    MOI_SSL_FACET_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN f` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `c2 SUBSET {x:real^3 | --a dot x <= --b}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; DOT_LNEG; REAL_LE_NEG2] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot y = b` ASSUME_TAC THENL
     [UNDISCH_TAC `f SUBSET {x:real^3 | a dot x = b}` THEN
      UNDISCH_TAC `(y:real^3) IN f` THEN SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `m = min (&1 / &2) (r1 / (&2 * (norm(z - y:real^3) + &1)))` THEN
    SUBGOAL_THEN `&0 < m /\ m < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_LT_DIV THEN
      MP_TAC(ISPEC `z - y:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `y + m % (z - y:real^3) IN c1 /\ y + m % (z - y) IN c2`
    MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_BALL; NORM_ARITH `dist(y:real^3,y + v) = norm v`] THEN
        REWRITE_TAC[NORM_MUL; DOT_RADD; DOT_RMUL; DOT_RSUB] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
          SUBGOAL_THEN `&0 < &2 * (norm(z - y:real^3) + &1)` ASSUME_TAC THENL
           [MP_TAC(ISPEC `z - y:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `m * (&2 * (norm(z - y:real^3) + &1)) <= r1` MP_TAC THENL
           [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN EXPAND_TAC "m" THEN
            REAL_ARITH_TAC;
            ALL_TAC] THEN
          MP_TAC(SPECL [`m:real`; `norm(z - y:real^3)`] REAL_LE_MUL) THEN
          ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
          UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= m * (b - az) ==> b + m * (az - b) <= b`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[VECTOR_ARITH `y + m % (z - y):real^3 = (&1 - m) % y + m % z`] THEN
        MATCH_MP_TAC IN_CONVEX_SET THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `(y:real^3) IN f` THEN
        UNDISCH_TAC `c1 INTER c2 = f:real^3->bool` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot (y + m % (z - y)) = b` MP_TAC THENL
     [UNDISCH_TAC `y + m % (z - y:real^3) IN c1 /\ y + m % (z - y) IN c2` THEN
      UNDISCH_TAC `c1 INTER c2 = f:real^3->bool` THEN
      UNDISCH_TAC `f SUBSET {x:real^3 | a dot x = b}` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
    REWRITE_TAC[REAL_ARITH `b + m * (az - b) = b <=> m * (az - b) = &0`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c2:real^3->bool`; `f:real^3->bool`; `y:real^3`; `--a:real^3`; `--b`]
    MOI_SSL_FACET_LOCAL) THEN
  SUBGOAL_THEN `f SUBSET {x:real^3 | --a dot x = --b}` ASSUME_TAC THENL
   [UNDISCH_TAC `f SUBSET {x:real^3 | a dot x = b}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; DOT_LNEG; REAL_EQ_NEG2];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VECTOR_NEG_EQ_0] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min r1 r2` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL; IN_UNION] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(a:real^3) dot x <= b` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN ball(y,r1) /\ a dot x <= b ==> x IN c1`)
        (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL];
    DISJ2_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN ball(y,r2) /\ --a dot x <= --b ==> x IN c2`)
        (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL; DOT_LNEG] THEN ASM_REAL_ARITH_TAC]);;

(* Near any point x of a pure triangulated region, every point lies in a    *)
(* 3-simplex through x.                                                      *)

let MOI_SSL_LOCAL_TETS = prove
 (`!k (x:real^3).
     simplicial_complex k /\ UNIONS k SUBSET closure(interior(UNIONS k)) /\
     x IN UNIONS k
     ==> ?r. &0 < r /\
             !y. y IN UNIONS k /\ dist(x,y) < r
                 ==> ?t. t IN k /\ aff_dim t = &3 /\ x IN t /\ y IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_SIMP_TAC[MOI_SSL_SC_LF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k:(real^3->bool)->bool` MOI_SSL_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^3->bool` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t':real^3->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Interior points propagate along the relative interior of a convex set    *)
(* contained in every member of a family of convex sets.                    *)

let MOI_SSL_RELINT_HOMOG = prove
 (`!(f:(real^3->bool)->bool) rho y z.
     (!t. t IN f ==> convex t /\ rho SUBSET t) /\
     y IN relative_interior rho /\ z IN rho /\ z IN interior (UNIONS f)
     ==> y IN interior (UNIONS f)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `y:real^3 = z` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN interior (UNIONS f)` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:real^3) IN relative_interior rho` THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < norm(y - z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `m = d / (&2 * norm(y - z:real^3))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y + m % (y - z:real^3) IN rho` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(y:real^3,y + v) = norm v`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
      EXPAND_TAC "m" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ;
        REAL_FIELD `&0 < n ==> d / (&2 * n) * n = d / &2`] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH
       `y + m % (y - z):real^3 = (&1 - --m) % y + --m % z`] THEN
      MP_TAC(ISPEC `rho:real^3->bool` AFFINE_AFFINE_HULL) THEN
      REWRITE_TAC[AFFINE_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[HULL_INC; SUBSET; RELATIVE_INTERIOR_SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `th = m / (&1 + m)` THEN
  SUBGOAL_THEN `&0 < th /\ th < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < m ==> &0 < &1 + m`;
      REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `th * r:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `z + inv th % (w - y:real^3) IN UNIONS f` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z:real^3,z + v) = norm v`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < t ==> abs t = t`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `dist(y:real^3,w) < th * r` THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[NORM_ARITH `norm(y - w:real^3) = norm(w - y)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - th) * (&1 + m) = &1 /\ (&1 - th) * m = th`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN
    MATCH_MP_TAC(REAL_FIELD `~(&1 + m = &0)
      ==> (&1 - m / (&1 + m)) * (&1 + m) = &1 /\
          (&1 - m / (&1 + m)) * m = m / (&1 + m)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `w = (&1 - th) % (y + m % (y - z)) + th % (z + inv th % (w - y:real^3))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH
     `(a:real) % (y + m % (y - z)) + b % (z + c % (w - y)) =
      (a * (&1 + m)) % y - (a * m) % z + b % z + (b * c) % (w - y:real^3)`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[SUBSET]);;

(* A simplex of k meeting the relative interior of another one in a point   *)
(* of that relative interior contains it.                                   *)

let MOI_SSL_RELINT_SUBSET = prove
 (`!k c t (x:real^3).
     simplicial_complex k /\ c IN k /\ t IN k /\ x IN relative_interior c /\
     x IN t
     ==> c SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c INTER t:real^3->bool) face_of c` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (k:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real^3->bool`; `t:real^3->bool`] o
      last o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `c INTER t:real^3->bool = c` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `c INTER t:real^3->bool`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier; SUBSET; IN_INTER; IN_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[]);;

(* Interior points of the region propagate along relative interiors of     *)
(* simplices.                                                                *)

let MOI_SSL_CARRIER_SIDE = prove
 (`!k c (x:real^3) y.
     simplicial_complex k /\ UNIONS k SUBSET closure(interior(UNIONS k)) /\
     c IN k /\ x IN relative_interior c /\ x IN interior(UNIONS k) /\
     y IN relative_interior c
     ==> y IN interior(UNIONS k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS k` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_LOCAL_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^3) IN interior(UNIONS k)` THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `f = {t:real^3->bool | t IN k /\ aff_dim t = &3 /\ c SUBSET t}` THEN
  SUBGOAL_THEN `UNIONS f SUBSET UNIONS (k:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN interior(UNIONS f)` MP_TAC THENL
   [MATCH_MP_TAC MOI_SSL_RELINT_HOMOG THEN
    MAP_EVERY EXISTS_TAC [`c:real^3->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min r r'` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL] THEN
      X_GEN_TAC `y':real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y':real^3) IN UNIONS k` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(x:real^3,r') SUBSET UNIONS k` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y':real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SSL_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `x:real^3`] THEN
      ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[SUBSET_INTERIOR; SUBSET]]);;

(* The sphere is a union of simplices of the triangulation of its filling: *)
(* a simplex whose relative interior meets the sphere lies in it.           *)

let MOI_SSL_SPHERE_SIMPLICES = prove
 (`!s k c (x:real^3).
     pl_sphere 2 s /\ simplicial_complex k /\ UNIONS k = s UNION inside s /\
     c IN k /\ x IN relative_interior c /\ x IN s
     ==> c SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                       ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_SSL_FILLED_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRONTIER_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (c:real^3->bool) /\ closed c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior c /\ ~(z IN s)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((c:real^3->bool) SUBSET s)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `c:real^3->bool` CONVEX_CLOSURE_RELATIVE_INTERIOR) THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN UNIONS k` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `c:real^3->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN interior(UNIONS k)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN UNIONS k` THEN UNDISCH_TAC `~((z:real^3) IN s)` THEN
    REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`;
                ASSUME `interior (s UNION inside s) = inside (s:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `c:real^3->bool`; `z:real^3`; `x:real^3`]
    MOI_SSL_CARRIER_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`;
                ASSUME `interior (s UNION inside s) = inside (s:real^3->bool)`;
                ASSUME `closure (inside s) = s UNION inside (s:real^3->bool)`] THEN
    REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`;
              ASSUME `interior (s UNION inside s) = inside (s:real^3->bool)`] THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN
  UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[]);;

let MOI_SSL_SPHERE_UNIONS = prove
 (`!s k:(real^3->bool)->bool.
     pl_sphere 2 s /\ simplicial_complex k /\ UNIONS k = s UNION inside s
     ==> s = UNIONS {c | c IN k /\ c SUBSET s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_CARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `c:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SSL_SPHERE_SIMPLICES THEN
    MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The slab around a vertex.  Setting moi_ssl_slab_hyp (the hypotheses of    *)
(* MOI_SSL_SLAB_STMT), interior and frontier criteria for unions of slab     *)
(* cells, and sections of 3-simplices by levels.                             *)
(* ------------------------------------------------------------------------- *)

let moi_ssl_slab_hyp = new_definition
 `moi_ssl_slab_hyp (s:real^3->bool) (a:real^3) lo hi k (v:real^3) t1 t2 <=>
    pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
    simplicial_complex k /\ UNIONS k = s UNION inside s /\
    (!x y. {x} IN k /\ {y} IN k /\ a dot x = a dot y ==> x = y) /\
    lo < t1 /\ t1 < a dot v /\ a dot v < t2 /\ t2 < hi /\ {v} IN k /\
    (!w. {w} IN k /\ t1 <= a dot w /\ a dot w <= t2 ==> w = v)`;;

(* The star part of the slab.  The sections at the vertex level of the      *)
(* 3-simplices at v that cross it form a PL 2-cell, and the slab part of    *)
(* the closed star of v has a simply imbedded frontier.  Proved in          *)
(* pc_moi_sch3_slabc; used by pc_moi_sch3_slabb.                            *)

let MOI_SSL_STAR_STMT =
 `!(s:real^3->bool) (a:real^3) (lo:real) (hi:real) (k:(real^3->bool)->bool)
   (v:real^3) (t1:real) (t2:real).
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> (?j0:real^3->bool.
            pl_cell_with_boundary 2
              (UNIONS {t INTER {x:real^3 | a dot x = a dot v} | t |
                       t IN k /\ aff_dim t = &3 /\ v IN t /\
                       ~(interior t INTER {x:real^3 | a dot x = a dot v} = {})})
              j0) /\
         moi_sch3_simple
           (frontier (UNIONS {t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2} | t |
                              t IN k /\ aff_dim t = &3 /\ v IN t}))`;;

let MOI_SSL_SLAB_FACTS = prove
 (`!s (a:real^3) lo hi k v t1 t2.
     moi_ssl_slab_hyp s a lo hi k v t1 t2
     ==> ~(a = vec 0) /\ closed (s UNION inside s) /\
         compact (s UNION inside s) /\ closed s /\
         frontier (s UNION inside s) = s /\
         interior (s UNION inside s) = inside s /\
         inside s INTER s = {} /\
         UNIONS k SUBSET closure(interior(UNIONS k)) /\
         t1 < t2 /\ lo < a dot v /\ a dot v < hi /\
         v IN s UNION inside s /\
         (!w. {w} IN k ==> w = v \/ a dot w < t1 \/ t2 < a dot w) /\
         (!t. lo < t /\ t < hi
              ==> pl_cell_with_boundary 2 ((s UNION inside s) INTER {x | a dot x = t})
                                          (s INTER {x | a dot x = t}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ssl_slab_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`]
    MOI_SSL_FIB_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC [el 1 ths; el 2 ths; el 3 ths; el 4 ths; el 6 ths; last ths]) THEN
  SUBGOAL_THEN `~(a:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_sch3_fibred s (a:real^3) lo hi` THEN
    SIMP_TAC[moi_sch3_fibred];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FRONTIER_CLOSED];
    REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`;
                ASSUME `interior (s UNION inside s) = inside (s:real^3->bool)`] THEN
    ASM_SIMP_TAC[MOI_SSL_FILLED_CLOSURE; SUBSET_REFL];
    UNDISCH_TAC `t1 < (a:real^3) dot v` THEN UNDISCH_TAC `(a:real^3) dot v < t2` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `lo < t1` THEN UNDISCH_TAC `t1 < (a:real^3) dot v` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `t2 < hi` THEN UNDISCH_TAC `(a:real^3) dot v < t2` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `UNIONS k = s UNION inside (s:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `w:real^3 = v` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t2:real`)) (concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Basic facts on the simplices of a finite simplicial complex.             *)

let MOI_SSL_SC_INTER = prove
 (`!k s t:real^N->bool.
     simplicial_complex k /\ s IN k /\ t IN k
     ==> (s INTER t) face_of s /\ (s INTER t) face_of t /\ (s INTER t) IN k`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_SSL_SC_SIMPLEX = prove
 (`!k s:real^3->bool.
     simplicial_complex k /\ s IN k
     ==> convex s /\ compact s /\ closed s /\ polytope s /\
         (aff_dim s = &3 ==> ~(interior s = {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CLOSED;
               SIMPLEX_IMP_POLYTOPE] THEN
  DISCH_TAC THEN MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
  ASM_SIMP_TAC[DIMINDEX_3; SIMPLEX_IMP_CONVEX]);;

(* The interior of a closed slab is the open slab.                          *)

let MOI_SSL_INTERIOR_SLAB = prove
 (`!(a:real^3) t1 t2.
     ~(a = vec 0)
     ==> interior {y | t1 <= a dot y /\ a dot y <= t2} =
         {y | t1 < a dot y /\ a dot y < t2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y:real^3 | t1 <= a dot y /\ a dot y <= t2} =
                {y | a dot y >= t1} INTER {y | a dot y <= t2}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]);;

(* Interior criterion: a point of the open slab off the sphere, all of whose *)
(* 3-simplices are present, is interior to the union of the present slab    *)
(* cells.                                                                    *)

let MOI_SSL_INT_CRIT = prove
 (`!s k (a:real^3) t1 t2 f x.
     pl_sphere 2 s /\ simplicial_complex k /\ UNIONS k = s UNION inside s /\
     f SUBSET {t | t IN k /\ aff_dim t = &3} /\
     x IN UNIONS k /\ ~(x IN s) /\ t1 < a dot x /\ a dot x < t2 /\
     (!t. t IN k /\ aff_dim t = &3 /\ x IN t ==> t IN f)
     ==> x IN interior (UNIONS {t INTER {y | t1 <= a dot y /\ a dot y <= t2} |
                                t IN f})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  SUBGOAL_THEN `UNIONS k SUBSET closure(interior(UNIONS k:real^3->bool))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_SSL_FILLED_CLOSURE; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN interior(UNIONS k)` MP_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN UNIONS k` THEN UNDISCH_TAC `~((x:real^3) IN s)` THEN
    REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`;
                ASSUME `interior (s UNION inside s) = inside (s:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `x:real^3`] MOI_SSL_LOCAL_TETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r3. &0 < r3 /\ !y:real^3. dist(x,y) < r3 ==> t1 < a dot y /\ a dot y < t2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `{y:real^3 | a dot y > t1} INTER {y | a dot y < t2}`
      OPEN_CONTAINS_BALL) THEN
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_INTER; IN_ELIM_THM; real_gt] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min r1 (min r2 r3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN] THEN X_GEN_TAC `y:real^3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS k` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x:real^3,r1) SUBSET UNIONS k` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `r2:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `t INTER {y:real^3 | t1 <= a dot y /\ a dot y <= t2}` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `t:real^3->bool` THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r3:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Frontier criterion: a point of the union of slab cells lies on its        *)
(* frontier if it is on the sphere, on a boundary level, or in the open slab *)
(* on an absent 3-simplex.                                                   *)

let MOI_SSL_FR_CRIT = prove
 (`!s k (a:real^3) t1 t2 f x.
     pl_sphere 2 s /\ simplicial_complex k /\ UNIONS k = s UNION inside s /\
     ~(a = vec 0) /\
     f SUBSET {t | t IN k /\ aff_dim t = &3} /\
     x IN UNIONS {t INTER {y | t1 <= a dot y /\ a dot y <= t2} | t IN f} /\
     (x IN s \/ a dot x = t1 \/ a dot x = t2 \/
      (t1 < a dot x /\ a dot x < t2 /\
       ?t. t IN k /\ aff_dim t = &3 /\ x IN t /\ ~(t IN f)))
     ==> x IN frontier (UNIONS {t INTER {y | t1 <= a dot y /\ a dot y <= t2} |
                                t IN f})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  ABBREV_TAC `r = UNIONS {t INTER {y:real^3 | t1 <= a dot y /\ a dot y <= t2} |
                          t IN f}` THEN
  SUBGOAL_THEN `(r:real^3->bool) SUBSET UNIONS k /\
                r SUBSET {y | t1 <= a dot y /\ a dot y <= t2}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    UNDISCH_TAC `f SUBSET {t:real^3->bool | t IN k /\ aff_dim t = &3}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN
  SUBGOAL_THEN `(x:real^3) IN closure r` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `interior r SUBSET {y:real^3 | t1 < a dot y /\ a dot y < t2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior {y:real^3 | t1 <= a dot y /\ a dot y <= t2}` THEN
    ASM_SIMP_TAC[SUBSET_INTERIOR; MOI_SSL_INTERIOR_SLAB; SUBSET_REFL];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `interior r SUBSET inside (s:real^3->bool)` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> SUBST1_TAC(SYM(CONJUNCT1(CONJUNCT2 th)))) THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      UNDISCH_TAC `(r:real^3->bool) SUBSET UNIONS k` THEN
      REWRITE_TAC[ASSUME `UNIONS k = s UNION inside (s:real^3->bool)`];
      ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[];
    UNDISCH_TAC `interior r SUBSET {y:real^3 | t1 < a dot y /\ a dot y < t2}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    UNDISCH_TAC `interior r SUBSET {y:real^3 | t1 < a dot y /\ a dot y < t2}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN interior r` THEN REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^3. y IN interior t /\ dist(x,y) < e` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` CONVEX_CLOSURE_INTERIOR) THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:real^3->bool. (x:real^3) IN u`) THEN
    ASM_REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN r` MP_TAC THENL
   [UNDISCH_TAC `ball(x:real^3,e) SUBSET r` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "r" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(t':real^3->bool) IN k /\ aff_dim t' = &3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `f SUBSET {t:real^3->bool | t IN k /\ aff_dim t = &3}` THEN
    UNDISCH_TAC `(t':real^3->bool) IN f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN t'` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN u` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t':real^3->bool = t)` ASSUME_TAC THENL
   [UNDISCH_TAC `(t':real^3->bool) IN f` THEN UNDISCH_TAC `~((t:real^3->bool) IN f)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`; `t':real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t INTER t':real^3->bool = t)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `t':real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t':real^3->bool`]
          MOI_SSL_SC_SIMPLEX) THEN ASM_SIMP_TAC[];
        UNDISCH_TAC `(t INTER t':real^3->bool) face_of t'` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(t':real^3->bool = t)` THEN MESON_TAC[]];
      ASM_REWRITE_TAC[INT_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN t /\ y IN relative_interior t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN interior t` THEN SET_TAC[];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `t INTER t':real^3->bool`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier; SUBSET; IN_DIFF; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]);;

(* A convex set with nonempty interior and points on both sides of a level  *)
(* meets that level in interior points.                                      *)

let MOI_SSL_INTERIOR_LEVEL = prove
 (`!t (a:real^3) b x1 x2.
     convex t /\ ~(interior t = {}) /\ x1 IN t /\ x2 IN t /\
     a dot x1 < b /\ b < a dot x2
     ==> ~(interior t INTER {x | a dot x = b} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN t ==> !e. &0 < e ==> ?y. y IN interior t /\ dist(y,x) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `t:real^3->bool` CONVEX_CLOSURE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:real^3->bool. (x:real^3) IN u`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y1:real^3. y1 IN interior t /\ a dot y1 < b` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x1:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(b - a dot x1) / (norm(a:real^3) + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `y - x1:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    UNDISCH_TAC `dist(y:real^3,x1) < (b - a dot x1) / (norm(a:real^3) + &1)` THEN
    REWRITE_TAC[dist] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE] THEN
    REWRITE_TAC[DOT_RSUB] THEN
    MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN MP_TAC(ISPEC `y - x1:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(a:real^3)`,`na:real`) THEN SPEC_TAC(`norm(y - x1:real^3)`,`nd:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `na * nd <= (na + &1) * nd` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?y2:real^3. y2 IN interior t /\ b < a dot y2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x2:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(a dot x2 - b) / (norm(a:real^3) + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `y - x2:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    UNDISCH_TAC `dist(y:real^3,x2) < (a dot x2 - b) / (norm(a:real^3) + &1)` THEN
    REWRITE_TAC[dist] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE] THEN
    REWRITE_TAC[DOT_RSUB] THEN
    MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN MP_TAC(ISPEC `y - x2:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(a:real^3)`,`na:real`) THEN SPEC_TAC(`norm(y - x2:real^3)`,`nd:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `na * nd <= (na + &1) * nd` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interior t:real^3->bool`; `y1:real^3`; `y2:real^3`; `a:real^3`; `b:real`]
    CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM]);;

(* A polytope meeting a level in interior points is cut in a 2-dimensional  *)
(* polytope spanning the level, with relative interior the interior points. *)

let MOI_SSL_LEVEL_SECTION = prove
 (`!t (a:real^3) b.
     polytope t /\ ~(a = vec 0) /\ ~(interior t INTER {x | a dot x = b} = {})
     ==> polytope (t INTER {x | a dot x = b}) /\
         affine hull (t INTER {x | a dot x = b}) = {x | a dot x = b} /\
         aff_dim (t INTER {x | a dot x = b}) = &2 /\
         relative_interior (t INTER {x | a dot x = b}) =
           interior t INTER {x | a dot x = b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `affine hull (t INTER {x:real^3 | a dot x = b}) = {x | a dot x = b}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE; INTER_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull ({x:real^3 | a dot x = b} INTER interior t)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`{x:real^3 | a dot x = b}`; `interior t:real^3->bool`]
          AFFINE_HULL_CONVEX_INTER_OPEN) THEN
        REWRITE_TAC[CONVEX_HYPERPLANE; OPEN_INTERIOR] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SIMP_TAC[HULL_SUBSET];
        MATCH_MP_TAC HULL_MONO THEN
        MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    ASM_REWRITE_TAC[POLYHEDRON_HYPERPLANE];
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC;
    MATCH_MP_TAC RELATIVE_INTERIOR_CONVEX_INTER_AFFINE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; AFFINE_HYPERPLANE]]);;

(* The part of a polytope in a closed slab, when the polytope meets the open *)
(* slab in interior points, is a polytope with nonempty interior.            *)

let MOI_SSL_SLAB_CELL = prove
 (`!t (a:real^3) t1 t2.
     polytope t /\ ~(a = vec 0) /\
     ~(interior t INTER {x | t1 < a dot x /\ a dot x < t2} = {})
     ==> polytope (t INTER {x | t1 <= a dot x /\ a dot x <= t2}) /\
         ~(interior (t INTER {x | t1 <= a dot x /\ a dot x <= t2}) = {})`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^3 | t1 <= a dot x /\ a dot x <= t2} =
                  {x | a dot x >= t1} INTER {x | a dot x <= t2}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge]; ALL_TAC] THEN
    MATCH_MP_TAC POLYHEDRON_INTER THEN
    REWRITE_TAC[POLYHEDRON_HALFSPACE_GE; POLYHEDRON_HALFSPACE_LE];
    UNDISCH_TAC `interior (t INTER {x:real^3 | t1 <= a dot x /\ a dot x <= t2}) = {}` THEN
    ASM_SIMP_TAC[INTERIOR_INTER; MOI_SSL_INTERIOR_SLAB]]);;

(* A vertex of k lying in a simplex of k is one of its vertices.            *)

let MOI_SSL_VERTEX_IN_HULL = prove
 (`!k t c (v:real^3).
     simplicial_complex k /\ {v} IN k /\ t IN k /\ v IN t /\ t = convex hull c
     ==> v IN c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `{v:real^3}`; `t:real^3->bool`]
    MOI_SSL_SC_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^3} INTER t = {v}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FACE_OF_SING] THEN STRIP_TAC THEN
  MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
  ASM_MESON_TAC[]);;

(* If all points of a finite set other than p lie strictly above the level  *)
(* of p, the hull meets that level only in p.                               *)

let MOI_SSL_HULL_ONE_SIDE = prove
 (`!c (a:real^3) p.
     FINITE c /\ p IN c /\ (!w. w IN c /\ ~(w = p) ==> a dot p < a dot w)
     ==> convex hull c INTER {x | a dot x = a dot p} = {p}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c DELETE (p:real^3) = {}` THENL
   [SUBGOAL_THEN `c = {p:real^3}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c = (p:real^3) INSERT (c DELETE p)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real`
      (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))) MP_TAC) THEN
    SUBGOAL_THEN `(a:real^3) dot p < a dot b` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SSL_HULL_GT THEN EXISTS_TAC `c DELETE (p:real^3)` THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `w = &0` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `w * (a dot b - a dot (p:real^3)) = &0` MP_TAC THENL
       [UNDISCH_TAC `u + w = &1` THEN UNDISCH_TAC
         `u * (a:real^3) dot p + w * a dot b = a dot p` THEN
        CONV_TAC REAL_RING;
        REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `&0`] THEN
    SUBGOAL_THEN `?b:real^3. b IN convex hull (c DELETE p)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[HULL_INC; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    EXISTS_TAC `b:real^3` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC]);;

let MOI_SSL_HULL_ONE_SIDE_LT = prove
 (`!c (a:real^3) p.
     FINITE c /\ p IN c /\ (!w. w IN c /\ ~(w = p) ==> a dot w < a dot p)
     ==> convex hull c INTER {x | a dot x = a dot p} = {p}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `--a:real^3`; `p:real^3`] MOI_SSL_HULL_ONE_SIDE) THEN
  ASM_REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2; REAL_EQ_NEG2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* Classification of the 3-simplices of k in the slab around v: a           *)
(* 3-simplex not containing v and meeting the open slab has all vertices     *)
(* outside the closed slab, some below and some above, and meets every      *)
(* level of the slab in interior points; a 3-simplex containing v either    *)
(* meets the level of v in interior points or only in v.                    *)

let MOI_SSL_PRISM = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN k /\ aff_dim t = &3 /\
     ~(v IN t) /\ ~(t INTER {x | t1 < a dot x /\ a dot x < t2} = {})
     ==> (?c. FINITE c /\ ~affine_dependent c /\ t = convex hull c /\
              (!w. w IN c ==> {w} IN k /\ (a dot w < t1 \/ t2 < a dot w)) /\
              (?w. w IN c /\ a dot w < t1) /\ (?w. w IN c /\ t2 < a dot w)) /\
         (!b. t1 <= b /\ b <= t2 ==> ~(interior t INTER {x | a dot x = b} = {}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`; `k:(real^3->bool)->bool`;
                 `v:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2` THEN
  REWRITE_TAC[moi_ssl_slab_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w:real^3. w IN c ==> a dot w < t1 \/ t2 < a dot w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = v)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~((v:real^3) IN t)` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[HULL_INC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t2:real`)) (concl th) &&
      not (can (find_term ((=) `t1 <= (a:real^3) dot w`)) (concl th)) &&
      can (find_term ((=) `v:real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?w:real^3. w IN c /\ a dot w < t1) /\ (?w. w IN c /\ t2 < a dot w)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `~(t INTER {x:real^3 | t1 < a dot x /\ a dot x < t2} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THENL
     [MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t2:real`; `x:real^3`]
        MOI_SSL_HULL_GT) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `t1 <= (a:real^3) dot w`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(a:real^3) dot w < t1`)) (concl th) &&
        can (find_term ((=) `t2 < (a:real^3) dot w`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`c:real^3->bool`; `a:real^3`; `t1:real`; `x:real^3`]
        MOI_SSL_HULL_LT) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(a:real^3) dot w <= t2`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(a:real^3) dot w < t1`)) (concl th) &&
        can (find_term ((=) `t2 < (a:real^3) dot w`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `c:real^3->bool` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `b:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) && can (find_term ((=) `t1:real`)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) && can (find_term ((=) `t2:real`)) (concl th))) THEN
  MATCH_MP_TAC MOI_SSL_INTERIOR_LEVEL THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN
  ASM_SIMP_TAC[HULL_INC] THEN ASM_REAL_ARITH_TAC);;

let MOI_SSL_STAR = prove
 (`!s (a:real^3) lo hi k v t1 t2 t.
     moi_ssl_slab_hyp s a lo hi k v t1 t2 /\ t IN k /\ aff_dim t = &3 /\ v IN t
     ==> ~(interior t INTER {x | a dot x = a dot v} = {}) \/
         t INTER {x | a dot x = a dot v} = {v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_ssl_slab_hyp s (a:real^3) lo hi k v t1 t2` THEN
  REWRITE_TAC[moi_ssl_slab_hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SIMPLEX_HULL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^3) IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SSL_VERTEX_IN_HULL THEN
    MAP_EVERY EXISTS_TAC [`k:(real^3->bool)->bool`; `t:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN c /\ ~(w = v) ==> ~(a dot w = a dot v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `x:real^3`)) (concl th) &&
      can (find_term ((=) `y:real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(?w:real^3. w IN c /\ a dot w < a dot v) /\
                 (?w:real^3. w IN c /\ a dot v < a dot w)` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`k:(real^3->bool)->bool`; `t:real^3->bool`] MOI_SSL_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SSL_INTERIOR_LEVEL THEN
    MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN
    ASM_SIMP_TAC[HULL_INC];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_EXISTS_THM;
      REAL_NOT_LT]) THENL
     [MATCH_MP_TAC MOI_SSL_HULL_ONE_SIDE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(a:real^3) dot v <= a dot w`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `~((a:real^3) dot w = a dot v)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_SSL_HULL_ONE_SIDE_LT THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `(a:real^3) dot w <= a dot v`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `~((a:real^3) dot w = a dot v)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The free cell in the plane.  The planar structure of a free cell of a     *)
(* cell decomposition of a disk (MOI_SSL_FREE2, in real^2): its attaching    *)
(* arc is the union of the edges shared with other cells, every other edge   *)
(* lies on the boundary of the disk.                                         *)
(* ------------------------------------------------------------------------- *)

(* A proper face of a segment is finite.                                    *)

let MOI_SSL_SEG_FACE_FINITE = prove
 (`!u w f:real^N->bool.
     f face_of segment[u,w] /\ ~(f = segment[u,w]) ==> FINITE f`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `u:real^N = w` THENL
   [UNDISCH_TAC `f face_of segment[u:real^N,w]` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:real^N}` THEN
    REWRITE_TAC[FINITE_SING] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {u:real^N,w}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2]; ALL_TAC] THEN
  UNDISCH_TAC `f face_of segment[u:real^N,w]` THEN
  ASM_SIMP_TAC[SEGMENT_CONVEX_HULL; FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c = {} \/ c = {u:real^N} \/ c = {w} \/ c = {u,w}` MP_TAC THENL
   [UNDISCH_TAC `c SUBSET {u:real^N,w}` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN UNDISCH_TAC `~(f = segment[u:real^N,w])` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING; SEGMENT_CONVEX_HULL;
                  FINITE_EMPTY; FINITE_SING]);;

(* A nondegenerate segment is the closure of itself minus a finite set.     *)

let MOI_SSL_SEG_CLOSURE_DIFF = prove
 (`!u w:real^N k. ~(u = w) /\ FINITE k ==> closure(segment[u,w] DIFF k) = segment[u,w]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`linepath(u:real^N,w)`; `k:real^N->bool`] MOI_SFR_ARC_CLOSURE_DIFF) THEN
  ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH]);;

(* A PL arc is infinite.                                                    *)

let MOI_SSL_PL_BALL1_INFINITE = prove
 (`!s:real^N->bool. pl_ball 1 s ==> INFINITE s`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(k:real^N->bool) homeomorphic (s:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_FINITE_STRONG] THEN
  UNDISCH_TAC `&1 simplex (k:real^N->bool)` THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; FINITE_SEGMENT]);;

let MOI_SSL_PL_BALL_CONNECTED = prove
 (`!n (s:real^N->bool). pl_ball n s ==> connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    can (find_term ((=) `homeomorphism:(real^N->bool)#(real^N->bool)->
                         (real^N->real^N)#(real^N->real^N)->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `IMAGE (f:real^N->real^N) k = s`)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONVEX_CONNECTED THEN
  UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]);;

let MOI_SSL_FREE2 = prove
 (`!g j c:real^2->bool.
     moi_sfr_cplx g /\ pl_cell_with_boundary 2 (UNIONS g) j /\ c IN g /\
     pl_ball 1 (relative_frontier c INTER j) /\
     pl_cell_with_boundary 2 (UNIONS (g DELETE c))
       (closure ((j UNION relative_frontier c) DIFF (relative_frontier c INTER j)))
     ==> ?bb:real^1->real^2.
           arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
           path_image bb SUBSET relative_frontier c /\
           c INTER UNIONS (g DELETE c) = path_image bb /\
           (relative_frontier c INTER j) INTER path_image bb =
             {pathstart bb, pathfinish bb} /\
           (relative_frontier c INTER j) UNION path_image bb = relative_frontier c /\
           (!e. e face_of c /\ aff_dim e = &1
                ==> (e SUBSET path_image bb /\
                     ?d. d IN g /\ ~(d = c) /\ e SUBSET d) \/
                    e SUBSET j) /\
           path_image bb =
             UNIONS {e | e face_of c /\ aff_dim e = &1 /\ e SUBSET path_image bb} /\
           ~(relative_frontier c SUBSET path_image bb)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `j:real^2->bool`; `c:real^2->bool`]
    MOI_SGL_FREE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^1->real^2` (X_CHOOSE_THEN `kj:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `bb:real^1->real^2` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`UNIONS g:real^2->bool`; `j:real^2->bool`] MOI_SFR_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(real^2->bool)->bool`; `c:real^2->bool`] MOI_SFR_CPLX_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (g:(real^2->bool)->bool) /\ (!d. d IN g ==> closed d)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_sfr_cplx (g:(real^2->bool)->bool)` THEN
    REWRITE_TAC[moi_sfr_cplx] THEN MESON_TAC[POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (g DELETE (c:real^2->bool)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  ABBREV_TAC `p = path_image(bb:real^1->real^2)` THEN
  ABBREV_TAC `a1 = relative_frontier c INTER (j:real^2->bool)` THEN
  SUBGOAL_THEN `UNIONS g DIFF j SUBSET interior(UNIONS g:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (UNIONS g) = (j:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2->bool) SUBSET relative_frontier c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c INTER UNIONS (g DELETE c) = p:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p DIFF {pathstart bb,pathfinish bb} SUBSET
                  UNIONS (g DELETE (c:real^2->bool))` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN interior(UNIONS g)` MP_TAC THENL
       [SUBGOAL_THEN `(y:real^2) IN UNIONS g /\ ~(y IN j)` MP_TAC THENL
         [CONJ_TAC THENL
           [SUBGOAL_THEN `(y:real^2) IN c` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
            UNDISCH_TAC `(c:real^2->bool) IN g` THEN SET_TAC[];
            DISCH_TAC THEN
            UNDISCH_TAC `~((y:real^2) IN {pathstart bb,pathfinish bb})` THEN
            REWRITE_TAC[] THEN
            UNDISCH_TAC `(a1:real^2->bool) INTER p = {pathstart bb,pathfinish bb}` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "a1" THEN
            ASM SET_TAC[]];
          UNDISCH_TAC `UNIONS g DIFF j SUBSET interior(UNIONS g:real^2->bool)` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTERIOR] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^2) IN frontier c` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN closure (UNIONS (g DELETE c))` MP_TAC THENL
       [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        UNDISCH_TAC `~((y:real^2) IN interior c)` THEN
        REWRITE_TAC[IN_INTERIOR; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `min e r`) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL; NOT_FORALL_THM; NOT_IMP] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `z:real^2` THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(z:real^2) IN UNIONS g` MP_TAC THENL
           [UNDISCH_TAC `ball(y:real^2,r) SUBSET UNIONS g` THEN
            REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            UNDISCH_TAC `~((z:real^2) IN c)` THEN
            UNDISCH_TAC `c UNION UNIONS (g DELETE c) = UNIONS (g:(real^2->bool)->bool)` THEN
            SET_TAC[]];
          ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
        ASM_SIMP_TAC[CLOSURE_CLOSED]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(p:real^2->bool) SUBSET relative_frontier c` THEN
      UNDISCH_TAC `frontier c SUBSET (c:real^2->bool)` THEN
      REWRITE_TAC[ASSUME `relative_frontier c = frontier (c:real^2->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bb:real^1->real^2`; `{pathstart bb,pathfinish bb}:real^2->bool`]
      MOI_SFR_ARC_CLOSURE_DIFF) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!e. e face_of c /\ aff_dim e = &1
        ==> (e SUBSET p /\ ?d. d IN g /\ ~(d = c) /\ e SUBSET d) \/
            e SUBSET (j:real^2->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^2->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `?d:real^2->bool. d IN g /\ ~(d = c) /\ e SUBSET d` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `d:real^2->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `c INTER UNIONS (g DELETE c) = p:real^2->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `d:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
        `!d:real^2->bool s. d IN s ==> d SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_DELETE];
      DISJ2_TAC] THEN
    SUBGOAL_THEN `polytope (e:real^2->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE]; ALL_TAC] THEN
    MP_TAC(ISPEC `e:real^2->bool` POLYTOPE_AFF_DIM_1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `FINITE (e INTER UNIONS (g DELETE (c:real^2->bool)))` ASSUME_TAC THENL
     [REWRITE_TAC[INTER_UNIONS; FINITE_UNIONS] THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_DELETE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `d:real^2->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_SSL_SEG_FACE_FINITE THEN
      MAP_EVERY EXISTS_TAC [`u:real^2`; `w:real^2`] THEN
      UNDISCH_TAC `e = segment[u:real^2,w]` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(c INTER d:real^2->bool) face_of c` ASSUME_TAC THENL
         [ASM_MESON_TAC[moi_sfr_cplx]; ALL_TAC] THEN
        SUBGOAL_THEN `e INTER d:real^2->bool = (c INTER d) INTER e` SUBST1_TAC THENL
         [MP_TAC(ISPECL [`c:real^2->bool`; `e:real^2->bool`] FACE_OF_IMP_SUBSET) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`(c INTER d) INTER e:real^2->bool`; `c:real^2->bool`;
                       `e:real^2->bool`] FACE_OF_FACE) THEN
        ASM_REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC FACE_OF_INTER THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `~(?d:real^2->bool. d IN g /\ ~(d = c) /\ e SUBSET d)` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `d:real^2->bool` THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2`; `w:real^2`;
                   `e INTER UNIONS (g DELETE (c:real^2->bool))`]
      MOI_SSL_SEG_CLOSURE_DIFF) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `e = segment[u:real^2,w]` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[FRONTIER_CLOSED]] THEN
    SUBGOAL_THEN `(e:real^2->bool) SUBSET relative_frontier c` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^2->bool) = &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(e:real^2->bool) SUBSET relative_frontier c`;
      `c INTER UNIONS (g DELETE c) = p:real^2->bool`;
      `(a1:real^2->bool) UNION p = relative_frontier c`] THEN
    EXPAND_TAC "a1" THEN
    MP_TAC(ISPECL [`c:real^2->bool`; `e:real^2->bool`] FACE_OF_IMP_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier c SUBSET (p:real^2->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `a1:real^2->bool` MOI_SSL_PL_BALL1_INFINITE) THEN
    ANTS_TAC THENL [EXPAND_TAC "a1" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{pathstart bb,pathfinish (bb:real^1->real^2)}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    UNDISCH_TAC `(a1:real^2->bool) INTER p = {pathstart bb,pathfinish bb}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "a1" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `~(relative_frontier c SUBSET (p:real^2->bool))` THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MP_TAC(ISPECL [`bb:real^1->real^2`; `{pathstart bb,pathfinish bb}:real^2->bool`]
    MOI_SFR_ARC_CLOSURE_DIFF) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{e:real^2->bool | e face_of c}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; POLYTOPE_IMP_CLOSED]]] THEN
  SUBGOAL_THEN `relative_frontier c = UNIONS {f:real^2->bool | f facet_of c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_OF_POLYHEDRON THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^2` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN UNIONS {f:real^2->bool | f facet_of c}` MP_TAC THENL
   [UNDISCH_TAC `relative_frontier c = UNIONS {f:real^2->bool | f facet_of c}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(p:real^2->bool) SUBSET relative_frontier c` THEN
    UNDISCH_TAC `(y:real^2) IN p` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN REWRITE_TAC[IN_ELIM_THM; facet_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(e:real^2->bool) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `aff_dim(e:real^2->bool) = aff_dim(c:real^2->bool) - &1`)) THEN
  GEN_REWRITE_TAC I [IN_UNIONS] THEN EXISTS_TAC `e:real^2->bool` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^2->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `e face_of (c:real^2->bool)`)) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((y:real^2) IN {pathstart bb,pathfinish bb})` THEN
  UNDISCH_TAC `(a1:real^2->bool) INTER p = {pathstart bb,pathfinish bb}` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "a1" THEN
  MAP_EVERY UNDISCH_TAC [`(y:real^2) IN e`; `(e:real^2->bool) SUBSET j`;
    `(y:real^2) IN p`; `(p:real^2->bool) SUBSET relative_frontier c`] THEN
  SET_TAC[]);;

(* Injective affine maps preserve polytopes, dimensions, faces, relative    *)
(* frontiers and closures.                                                   *)

let MOI_SSL_AFFINJ_FACTS = prove
 (`!(l:real^M->real^N) q.
     linear l /\ (!u v. l u = l v ==> u = v)
     ==> (!s. polytope (IMAGE (\u. q + l u) s) <=> polytope s) /\
         (!s. aff_dim (IMAGE (\u. q + l u) s) = aff_dim s) /\
         (!s t. IMAGE (\u. q + l u) s face_of IMAGE (\u. q + l u) t <=> s face_of t) /\
         (!s. relative_frontier (IMAGE (\u. q + l u) s) =
              IMAGE (\u. q + l u) (relative_frontier s)) /\
         (!s. closure (IMAGE (\u. q + l u) s) = IMAGE (\u. q + l u) (closure s)) /\
         (!x y. q + l x = q + l y ==> x = y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(MATCH_MP AFF_DIM_INJECTIVE_LINEAR_IMAGE th) THEN
    ASSUME_TAC(MATCH_MP FACE_OF_LINEAR_IMAGE th) THEN
    ASSUME_TAC(MATCH_MP RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE th) THEN
    ASSUME_TAC(MATCH_MP CLOSURE_INJECTIVE_LINEAR_IMAGE th)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  SUBGOAL_THEN `!s. IMAGE (\u. q + (l:real^M->real^N) u) s =
                    IMAGE (\x. q + x) (IMAGE l s)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ; AFF_DIM_TRANSLATION_EQ; FACE_OF_TRANSLATION_EQ;
                  RELATIVE_FRONTIER_TRANSLATION; CLOSURE_TRANSLATION;
                  VECTOR_ARITH `q + x:real^N = q + y <=> x = y`] THEN
  X_GEN_TAC `s:real^M->bool` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `l:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s = IMAGE (l':real^N->real^M) (IMAGE l s)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN ASM_REWRITE_TAC[IMAGE_I]; ALL_TAC] THEN
    MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[POLYTOPE_LINEAR_IMAGE]]);;


let MOI_SSL_IMAGE_EQ_SELF = prove
 (`!(h:A->A) s. (!x. x IN s ==> h x = x) ==> IMAGE h s = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* The free cell theorem and the planar structure of the free cell, for a   *)
(* cell decomposition of a disk lying in a plane of real^3 (transported by  *)
(* the affine frame of the plane).                                          *)

let MOI_SSL_FREE_PLANE = prove
 (`!(a:real^3) b g g0 j.
     ~(a = vec 0) /\ FINITE g /\ 2 <= CARD g /\
     (!c. c IN g ==> polytope c /\ aff_dim c = &2 /\ c SUBSET {x | a dot x = b}) /\
     (!c c'. c IN g /\ c' IN g ==> (c INTER c') face_of c /\ (c INTER c') face_of c') /\
     pl_cell_with_boundary 2 (UNIONS g) j /\
     g0 SUBSET g /\ (g0 = {} \/ ?j0. pl_cell_with_boundary 2 (UNIONS g0) j0) /\
     ~(g0 = g)
     ==> ?c bb:real^1->real^3.
           c IN g /\ ~(c IN g0) /\
           pl_cell_with_boundary 2 (UNIONS (g DELETE c))
             (closure ((j UNION relative_frontier c) DIFF (relative_frontier c INTER j))) /\
           arc bb /\ pl_map_on (interval[vec 0,vec 1]) bb /\
           path_image bb SUBSET relative_frontier c /\
           c INTER UNIONS (g DELETE c) = path_image bb /\
           (relative_frontier c INTER j) INTER path_image bb =
             {pathstart bb, pathfinish bb} /\
           (relative_frontier c INTER j) UNION path_image bb = relative_frontier c /\
           (!e. e face_of c /\ aff_dim e = &1
                ==> (e SUBSET path_image bb /\
                     ?d. d IN g /\ ~(d = c) /\ e SUBSET d) \/
                    e SUBSET j) /\
           path_image bb =
             UNIONS {e | e face_of c /\ aff_dim e = &1 /\ e SUBSET path_image bb} /\
           ~(relative_frontier c SUBSET path_image bb) /\
           connected (relative_frontier c INTER j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real`] MOI_SSL_PLANE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `psi:real^3->real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `q:real^3`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(!s. polytope (IMAGE (f:real^2->real^3) s) <=> polytope s) /\
    (!s. aff_dim (IMAGE (f:real^2->real^3) s) = aff_dim s) /\
    (!s t. IMAGE (f:real^2->real^3) s face_of IMAGE f t <=> s face_of t) /\
    (!s. relative_frontier (IMAGE (f:real^2->real^3) s) = IMAGE f (relative_frontier s)) /\
    (!s. closure (IMAGE (f:real^2->real^3) s) = IMAGE f (closure s)) /\
    (!x y. (f:real^2->real^3) x = f y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^2->real^3) = (\u:real^2. (q:real^3) + (l:real^2->real^3) u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      BETA_TAC THEN MATCH_MP_TAC MOI_SSL_AFFINJ_FACTS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `!u:real^2. (f:real^2->real^3) u = q + l u`)) THEN
  SUBGOAL_THEN `!x:real^3->bool. x SUBSET {x | (a:real^3) dot x = b}
                ==> IMAGE (f:real^2->real^3) (IMAGE (psi:real^3->real^2) x) = x`
  (LABEL_TAC "fpsi") THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM IMAGE_o; o_DEF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) x` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
    MATCH_MP_TAC(SET_RULE
      `!f g:real^3->real^3 s. (!y. y IN s ==> f y = g y) ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!s t. IMAGE (f:real^2->real^3) (s INTER t) = IMAGE f s INTER IMAGE f t) /\
                (!s t. IMAGE (f:real^2->real^3) (s DIFF t) = IMAGE f s DIFF IMAGE f t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_MP_TAC IMAGE_INTER_INJ; MATCH_MP_TAC IMAGE_DIFF_INJ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2->bool. IMAGE (psi:real^3->real^2) (IMAGE (f:real^2->real^3) y) = y`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2->bool. IMAGE (f:real^2->real^3) x = IMAGE f y ==> x = y`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[INJECTIVE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(UNIONS g:real^3->bool) SUBSET {x | (a:real^3) dot x = b}` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET UNIONS g` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SS2_CELL_FACTS]; ALL_TAC] THEN
  ABBREV_TAC `g' = IMAGE (IMAGE (psi:real^3->real^2)) g` THEN
  ABBREV_TAC `g0' = IMAGE (IMAGE (psi:real^3->real^2)) g0` THEN
  ABBREV_TAC `j' = IMAGE (psi:real^3->real^2) j` THEN
  SUBGOAL_THEN `!s:(real^3->bool)->bool. (!x. x IN s ==> x SUBSET {x | (a:real^3) dot x = b})
                ==> IMAGE (IMAGE (f:real^2->real^3)) (IMAGE (IMAGE psi) s) = s`
  (LABEL_TAC "ffpsi") THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM IMAGE_o] THEN
    MATCH_MP_TAC MOI_SSL_IMAGE_EQ_SELF THEN REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `x:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "fpsi" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (IMAGE (f:real^2->real^3)) g' = g /\
                IMAGE (IMAGE (f:real^2->real^3)) g0' = g0 /\
                IMAGE (f:real^2->real^3) j' = j`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "g0'"; "j'"] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ffpsi" MATCH_MP_TAC THEN
      X_GEN_TAC `x:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `polytope (c:real^3->bool)`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      USE_THEN "ffpsi" MATCH_MP_TAC THEN
      X_GEN_TAC `x:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `polytope (c:real^3->bool)`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      USE_THEN "fpsi" MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (g':(real^2->bool)->bool) /\ CARD g' = CARD (g:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (g':(real^2->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "g'" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (IMAGE (f:real^2->real^3)) g' = g` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^2->bool. c IN g' ==> IMAGE (f:real^2->real^3) c IN g`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (IMAGE (f:real^2->real^3)) g' = g` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_sfr_cplx (g':(real^2->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sfr_cplx] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:real^2->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^2->real^3) c` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `polytope (c:real^3->bool)`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`c:real^2->bool`; `d:real^2->bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`IMAGE (f:real^2->real^3) c`; `IMAGE (f:real^2->real^3) d`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `(c:real^3->bool) INTER c'`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM(ASSUME `!s t. IMAGE (f:real^2->real^3) (s INTER t) =
                                     IMAGE f s INTER IMAGE f t`)] THEN
      REWRITE_TAC[ASSUME `!s t. IMAGE (f:real^2->real^3) s face_of IMAGE f t <=>
                                s face_of t`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d e:real^3->bool. pl_cell_with_boundary 2 d e /\ d SUBSET {x | (a:real^3) dot x = b}
                ==> pl_cell_with_boundary 2 (IMAGE (psi:real^3->real^2) d) (IMAGE psi e)`
  (LABEL_TAC "cellpsi") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA_2] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`{x:real^3 | a dot x = b}`; `(:real^2)`; `f:real^2->real^3`] THEN
    ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA];
    ALL_TAC] THEN
  SUBGOAL_THEN `!d e:real^2->bool. pl_cell_with_boundary 2 d e
                ==> pl_cell_with_boundary 2 (IMAGE (f:real^2->real^3) d) (IMAGE f e)`
  (LABEL_TAC "cellf") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `{x:real^3 | a dot x = b}`; `psi:real^3->real^2`] THEN
    ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA_2; SUBSET_UNIV] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS g' = IMAGE (psi:real^3->real^2) (UNIONS g) /\
                UNIONS g0' = IMAGE (psi:real^3->real^2) (UNIONS g0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "g0'"] THEN REWRITE_TAC[IMAGE_UNIONS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g':(real^2->bool)->bool`; `g0':(real^2->bool)->bool`;
                 `j':real^2->bool`] FREE_CELL) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_sfr_cplx (g':(real^2->bool)->bool)` THEN
  REWRITE_TAC[moi_sfr_cplx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "j'" THEN USE_THEN "cellpsi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXPAND_TAC ["g'"; "g0'"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [DISJ1_TAC THEN EXPAND_TAC "g0'" THEN
      UNDISCH_TAC `g0:(real^3->bool)->bool = {}` THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IMAGE_CLAUSES];
      DISJ2_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `j0:real^3->bool` o check (fun th ->
        is_exists(concl th) && can (find_term ((=) `g0:(real^3->bool)->bool`)) (concl th))) THEN
      EXISTS_TAC `IMAGE (psi:real^3->real^2) j0` THEN
      USE_THEN "cellpsi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS g:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN UNDISCH_TAC `~(g0:(real^3->bool)->bool = g)` THEN
    MAP_EVERY UNDISCH_TAC [`IMAGE (IMAGE (f:real^2->real^3)) g' = g`;
                           `IMAGE (IMAGE (f:real^2->real^3)) g0' = g0`] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g':(real^2->bool)->bool`; `j':real^2->bool`; `c':real^2->bool`]
    MOI_SSL_FREE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "j'" THEN USE_THEN "cellpsi" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb':real^1->real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^2->real^3) c'`; `(f:real^2->real^3) o (bb':real^1->real^2)`] THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
  SUBGOAL_THEN `(g:(real^3->bool)->bool) DELETE IMAGE f c' = IMAGE (IMAGE (f:real^2->real^3)) (g' DELETE c')`
  SUBST1_TAC THENL
   [UNDISCH_TAC `IMAGE (IMAGE (f:real^2->real^3)) g' = g` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC IMAGE_DELETE_INJ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3) j' = j` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ASSUME `!s. relative_frontier (IMAGE (f:real^2->real^3) s) =
                          IMAGE f (relative_frontier s)`;
              ASSUME `!s. closure (IMAGE (f:real^2->real^3) s) = IMAGE f (closure s)`;
              GSYM IMAGE_UNIONS; GSYM IMAGE_UNION;
              GSYM(ASSUME `!s t. IMAGE (f:real^2->real^3) (s INTER t) =
                                 IMAGE f s INTER IMAGE f t`);
              GSYM(ASSUME `!s t. IMAGE (f:real^2->real^3) (s DIFF t) =
                                 IMAGE f s DIFF IMAGE f t`)] THEN
  REWRITE_TAC[ASSUME `c' INTER UNIONS (g' DELETE c') = path_image (bb':real^1->real^2)`;
              ASSUME `(relative_frontier c' INTER j') INTER path_image bb' =
                      {pathstart bb', pathfinish (bb':real^1->real^2)}`;
              ASSUME `relative_frontier c' INTER j' UNION path_image bb' =
                      relative_frontier (c':real^2->bool)`;
              IMAGE_CLAUSES] THEN
  SUBGOAL_THEN `homeomorphism ((:real^2),{x:real^3 | a dot x = b}) (f,psi) /\
                pl_map_on (:real^2) (f:real^2->real^3)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ({x:real^3 | a dot x = b},(:real^2)) (psi,f)` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    UNDISCH_TAC `IMAGE (IMAGE (f:real^2->real^3)) g0' = g0` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((c':real^2->bool) IN g0')` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `c':real^2->bool = x` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[];
    USE_THEN "cellf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    UNDISCH_TAC `homeomorphism ((:real^2),{x:real^3 | a dot x = b}) (f,psi)` THEN
    SIMP_TAC[homeomorphism];
    ASM_MESON_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) (IMAGE psi e) = e` ASSUME_TAC THENL
   [USE_THEN "fpsi" MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:real^2->real^3) c'` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e' = IMAGE (psi:real^3->real^2) e` THEN
  SUBGOAL_THEN `(e':real^2->bool) face_of c' /\ aff_dim e' = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `e face_of IMAGE (f:real^2->real^3) c'` THEN
    UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) e' = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e':real^2->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `j':real^2->bool`)) (concl th) &&
    can (find_term ((=) `c':real^2->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3) e' = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    EXISTS_TAC `IMAGE (f:real^2->real^3) d` THEN ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    ASM_MESON_TAC[];
    DISJ2_TAC THEN ASM_SIMP_TAC[IMAGE_SUBSET]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `path_image (bb':real^1->real^2)`)) THEN
  REWRITE_TAC[IMAGE_UNIONS] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `e':real^2->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[IMAGE_SUBSET; FUN_IN_IMAGE];
    DISCH_TAC THEN
    UNDISCH_TAC `~(relative_frontier c' SUBSET path_image (bb':real^1->real^2))` THEN
    REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ISPEC `psi:real^3->real^2` IMAGE_SUBSET)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      UNDISCH_TAC `homeomorphism ((:real^2),{x:real^3 | a dot x = b}) (f,psi)` THEN
      SIMP_TAC[homeomorphism];
      MATCH_MP_TAC MOI_SSL_PL_BALL_CONNECTED THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Convex polygons in real^3 are PL 2-cells; gluing polygons along common    *)
(* edges (the attaching strips of slab prisms).                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_POLYGON3_CELL = prove
 (`!p:real^3->bool.
     polytope p /\ aff_dim p = &2
     ==> pl_cell_with_boundary 2 p (relative_frontier p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3->bool` AFF_DIM_EQ_HYPERPLANE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^3->bool) SUBSET {x | a dot x = b}` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real`] MOI_SSL_PLANE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `psi:real^3->real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `q:real^3`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `(!s. polytope (IMAGE (f:real^2->real^3) s) <=> polytope s) /\
    (!s. aff_dim (IMAGE (f:real^2->real^3) s) = aff_dim s) /\
    (!s. relative_frontier (IMAGE (f:real^2->real^3) s) = IMAGE f (relative_frontier s))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^2->real^3) = (\u:real^2. (q:real^3) + (l:real^2->real^3) u)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
      BETA_TAC THEN MP_TAC(ISPECL [`l:real^2->real^3`; `q:real^3`] MOI_SSL_AFFINJ_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) (IMAGE psi p) = p` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_SSL_IMAGE_EQ_SELF THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
      `!x:real^3. (a:real^3) dot x = b ==> (f:real^2->real^3) ((psi:real^3->real^2) x) = x`)) THEN
    UNDISCH_TAC `(p:real^3->bool) SUBSET {x | a dot x = b}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p' = IMAGE (psi:real^3->real^2) p` THEN
  SUBGOAL_THEN `polytope (p':real^2->bool) /\ aff_dim p' = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^3) p' = p` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `polytope (IMAGE (f:real^2->real^3) p')` THEN
    UNDISCH_TAC `aff_dim (IMAGE (f:real^2->real^3) p') = &2` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p':real^2->bool` MOI_SFR_POLYGON_CELL) THEN
  MP_TAC(ISPEC `p':real^2->bool` MOI_SFR_POLYGON_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 5 (CONJUNCTS th))]) THEN
  STRIP_TAC THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^3) p' = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN
  MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`(:real^2)`; `{x:real^3 | a dot x = b}`; `psi:real^3->real^2`] THEN
  ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA_2; SUBSET_UNIV] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

(* Gluing two PL 2-cells along a common boundary segment.                   *)

let MOI_SSL_GLUE_SEG = prove
 (`!d1 j1 d2 j2 (p:real^3) q.
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     ~(p = q) /\ d1 INTER d2 = segment[p,q] /\
     segment[p,q] SUBSET j1 /\ segment[p,q] SUBSET j2
     ==> pl_cell_with_boundary 2 (d1 UNION d2)
           ((j1 UNION j2) DIFF (segment[p,q] DIFF {p,q}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`;
                 `j2:real^3->bool`; `linepath(p:real^3,q)`] MOI_FSA_GLUE) THEN
  ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[ARC_LINEPATH] THEN
  MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
  REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]);;

(* Chains of two and three convex polygons glued along edges.               *)

let MOI_SSL_STRIP2 = prove
 (`!q1 q2 (p:real^3) q.
     polytope q1 /\ aff_dim q1 = &2 /\ polytope q2 /\ aff_dim q2 = &2 /\
     ~(p = q) /\ q1 INTER q2 = segment[p,q] /\
     segment[p,q] SUBSET relative_frontier q1 /\
     segment[p,q] SUBSET relative_frontier q2
     ==> pl_cell_with_boundary 2 (q1 UNION q2)
           ((relative_frontier q1 UNION relative_frontier q2) DIFF
            (segment[p,q] DIFF {p,q}))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SSL_GLUE_SEG THEN
  ASM_SIMP_TAC[MOI_SSL_POLYGON3_CELL]);;

let MOI_SSL_STRIP3 = prove
 (`!q1 q2 q3 (p:real^3) q p' q'.
     polytope q1 /\ aff_dim q1 = &2 /\ polytope q2 /\ aff_dim q2 = &2 /\
     polytope q3 /\ aff_dim q3 = &2 /\
     ~(p = q) /\ q1 INTER q2 = segment[p,q] /\
     segment[p,q] SUBSET relative_frontier q1 /\
     segment[p,q] SUBSET relative_frontier q2 /\
     ~(p' = q') /\ q2 INTER q3 = segment[p',q'] /\
     segment[p',q'] SUBSET relative_frontier q2 /\
     segment[p',q'] SUBSET relative_frontier q3 /\
     q1 INTER q3 = {} /\ segment[p,q] INTER segment[p',q'] = {}
     ==> pl_cell_with_boundary 2 (q1 UNION q2 UNION q3)
           ((relative_frontier q1 UNION relative_frontier q2 UNION
             relative_frontier q3) DIFF
            ((segment[p,q] DIFF {p,q}) UNION (segment[p',q'] DIFF {p',q'})))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q1:real^3->bool`; `q2:real^3->bool`; `p:real^3`; `q:real^3`]
    MOI_SSL_STRIP2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q1 UNION q2:real^3->bool`;
    `(relative_frontier q1 UNION relative_frontier q2) DIFF
     (segment[p,q] DIFF {p,q}):real^3->bool`;
    `q3:real^3->bool`; `relative_frontier q3:real^3->bool`; `p':real^3`; `q':real^3`]
    MOI_SSL_GLUE_SEG) THEN
  ASM_SIMP_TAC[MOI_SSL_POLYGON3_CELL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`q1 INTER q3:real^3->bool = {}`;
                             `q2 INTER q3:real^3->bool = segment[p',q']`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[p:real^3,q] INTER segment[p',q'] = {}`;
        `segment[p':real^3,q'] SUBSET relative_frontier q2`] THEN
      SET_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[UNION_ASSOC] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `relative_frontier q3 SUBSET (q3:real^3->bool)` MP_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET_EQ; POLYTOPE_IMP_CLOSED] THEN
      REWRITE_TAC[relative_frontier] THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED] THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`segment[p:real^3,q] INTER segment[p',q'] = {}`;
      `q1 INTER q3:real^3->bool = {}`; `q1 INTER q2:real^3->bool = segment[p,q]`] THEN
    SET_TAC[]]);;

(* An edge from below a closed slab to above it meets the slab in a         *)
(* segment between its points on the two boundary levels.                   *)

let MOI_SSL_EDGE_SLAB = prove
 (`!(a:real^3) t1 t2 x y.
     a dot x < t1 /\ t1 < t2 /\ t2 < a dot y
     ==> ?p q. ~(p = q) /\ a dot p = t1 /\ a dot q = t2 /\
               p IN segment[x,y] /\ q IN segment[x,y] /\
               segment[x,y] INTER {z | t1 <= a dot z /\ a dot z <= t2} = segment[p,q]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = (a:real^3) dot y - a dot x` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = (t1 - (a:real^3) dot x) / d` THEN
  ABBREV_TAC `s2 = (t2 - (a:real^3) dot x) / d` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < s2 /\ s2 < &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LID; REAL_SUB_LT;
                 REAL_LT_DIV2_EQ] THEN
    EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. (a:real^3) dot (x + m % (y - x)) = a dot x + m * d` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "d" THEN REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. &0 <= m /\ m <= &1 ==> x + m % (y - x) IN segment[x:real^3,y]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `m:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x + s1 % (y - x):real^3`; `x + s2 % (y - x):real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `x + a % v:real^3 = x + b % v <=> (a - b) % v = vec 0`;
                VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < d` THEN EXPAND_TAC "d" THEN
    REAL_ARITH_TAC;
    EXPAND_TAC "s1" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    EXPAND_TAC "s2" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 = (a:real^3) dot x + s1 * d /\ t2 = a dot x + s2 * d`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    SUBGOAL_THEN `z = x + m % (y - x:real^3)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `(m - s1) / (s2 - s1)` THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % (x + s1 % (y - x)) + u % (x + s2 % (y - x)):real^3 =
      x + ((&1 - u) * s1 + u * s2) % (y - x)`] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&1 - u) * s1 + u * s2 = s1 + u * (s2 - s1)`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % (x + s1 % (y - x)) + u % (x + s2 % (y - x)):real^3 =
      x + ((&1 - u) * s1 + u * s2) % (y - x)`] THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(&1 - u) * s1 + u * s2` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= (&1 - u) /\ b <= u ==> a + b <= &1`) THEN
        CONJ_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `x = x * &1`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        VECTOR_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= u * (s2 - s1) ==> s1 <= (&1 - u) * s1 + u * s2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - u) * (s2 - s1) ==> (&1 - u) * s1 + u * s2 <= s2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

(* A convex set with points on both sides of a level meets it in relative  *)
(* interior points.                                                         *)

let MOI_SSL_RELINT_LEVEL = prove
 (`!t (a:real^3) b x1 x2.
     convex t /\ x1 IN t /\ x2 IN t /\
     a dot x1 < b /\ b < a dot x2
     ==> ~(relative_interior t INTER {x | a dot x = b} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN t ==> !e. &0 < e ==> ?y. y IN relative_interior t /\ dist(y,x) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `t:real^3->bool` CONVEX_CLOSURE_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:real^3->bool. (x:real^3) IN u`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y1:real^3. y1 IN relative_interior t /\ a dot y1 < b` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x1:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(b - a dot x1) / (norm(a:real^3) + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `y - x1:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    UNDISCH_TAC `dist(y:real^3,x1) < (b - a dot x1) / (norm(a:real^3) + &1)` THEN
    REWRITE_TAC[dist] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE] THEN
    REWRITE_TAC[DOT_RSUB] THEN
    MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN MP_TAC(ISPEC `y - x1:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(a:real^3)`,`na:real`) THEN SPEC_TAC(`norm(y - x1:real^3)`,`nd:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `na * nd <= (na + &1) * nd` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?y2:real^3. y2 IN relative_interior t /\ b < a dot y2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x2:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(a dot x2 - b) / (norm(a:real^3) + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `y - x2:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    UNDISCH_TAC `dist(y:real^3,x2) < (a dot x2 - b) / (norm(a:real^3) + &1)` THEN
    REWRITE_TAC[dist] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= n ==> &0 < n + &1`; NORM_POS_LE] THEN
    REWRITE_TAC[DOT_RSUB] THEN
    MP_TAC(ISPEC `a:real^3` NORM_POS_LE) THEN MP_TAC(ISPEC `y - x2:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(a:real^3)`,`na:real`) THEN SPEC_TAC(`norm(y - x2:real^3)`,`nd:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `na * nd <= (na + &1) * nd` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_interior t:real^3->bool`; `y1:real^3`; `y2:real^3`; `a:real^3`; `b:real`]
    CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM]);;


(* Basic facts on a closed slab and its interior.                            *)

let MOI_SSL_SLAB_BASIC = prove
 (`!(a:real^3) t1 t2.
     ~(a = vec 0) /\ t1 < t2
     ==> convex {w | t1 <= a dot w /\ a dot w <= t2} /\
         closed {w | t1 <= a dot w /\ a dot w <= t2} /\
         polyhedron {w | t1 <= a dot w /\ a dot w <= t2} /\
         interior {w | t1 <= a dot w /\ a dot w <= t2} =
           {w | t1 < a dot w /\ a dot w < t2} /\
         open {w | t1 < a dot w /\ a dot w < t2} /\
         relative_interior {w | t1 <= a dot w /\ a dot w <= t2} =
           {w | t1 < a dot w /\ a dot w < t2} /\
         ~({w | t1 < a dot w /\ a dot w < t2} = {}) /\
         {w | t1 <= a dot w /\ a dot w <= t2} DIFF {w | t1 < a dot w /\ a dot w < t2} =
           {w | a dot w = t1} UNION {w | a dot w = t2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{w:real^3 | t1 <= a dot w /\ a dot w <= t2} =
                {w | a dot w >= t1} INTER {w | a dot w <= t2} /\
                {w:real^3 | t1 < a dot w /\ a dot w < t2} =
                {w | a dot w > t1} INTER {w | a dot w < t2}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge; real_gt]; ALL_TAC] THEN
  SIMP_TAC[CONVEX_INTER; CONVEX_HALFSPACE_GE; CONVEX_HALFSPACE_LE; CLOSED_INTER;
           CLOSED_HALFSPACE_GE; CLOSED_HALFSPACE_LE; POLYHEDRON_INTER;
           POLYHEDRON_HALFSPACE_GE; POLYHEDRON_HALFSPACE_LE; OPEN_INTER;
           OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT] THEN
  ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE] THEN
  SUBGOAL_THEN `~({w:real^3 | a dot w > t1} INTER {w | a dot w < t2} = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM; real_gt] THEN
    EXISTS_TAC `((t1 + t2) / &2 / (a dot a)) % a:real^3` THEN
    REWRITE_TAC[DOT_RMUL] THEN
    SUBGOAL_THEN `&0 < (a:real^3) dot a` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `interior({w:real^3 | a dot w >= t1} INTER {w | a dot w <= t2})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
      ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE];
      ASM_SIMP_TAC[INTERIOR_INTER; INTERIOR_HALFSPACE_LE; INTERIOR_HALFSPACE_GE]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_ELIM_THM; real_ge; real_gt] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The part of a triangle crossing a closed slab (one vertex below, two     *)
(* above): a convex polygon whose relative frontier consists of its two     *)
(* level edges and the slab parts of the two crossing edges.                *)

let MOI_SSL_TRAP_FACE = prove
 (`!(a:real^3) t1 t2 x y z.
     ~collinear {x,y,z} /\ a dot x < t1 /\ t1 < t2 /\ t2 < a dot y /\ t2 < a dot z
     ==> polytope (convex hull {x,y,z} INTER {w | t1 <= a dot w /\ a dot w <= t2}) /\
         aff_dim (convex hull {x,y,z} INTER {w | t1 <= a dot w /\ a dot w <= t2}) = &2 /\
         relative_interior
           (convex hull {x,y,z} INTER {w | t1 <= a dot w /\ a dot w <= t2}) =
         relative_interior (convex hull {x,y,z}) INTER
           {w | t1 < a dot w /\ a dot w < t2} /\
         relative_frontier
           (convex hull {x,y,z} INTER {w | t1 <= a dot w /\ a dot w <= t2}) =
         (convex hull {x,y,z} INTER {w | a dot w = t1}) UNION
         (convex hull {x,y,z} INTER {w | a dot w = t2}) UNION
         (segment[x,y] INTER {w | t1 <= a dot w /\ a dot w <= t2}) UNION
         (segment[x,z] INTER {w | t1 <= a dot w /\ a dot w <= t2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DOT_LZERO]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `phi = convex hull {x:real^3,y,z}` THEN
  ABBREV_TAC `sl = {w:real^3 | t1 <= a dot w /\ a dot w <= t2}` THEN
  ABBREV_TAC `osl = {w:real^3 | t1 < a dot w /\ a dot w < t2}` THEN
  SUBGOAL_THEN `polytope (phi:real^3->bool) /\ convex phi /\ closed phi /\ aff_dim phi = &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN
    SIMP_TAC[POLYTOPE_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY; CONVEX_CONVEX_HULL;
             POLYTOPE_IMP_CLOSED; AFF_DIM_CONVEX_HULL] THEN
    MATCH_MP_TAC(INT_ARITH `&1 + &1 <= x:int /\ x <= &2 ==> x = &2`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM INT_LT_DISCRETE; GSYM INT_NOT_LE] THEN
      ASM_REWRITE_TAC[GSYM COLLINEAR_AFF_DIM];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC(INT_ARITH `y <= &2 ==> x:int <= y ==> x <= &2`) THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior phi INTER (osl:real^3->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->bool`; `a:real^3`; `(t1 + t2) / &2`; `x:real^3`;
                   `y:real^3`] MOI_SSL_RELINT_LEVEL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "phi" THEN
      SIMP_TAC[HULL_INC; IN_INSERT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXPAND_TAC "osl" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (phi INTER sl) =
                relative_interior phi INTER (osl:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_INTER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `aff_dim (phi INTER osl:real^3->bool) = &2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
      SUBGOAL_THEN `affine hull (phi INTER osl:real^3->bool) = affine hull phi`
      SUBST1_TAC THENL
       [MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(relative_interior phi INTER (osl:real^3->bool) = {})` THEN
        MP_TAC(ISPEC `phi:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
        ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `aff_dim(phi:real^3->bool) = &2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN SET_TAC[];
      UNDISCH_TAC `aff_dim (phi INTER osl:real^3->bool) = &2` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      UNDISCH_TAC `relative_interior sl = osl:real^3->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPEC `sl:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (phi INTER sl:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSED_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN
  SUBGOAL_THEN `relative_interior phi = phi DIFF
                (segment[x,y] UNION segment[y,z] UNION segment[z,x:real^3])`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `y:real^3`; `z:real^3`] RELATIVE_FRONTIER_OF_TRIANGLE) THEN
    ASM_REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `phi:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[y,z] INTER (sl:real^3->bool) = {}` ASSUME_TAC THENL
   [EXPAND_TAC "sl" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `w:real^3` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{y:real^3,z}`; `a:real^3`; `t2:real`; `w:real^3`] MOI_SSL_HULL_GT) THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^3,y] SUBSET phi /\ segment[x,z] SUBSET phi`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_SYM] THEN
  MAP_EVERY UNDISCH_TAC
   [`segment[y,z] INTER (sl:real^3->bool) = {}`;
    `(sl:real^3->bool) DIFF osl = {w | a dot w = t1} UNION {w | a dot w = t2}`;
    `segment[x:real^3,y] SUBSET phi`; `segment[x:real^3,z] SUBSET phi`] THEN
  REWRITE_TAC[SEGMENT_SYM] THEN
  SUBGOAL_THEN `{w:real^3 | a dot w = t1} SUBSET sl /\ {w:real^3 | a dot w = t2} SUBSET sl`
  MP_TAC THENL
   [EXPAND_TAC "sl" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LE_REFL;
      REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SET_TAC[]);;

(* A hyperplane through a relative interior point of a convex set cuts its  *)
(* affine hull in the affine hull of the section; the section loses one     *)
(* dimension unless the set lies in the hyperplane.                         *)

let MOI_SSL_SECTION_HULL = prove
 (`!p (a:real^3) b.
     convex p /\ ~(relative_interior p INTER {x | a dot x = b} = {})
     ==> affine hull (p INTER {x | a dot x = b}) =
         affine hull p INTER {x | a dot x = b}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL; AFFINE_HYPERPLANE] THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `p:real^3->bool`] HULL_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; IN_RELATIVE_INTERIOR; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC))
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`affine hull p INTER {x:real^3 | a dot x = b}`; `ball(y:real^3,e)`]
    AFFINE_HULL_AFFINE_INTER_OPEN) THEN
  SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL; AFFINE_HYPERPLANE; OPEN_BALL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
    ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL; HULL_INC];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MONO THEN
  UNDISCH_TAC `ball(y:real^3,e) INTER affine hull p SUBSET p` THEN SET_TAC[]);;

let MOI_SSL_SECTION_DIM = prove
 (`!p (a:real^3) b.
     convex p /\ ~(relative_interior p INTER {x | a dot x = b} = {}) /\
     ~(p SUBSET {x | a dot x = b})
     ==> aff_dim (p INTER {x | a dot x = b}) = aff_dim p - &1`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  ASM_SIMP_TAC[MOI_SSL_SECTION_HULL] THEN
  SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_AFFINE_HULL] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `~(relative_interior p INTER {x:real^3 | a dot x = b} = {})` THEN
    MP_TAC(ISPEC `p:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `p:real^3->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `~(p SUBSET {x:real^3 | a dot x = b})` THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `p:real^3->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    REFL_TAC]);;

(* Sections of the faces of a simplex by a level containing no vertex: a    *)
(* face with vertices on both sides is cut through its relative interior,   *)
(* losing two from its vertex count in dimension; the edges of the section  *)
(* are exactly the sections of the crossing 2-faces.                        *)

let MOI_SSL_FACE_SECTION = prove
 (`!c0 w (a:real^3) h x1 x2.
     ~affine_dependent c0 /\ w SUBSET c0 /\ x1 IN w /\ x2 IN w /\
     a dot x1 < h /\ h < a dot x2
     ==> ~(relative_interior (convex hull w) INTER {x | a dot x = h} = {}) /\
         aff_dim (convex hull w INTER {x | a dot x = h}) = &(CARD w) - &2 /\
         (convex hull w INTER {x | a dot x = h}) face_of
           (convex hull c0 INTER {x | a dot x = h})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (w:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (convex hull w) INTER {x:real^3 | a dot x = h} = {})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SSL_RELINT_LEVEL THEN
    MAP_EVERY EXISTS_TAC [`x1:real^3`; `x2:real^3`] THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`convex hull w:real^3->bool`; `a:real^3`; `h:real`]
      MOI_SSL_SECTION_DIM) THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x1:real^3`) THEN ASM_SIMP_TAC[HULL_INC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN INT_ARITH_TAC;
    MATCH_MP_TAC FACE_OF_SLICE THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_SSL_SECTION_EDGE = prove
 (`!c0 e (a:real^3) h.
     ~affine_dependent c0 /\ (!w. w IN c0 ==> ~(a dot w = h)) /\
     e face_of (convex hull c0 INTER {x | a dot x = h}) /\ aff_dim e = &1
     ==> ?w. w SUBSET c0 /\ CARD w = 3 /\
             (?x. x IN w /\ a dot x < h) /\ (?x. x IN w /\ h < a dot x) /\
             e = convex hull w INTER {x | a dot x = h}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull c0:real^3->bool`; `{x:real^3 | a dot x = h}`;
                 `e:real^3->bool`] FACE_OF_INTER_AS_INTER_OF_FACE) THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; CONVEX_HYPERPLANE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `l:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`{x:real^3 | a dot x = h}`; `l:real^3->bool`] FACE_OF_AFFINE_TRIVIAL) THEN
  ASM_REWRITE_TAC[AFFINE_HYPERPLANE] THEN STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
    UNDISCH_TAC `k INTER l:real^3->bool = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_EMPTY; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(k:real^3->bool) face_of convex hull c0` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3->bool` THEN
  SUBGOAL_THEN `e = convex hull w INTER {x:real^3 | a dot x = h}` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (w:real^3->bool) /\ ~affine_dependent w` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `(?x:real^3. x IN w /\ a dot x < h) /\ (?x. x IN w /\ h < a dot x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
     DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
     UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
     SUBGOAL_THEN `e:real^3->bool = {}` (fun th -> REWRITE_TAC[th; AFF_DIM_EMPTY] THEN
       INT_ARITH_TAC) THEN
     ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN convex hull w` THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`w:real^3->bool`; `a:real^3`; `h:real`; `y:real^3`] MOI_SSL_HULL_GT) THEN
     ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
     ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
     SUBGOAL_THEN `~((a:real^3) dot u = h)` MP_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
         is_forall(concl th) && can (find_term ((=) `c0:real^3->bool`)) (concl th) &&
         can (find_term ((=) `h:real`)) (concl th))) THEN
       ASM SET_TAC[];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th ->
       is_forall(concl th) && is_disj(snd(dest_forall(concl th))))) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
     DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
     UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
     SUBGOAL_THEN `e:real^3->bool = {}` (fun th -> REWRITE_TAC[th; AFF_DIM_EMPTY] THEN
       INT_ARITH_TAC) THEN
     ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
     X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN convex hull w` THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`w:real^3->bool`; `a:real^3`; `h:real`; `y:real^3`] MOI_SSL_HULL_LT) THEN
     ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
     ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
     SUBGOAL_THEN `~((a:real^3) dot u = h)` MP_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
         is_forall(concl th) && can (find_term ((=) `c0:real^3->bool`)) (concl th) &&
         can (find_term ((=) `h:real`)) (concl th))) THEN
       ASM SET_TAC[];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th ->
       is_forall(concl th) && is_disj(snd(dest_forall(concl th))))) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `w:real^3->bool`; `a:real^3`; `h:real`]
    MOI_SSL_FACE_SECTION) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `x':real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `aff_dim (convex hull w INTER {x:real^3 | a dot x = h}) =
               &(CARD (w:real^3->bool)) - &2` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `&1:int = x - &2 <=> x = &3`; INT_OF_NUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The attaching set of a deleted prism.  For a tetrahedron conv c0 with all *)
(* vertices outside the slab [t1,t2], the slab parts of a set O of its       *)
(* crossing 2-faces (given by their omitted vertices) form a strip of 1-3    *)
(* polygons; it is a PL 2-cell whose boundary points lie on the slab levels  *)
(* or on the faces not in O, and whose other points lie in the open slab and *)
(* on no face outside O.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The slab part of a polytope meeting both sides of the slab.             *)

let MOI_SSL_TRAP_GEN = prove
 (`!(a:real^3) t1 t2 w x y.
     polytope w /\ x IN w /\ y IN w /\ a dot x < t1 /\ t1 < t2 /\ t2 < a dot y
     ==> polytope (w INTER {z | t1 <= a dot z /\ a dot z <= t2}) /\
         aff_dim (w INTER {z | t1 <= a dot z /\ a dot z <= t2}) = aff_dim w /\
         relative_interior (w INTER {z | t1 <= a dot z /\ a dot z <= t2}) =
           relative_interior w INTER {z | t1 < a dot z /\ a dot z < t2} /\
         relative_frontier (w INTER {z | t1 <= a dot z /\ a dot z <= t2}) SUBSET
           (relative_frontier w INTER {z | t1 <= a dot z /\ a dot z <= t2}) UNION
           (w INTER {z | a dot z = t1}) UNION (w INTER {z | a dot z = t2}) /\
         relative_frontier w INTER {z | t1 <= a dot z /\ a dot z <= t2} SUBSET
           relative_frontier (w INTER {z | t1 <= a dot z /\ a dot z <= t2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DOT_LZERO]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`] MOI_SSL_SLAB_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `sl = {z:real^3 | t1 <= a dot z /\ a dot z <= t2}` THEN
  ABBREV_TAC `osl = {z:real^3 | t1 < a dot z /\ a dot z < t2}` THEN
  SUBGOAL_THEN `convex (w:real^3->bool) /\ closed w` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior w INTER (osl:real^3->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w:real^3->bool`; `a:real^3`; `(t1 + t2) / &2`; `x:real^3`;
                   `y:real^3`] MOI_SSL_RELINT_LEVEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXPAND_TAC "osl" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (w INTER sl) =
                relative_interior w INTER (osl:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_INTER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `aff_dim (w INTER osl:real^3->bool) = aff_dim w` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(relative_interior w INTER (osl:real^3->bool) = {})` THEN
      MP_TAC(ISPEC `w:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN SET_TAC[];
      UNDISCH_TAC `aff_dim (w INTER osl:real^3->bool) = aff_dim w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      UNDISCH_TAC `relative_interior sl = osl:real^3->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPEC `sl:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]];
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; CLOSED_INTER] THEN
    UNDISCH_TAC `(sl:real^3->bool) DIFF osl =
                 {w | a dot w = t1} UNION {w | a dot w = t2}` THEN
    SET_TAC[];
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; CLOSED_INTER] THEN SET_TAC[]]);;

(* A point of the slab in the hull of points outside the slab sees both     *)
(* sides.                                                                   *)

let MOI_SSL_HULL_CROSS = prove
 (`!s (a:real^3) t1 t2 u.
     u IN convex hull s /\ (!z. z IN s ==> a dot z < t1 \/ t2 < a dot z) /\
     t1 <= a dot u /\ a dot u <= t2
     ==> (?p. p IN s /\ a dot p < t1) /\ (?q. q IN s /\ t2 < a dot q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `t2:real`; `u:real^3`]
      MOI_SSL_HULL_GT);
    MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `t1:real`; `u:real^3`]
      MOI_SSL_HULL_LT)] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_NOT_LT; REAL_LE_LT]);;

(* The slab part of a crossing edge, and its open part.                    *)

let MOI_SSL_PAIR_OPEN = prove
 (`!(a:real^3) t1 t2 p q.
     t1 < t2 /\ ((a dot p < t1 /\ t2 < a dot q) \/ (a dot q < t1 /\ t2 < a dot p))
     ==> ?p' q'. ~(p' = q') /\ a dot p' = t1 /\ a dot q' = t2 /\
                 convex hull {p,q} INTER {z | t1 <= a dot z /\ a dot z <= t2} =
                   segment[p',q'] /\
                 convex hull {p,q} INTER {z | t1 < a dot z /\ a dot z < t2} =
                   segment[p',q'] DIFF {p',q'}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?p' q':real^3. ~(p' = q') /\ a dot p' = t1 /\ a dot q' = t2 /\
                   convex hull {p,q} INTER {z | t1 <= a dot z /\ a dot z <= t2} =
                   segment[p',q']`
  (X_CHOOSE_THEN `p':real^3` (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THENL
   [REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `p:real^3`; `q:real^3`]
        MOI_SSL_EDGE_SLAB) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `q:real^3`; `p:real^3`]
        MOI_SSL_EDGE_SLAB) THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SEGMENT_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p':real^3`; `q':real^3`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} INTER {z | t1 < a dot z /\ a dot z < t2} =
                (convex hull {p,q} INTER {z | t1 <= a dot z /\ a dot z <= t2}) INTER
                {z | t1 < a dot z /\ a dot z < t2}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN
  ASM_CASES_TAC `z:real^3 IN segment[p',q']` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `a dot (z:real^3) < t2` THEN
    UNDISCH_TAC `t1 < a dot (z:real^3)` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `z:real^3 IN segment[p',q']` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `~(u = &0) /\ ~(u = &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_SUB_REFL; REAL_SUB_RZERO; VECTOR_MUL_LZERO;
                                VECTOR_MUL_LID; VECTOR_ADD_LID; VECTOR_ADD_RID]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `t1 < (&1 - u) * t1 + u * t2 <=> &0 < u * (t2 - t1)`;
              REAL_ARITH `(&1 - u) * t1 + u * t2 < t2 <=> &0 < (&1 - u) * (t2 - t1)`] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

(* Five distinct points do not fit in a 4-set.                             *)

let MOI_SSL_FIVE = prove
 (`!c0 (p:A) q x y z.
     FINITE c0 /\ CARD c0 = 4 /\ {p,q,x,y,z} SUBSET c0 /\
     ~(p = q) /\ ~(p = x) /\ ~(p = y) /\ ~(p = z) /\ ~(q = x) /\ ~(q = y) /\
     ~(q = z) /\ ~(x = y) /\ ~(x = z) /\ ~(y = z)
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{p:A,q,x,y,z}`; `c0:A->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

(* Boundary and interior points of the strip of slab faces: boundary points *)
(* lie on a slab level or on a face outside O; the other points lie in the  *)
(* open slab and on no face outside O.                                      *)

let MOI_SSL_STRIP_PROPS = prove
 (`!(a:real^3) t1 t2 c0 O.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < t2 /\
     (!z. z IN c0 ==> a dot z < t1 \/ t2 < a dot z) /\ O SUBSET c0 /\
     (!x. x IN O ==> (?p. p IN c0 DELETE x /\ a dot p < t1) /\
                     (?q. q IN c0 DELETE x /\ t2 < a dot q))
     ==> (!u. u IN UNIONS {relative_frontier (convex hull (c0 DELETE x) INTER
                                {z | t1 <= a dot z /\ a dot z <= t2}) | x IN O} /\
              ~(u IN UNIONS {convex hull ((c0 DELETE x) DELETE y) INTER
                              {z | t1 < a dot z /\ a dot z < t2} |
                             x IN O /\ y IN O /\ ~(x = y)})
              ==> a dot u = t1 \/ a dot u = t2 \/
                  ?z. z IN c0 /\ ~(z IN O) /\ u IN convex hull (c0 DELETE z)) /\
         (!u. u IN UNIONS {convex hull (c0 DELETE x) INTER
                           {z | t1 <= a dot z /\ a dot z <= t2} | x IN O} /\
              ~(u IN UNIONS {relative_frontier (convex hull (c0 DELETE x) INTER
                                {z | t1 <= a dot z /\ a dot z <= t2}) | x IN O} DIFF
                     UNIONS {convex hull ((c0 DELETE x) DELETE y) INTER
                              {z | t1 < a dot z /\ a dot z < t2} |
                             x IN O /\ y IN O /\ ~(x = y)})
              ==> t1 < a dot u /\ a dot u < t2 /\
                  !z. z IN c0 /\ ~(z IN O) ==> ~(u IN convex hull (c0 DELETE z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "out")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cross")))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ABBREV_TAC `sl = {z:real^3 | t1 <= a dot z /\ a dot z <= t2}` THEN
  ABBREV_TAC `osl = {z:real^3 | t1 < a dot z /\ a dot z < t2}` THEN
  SUBGOAL_THEN `(!u:real^3. u IN sl <=> t1 <= a dot u /\ a dot u <= t2) /\
                (!u:real^3. u IN osl <=> t1 < a dot u /\ a dot u < t2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sl"; "osl"] THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN O
        ==> closed (convex hull (c0 DELETE x) INTER sl) /\
            relative_interior (convex hull (c0 DELETE x) INTER sl) =
              relative_interior (convex hull (c0 DELETE x)) INTER osl /\
            relative_frontier (convex hull (c0 DELETE x) INTER sl) SUBSET
              (relative_frontier (convex hull (c0 DELETE x)) INTER sl) UNION
              {z | a dot z = t1} UNION {z | a dot z = t2} /\
            relative_frontier (convex hull (c0 DELETE x)) =
              UNIONS {convex hull ((c0 DELETE x) DELETE y) | y | y IN c0 DELETE x}`
  (LABEL_TAC "face") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "cross" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x:real^3 IN O`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `convex hull (c0 DELETE x:real^3)`;
                   `p:real^3`; `q:real^3`] MOI_SSL_TRAP_GEN) THEN
    ASM_SIMP_TAC[POLYTOPE_CONVEX_HULL; FINITE_DELETE; HULL_INC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED];
      FIRST_X_ASSUM(ACCEPT_TAC o MATCH_MP (SET_RULE
        `(s:real^3->bool) SUBSET a UNION (w INTER b) UNION (w INTER c)
         ==> s SUBSET a UNION b UNION c`) o
        check (fun th -> is_binary "SUBSET" (concl th) &&
          can (find_term ((=) `relative_frontier (convex hull (c0 DELETE x:real^3) INTER sl)`))
            (lhand(concl th))));
      MATCH_MP_TAC RELATIVE_FRONTIER_OF_CONVEX_HULL THEN
      MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real^3` THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
      (LABEL_TAC "nrem")) THEN
    USE_THEN "face" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x:real^3 IN O`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `u:real^3`) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_INTER; IN_ELIM_THM] THEN
    ASM_CASES_TAC `a dot (u:real^3) = t1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `a dot (u:real^3) = t2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_DELETE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(y:real^3) IN O` THENL
     [REMOVE_THEN "nrem" (MP_TAC o SPECL [`x:real^3`; `y:real^3`] o
        REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u:real^3) IN convex hull ((c0 DELETE x) DELETE y)` THEN
      SPEC_TAC(`u:real^3`,`u:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN
  REWRITE_TAC[IN_DIFF; DE_MORGAN_THM] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
    (LABEL_TAC "nj")) THEN
  USE_THEN "face" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x:real^3 IN O`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~((u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl))
    ==> ?x' y'. (x' IN O /\ y' IN O /\ ~(x' = y')) /\
                u IN convex hull ((c0 DELETE x') DELETE y') INTER osl`
  (LABEL_TAC "rem") THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^3) IN relative_frontier (convex hull (c0 DELETE x) INTER sl)`
    ASSUME_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[CLOSURE_CLOSED]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "nj" DISJ_CASES_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o REWRITE_RULE[NOT_EXISTS_THM] o
        check (fun th -> is_neg(concl th) && is_exists(rand(concl th)) &&
                         can (find_term ((=) `relative_frontier:(real^3->bool)->real^3->bool`))
                           (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < a dot (u:real^3) /\ a dot u < t2` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl)` THENL
     [UNDISCH_TAC `(u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl)` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      USE_THEN "rem" (fun th -> MP_TAC(MATCH_MP th (ASSUME
        `~((u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl))`))) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x:real^3 = z)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN convex hull ((c0 DELETE x) DELETE z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull (c0 DELETE x) INTER convex hull (c0 DELETE z) =
                  convex hull ((c0 DELETE x) DELETE (z:real^3))`
    (fun th -> REWRITE_TAC[GSYM th] THEN ASM_REWRITE_TAC[IN_INTER] THEN
               UNDISCH_TAC `(u:real^3) IN convex hull (c0 DELETE x) INTER sl` THEN
               SIMP_TAC[IN_INTER]) THEN
    SUBGOAL_THEN `(c0 DELETE x) DELETE (z:real^3) = (c0 DELETE x) INTER (c0 DELETE z)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_HULL_INTER THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(u:real^3) IN relative_frontier (convex hull (c0 DELETE x))` MP_TAC THENL
     [ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "rem" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `~((u:real^3) IN relative_interior (convex hull (c0 DELETE x) INTER sl))`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^3` (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^3) IN convex hull (((c0 DELETE x) DELETE z) INTER
                                          ((c0 DELETE x') DELETE y'))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(c0 DELETE x) DELETE (z:real^3)`; `(c0 DELETE x') DELETE (y':real^3)`]
      CONVEX_HULL_INTER) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "IN" (concl th) &&
        rand(concl th) = `convex hull ((c0 DELETE x') DELETE y') INTER (osl:real^3->bool)`)) THEN
      ASM_SIMP_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`((c0 DELETE x) DELETE z) INTER ((c0 DELETE x') DELETE (y':real^3))`;
                 `a:real^3`; `t1:real`; `t2:real`; `u:real^3`] MOI_SSL_HULL_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_DELETE] THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_DELETE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `p:real^3`; `q:real^3`; `z:real^3`; `x':real^3`;
                 `y':real^3`] MOI_SSL_FIVE) THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> concl th = `O SUBSET (c0:real^3->bool)`)) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

(* Unions over explicit index sets.                                        *)

let MOI_SSL_UNIONS_IDX = prove
 (`(!(f:A->B->bool) x. UNIONS {f u | u IN {x}} = f x) /\
   (!(f:A->B->bool) x y. UNIONS {f u | u IN {x,y}} = f x UNION f y) /\
   (!(f:A->B->bool) x y z. UNIONS {f u | u IN {x,y,z}} = f x UNION f y UNION f z) /\
   (!(g:A->A->B->bool) x.
      UNIONS {g u w | u IN {x} /\ w IN {x} /\ ~(u = w)} = {}) /\
   (!(g:A->A->B->bool) x y.
      UNIONS {g u w | u IN {x,y} /\ w IN {x,y} /\ ~(u = w)} =
      (if x = y then {} else g x y UNION g y x)) /\
   (!(g:A->A->B->bool) x y z.
      ~(x = y) /\ ~(x = z) /\ ~(y = z)
      ==> UNIONS {g u w | u IN {x,y,z} /\ w IN {x,y,z} /\ ~(u = w)} =
          g x y UNION g y x UNION g x z UNION g z x UNION g y z UNION g z y)`,
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_1; UNIONS_2; UNIONS_INSERT] THEN
  REWRITE_TAC[UNION_EMPTY] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
  ASM_MESON_TAC[]);;

(* The slab part of a crossing 2-face of the tetrahedron: a polygon whose   *)
(* relative frontier contains the slab parts of the edges of the face.      *)

let MOI_SSL_FACE_Q = prove
 (`!(a:real^3) t1 t2 c0 x.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < t2 /\ x IN c0 /\
     (?p. p IN c0 DELETE x /\ a dot p < t1) /\ (?q. q IN c0 DELETE x /\ t2 < a dot q)
     ==> polytope (convex hull (c0 DELETE x) INTER {z | t1 <= a dot z /\ a dot z <= t2}) /\
         aff_dim (convex hull (c0 DELETE x) INTER {z | t1 <= a dot z /\ a dot z <= t2}) =
           &2 /\
         (!y. y IN c0 /\ ~(y = x)
              ==> convex hull ((c0 DELETE x) DELETE y) INTER
                  {z | t1 <= a dot z /\ a dot z <= t2} SUBSET
                  relative_frontier (convex hull (c0 DELETE x) INTER
                                     {z | t1 <= a dot z /\ a dot z <= t2}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `convex hull (c0 DELETE x:real^3)`;
                 `p:real^3`; `q:real^3`] MOI_SSL_TRAP_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_CONVEX_HULL; FINITE_DELETE; HULL_INC]; STRIP_TAC] THEN
  SUBGOAL_THEN `~affine_dependent (c0 DELETE x:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c0:real^3->bool` THEN
    ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT; CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `relative_frontier (convex hull (c0 DELETE x:real^3)) INTER
              {z | t1 <= a dot z /\ a dot z <= t2}` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[IN_DELETE]);;

(* Two slab faces of the tetrahedron meet in the slab part of their common *)
(* edge.                                                                    *)

let MOI_SSL_FACE_MEET = prove
 (`!(a:real^3) t1 t2 c0 x y.
     ~affine_dependent c0 /\ x IN c0 /\ y IN c0 /\ ~(x = y)
     ==> (convex hull (c0 DELETE x) INTER {z | t1 <= a dot z /\ a dot z <= t2}) INTER
         (convex hull (c0 DELETE y) INTER {z | t1 <= a dot z /\ a dot z <= t2}) =
         convex hull ((c0 DELETE x) DELETE y) INTER {z | t1 <= a dot z /\ a dot z <= t2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull (c0 DELETE x) INTER convex hull (c0 DELETE y) =
                convex hull ((c0 DELETE x) DELETE (y:real^3))` MP_TAC THENL
   [SUBGOAL_THEN `(c0 DELETE x) DELETE (y:real^3) = (c0 DELETE x) INTER (c0 DELETE y)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_HULL_INTER THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    SET_TAC[]]);;

(* The strip for one, two and three faces.                                 *)

let MOI_SSL_STRIP_C1 = prove
 (`!(a:real^3) t1 t2 c0 x.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < t2 /\ x IN c0 /\
     (?p. p IN c0 DELETE x /\ a dot p < t1) /\ (?q. q IN c0 DELETE x /\ t2 < a dot q)
     ==> pl_cell_with_boundary 2
           (UNIONS {convex hull (c0 DELETE u) INTER {z | t1 <= a dot z /\ a dot z <= t2} |
                    u IN {x}})
           (UNIONS {relative_frontier (convex hull (c0 DELETE u) INTER
                                       {z | t1 <= a dot z /\ a dot z <= t2}) | u IN {x}} DIFF
            UNIONS {convex hull ((c0 DELETE u) DELETE w) INTER
                    {z | t1 < a dot z /\ a dot z < t2} | u IN {x} /\ w IN {x} /\ ~(u = w)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_SSL_UNIONS_IDX; DIFF_EMPTY] THEN
  MATCH_MP_TAC MOI_SSL_POLYGON3_CELL THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `x:real^3`]
    MOI_SSL_FACE_Q) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_SSL_STRIP_C2 = prove
 (`!(a:real^3) t1 t2 c0 x y.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < t2 /\ x IN c0 /\ y IN c0 /\ ~(x = y) /\
     (?p. p IN (c0 DELETE x) DELETE y /\ a dot p < t1) /\
     (?q. q IN (c0 DELETE x) DELETE y /\ t2 < a dot q)
     ==> pl_cell_with_boundary 2
           (UNIONS {convex hull (c0 DELETE u) INTER {z | t1 <= a dot z /\ a dot z <= t2} |
                    u IN {x,y}})
           (UNIONS {relative_frontier (convex hull (c0 DELETE u) INTER
                                       {z | t1 <= a dot z /\ a dot z <= t2}) | u IN {x,y}} DIFF
            UNIONS {convex hull ((c0 DELETE u) DELETE w) INTER
                    {z | t1 < a dot z /\ a dot z < t2} |
                    u IN {x,y} /\ w IN {x,y} /\ ~(u = w)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  ASM_REWRITE_TAC[MOI_SSL_UNIONS_IDX] THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c0 DELETE x) DELETE (y:real^3) = {p,q} /\
                (c0 DELETE y) DELETE (x:real^3) = {p,q}` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
      ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE; INSERT_SUBSET; EMPTY_SUBSET] THEN
      TRY(CONJ_TAC THENL [ASM_MESON_TAC[IN_DELETE]; ALL_TAC]) THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `p:real^3`; `q:real^3`]
    MOI_SSL_PAIR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^3` (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[UNION_IDEMPOT] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `x:real^3`]
    MOI_SSL_FACE_Q) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_DELETE]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `y:real^3`]
    MOI_SSL_FACE_Q) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_DELETE]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_SSL_STRIP2 THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `x:real^3`;
                 `y:real^3`] MOI_SSL_FACE_MEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `convex hull {p:real^3,q} INTER {z | t1 <= a dot z /\ a dot z <= t2} =
               segment[p',q']` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (aconv `relative_frontier (convex hull (c0 DELETE x:real^3) INTER
                           {z | t1 <= a dot z /\ a dot z <= t2})`)) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (aconv `relative_frontier (convex hull (c0 DELETE y:real^3) INTER
                           {z | t1 <= a dot z /\ a dot z <= t2})`)) (concl th)))] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SSL_STRIP_C3 = prove
 (`!(a:real^3) t1 t2 c0 xa xm xb xo.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < t2 /\
     xa IN c0 /\ xm IN c0 /\ xb IN c0 /\ xo IN c0 /\
     ~(xa = xb) /\ ~(xm = xo) /\
     ((a dot xo < t1 /\ a dot xm < t1 /\ t2 < a dot xa /\ t2 < a dot xb) \/
      (t2 < a dot xo /\ t2 < a dot xm /\ a dot xa < t1 /\ a dot xb < t1))
     ==> pl_cell_with_boundary 2
           (UNIONS {convex hull (c0 DELETE u) INTER {z | t1 <= a dot z /\ a dot z <= t2} |
                    u IN {xa,xm,xb}})
           (UNIONS {relative_frontier (convex hull (c0 DELETE u) INTER
                                       {z | t1 <= a dot z /\ a dot z <= t2}) |
                    u IN {xa,xm,xb}} DIFF
            UNIONS {convex hull ((c0 DELETE u) DELETE w) INTER
                    {z | t1 < a dot z /\ a dot z < t2} |
                    u IN {xa,xm,xb} /\ w IN {xa,xm,xb} /\ ~(u = w)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `~(xa:real^3 = xm) /\ ~(xa = xo) /\ ~(xm = xb) /\ ~(xb = xo)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c0 = {xa:real^3,xm,xb,xo}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(c0 DELETE xa) DELETE xm = {xb,xo:real^3} /\ (c0 DELETE xm) DELETE xa = {xb,xo} /\
    (c0 DELETE xa) DELETE xb = {xm,xo} /\ (c0 DELETE xb) DELETE xa = {xm,xo} /\
    (c0 DELETE xm) DELETE xb = {xa,xo} /\ (c0 DELETE xb) DELETE xm = {xa,xo}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c0 = {xa:real^3,xm,xb,xo}` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `c0 = {xa:real^3,xm,xb,xo}`)) THEN
  ASM_SIMP_TAC[MOI_SSL_UNIONS_IDX] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `xb:real^3`; `xo:real^3`]
    MOI_SSL_PAIR_OPEN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_THEN `q1:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `xa:real^3`; `xo:real^3`]
    MOI_SSL_PAIR_OPEN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^3` (X_CHOOSE_THEN `q2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex hull {xm:real^3,xo} INTER {z | t1 <= a dot z /\ a dot z <= t2} = {} /\
                convex hull {xm:real^3,xo} INTER {z | t1 < a dot z /\ a dot z < t2} = {}`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET s /\ c INTER s = {}
                           ==> c INTER s = {} /\ c INTER t = {}`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{xm:real^3,xo}`; `a:real^3`; `t1:real`; `t2:real`; `u:real^3`]
      MOI_SSL_HULL_CROSS) THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; EXISTS_IN_INSERT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `xa:real^3`]
    MOI_SSL_FACE_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `if a dot (xo:real^3) < t1 then xo else xb`;
      EXISTS_TAC `if a dot (xo:real^3) < t1 then xb else xo`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fa")))] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `xm:real^3`]
    MOI_SSL_FACE_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `if a dot (xo:real^3) < t1 then xo else xb`;
      EXISTS_TAC `if a dot (xo:real^3) < t1 then xb else xo`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fm")))] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `xb:real^3`]
    MOI_SSL_FACE_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `if a dot (xo:real^3) < t1 then xo else xa`;
      EXISTS_TAC `if a dot (xo:real^3) < t1 then xa else xo`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fb")))] THEN
  SUBGOAL_THEN
   `segment[p1:real^3,q1] SUBSET relative_frontier (convex hull (c0 DELETE xa) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}) /\
    segment[p1,q1] SUBSET relative_frontier (convex hull (c0 DELETE xm) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}) /\
    segment[p2:real^3,q2] SUBSET relative_frontier (convex hull (c0 DELETE xm) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}) /\
    segment[p2,q2] SUBSET relative_frontier (convex hull (c0 DELETE xb) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `segment[p1:real^3,q1] = convex hull ((c0 DELETE xa) DELETE xm) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "fa" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      SUBGOAL_THEN `segment[p1:real^3,q1] = convex hull ((c0 DELETE xm) DELETE xa) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "fm" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      SUBGOAL_THEN `segment[p2:real^3,q2] = convex hull ((c0 DELETE xm) DELETE xb) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "fm" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      SUBGOAL_THEN `segment[p2:real^3,q2] = convex hull ((c0 DELETE xb) DELETE xm) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[];
        USE_THEN "fb" MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^3,q1] INTER segment[p2,q2] = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull {xb:real^3,xo} INTER convex hull {xa,xo} = {xo}` MP_TAC THENL
     [MP_TAC(ISPECL [`{xb:real^3,xo}`; `{xa:real^3,xo}`] CONVEX_HULL_INTER) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c0:real^3->bool` THEN
        ASM_REWRITE_TAC[UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `{xb:real^3,xo} INTER {xa,xo} = {xo}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        REWRITE_TAC[CONVEX_HULL_SING]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`convex hull {xb:real^3,xo} INTER {z | t1 <= a dot z /\ a dot z <= t2} =
       segment[p1,q1]`;
      `convex hull {xa:real^3,xo} INTER {z | t1 <= a dot z /\ a dot z <= t2} =
       segment[p2,q2]`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SING; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `u:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3`) THEN
    ASM_CASES_TAC `u:real^3 = xo` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC(TAUT `~p ==> ~((a /\ p) /\ b)`) THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`convex hull (c0 DELETE xa) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`;
    `convex hull (c0 DELETE xm) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`;
    `convex hull (c0 DELETE xb) INTER {z:real^3 | t1 <= a dot z /\ a dot z <= t2}`;
    `p1:real^3`; `q1:real^3`; `p2:real^3`; `q2:real^3`] MOI_SSL_STRIP3) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SSL_FACE_MEET]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[UNION_ACI]);;

(* Three crossing faces of a 2+2 tetrahedron: the face omitting the vertex  *)
(* on the side of the fourth vertex is the middle of the strip.             *)

let MOI_SSL_MIDDLE = prove
 (`!(a:real^3) t1 t2 x1 x2 x3 z.
     t1 < t2 /\ (!u. u IN {x1,x2,x3,z} ==> a dot u < t1 \/ t2 < a dot u) /\
     (?p. p IN {x1,x2,x3} /\ a dot p < t1) /\ (?q. q IN {x1,x2,x3} /\ t2 < a dot q) /\
     (?p. p IN {x2,x3,z} /\ a dot p < t1) /\ (?q. q IN {x2,x3,z} /\ t2 < a dot q) /\
     (?p. p IN {x1,x3,z} /\ a dot p < t1) /\ (?q. q IN {x1,x3,z} /\ t2 < a dot q) /\
     (?p. p IN {x1,x2,z} /\ a dot p < t1) /\ (?q. q IN {x1,x2,z} /\ t2 < a dot q)
     ==> ((a dot z < t1 /\ a dot x1 < t1 /\ t2 < a dot x2 /\ t2 < a dot x3) \/
          (t2 < a dot z /\ t2 < a dot x1 /\ a dot x2 < t1 /\ a dot x3 < t1)) \/
         ((a dot z < t1 /\ a dot x2 < t1 /\ t2 < a dot x1 /\ t2 < a dot x3) \/
          (t2 < a dot z /\ t2 < a dot x2 /\ a dot x1 < t1 /\ a dot x3 < t1)) \/
         ((a dot z < t1 /\ a dot x3 < t1 /\ t2 < a dot x1 /\ t2 < a dot x2) \/
          (t2 < a dot z /\ t2 < a dot x3 /\ a dot x1 < t1 /\ a dot x2 < t1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN ASSUME_TAC) MP_TAC)) THEN
  SUBGOAL_THEN
   `(t2 < a dot (x1:real^3) <=> ~(a dot x1 < t1)) /\
    (t2 < a dot (x2:real^3) <=> ~(a dot x2 < t1)) /\
    (t2 < a dot (x3:real^3) <=> ~(a dot x3 < t1)) /\
    (t2 < a dot (z:real^3) <=> ~(a dot z < t1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC TAUT);;

(* The strip of slab faces over a set O of omitted vertices: if O is a      *)
(* nonempty proper subset of the crossing faces whose sections at a level h *)
(* in the slab form a connected set, the slab faces form a PL 2-cell.       *)

let MOI_SSL_STRIP_CELL = prove
 (`!(a:real^3) t1 t2 h c0 O.
     ~affine_dependent c0 /\ CARD c0 = 4 /\ t1 < h /\ h < t2 /\
     (!z. z IN c0 ==> a dot z < t1 \/ t2 < a dot z) /\
     O SUBSET c0 /\ ~(O = {}) /\
     (!x. x IN O ==> (?p. p IN c0 DELETE x /\ a dot p < t1) /\
                     (?q. q IN c0 DELETE x /\ t2 < a dot q)) /\
     (?z. z IN c0 /\ ~(z IN O) /\ (?p. p IN c0 DELETE z /\ a dot p < t1) /\
          (?q. q IN c0 DELETE z /\ t2 < a dot q)) /\
     connected (UNIONS {convex hull (c0 DELETE x) INTER {y | a dot y = h} | x IN O})
     ==> ?je. pl_cell_with_boundary 2
                (UNIONS {convex hull (c0 DELETE x) INTER
                         {z | t1 <= a dot z /\ a dot z <= t2} | x IN O}) je /\
              (!u. u IN je
                   ==> a dot u = t1 \/ a dot u = t2 \/
                       ?z. z IN c0 /\ ~(z IN O) /\ u IN convex hull (c0 DELETE z)) /\
              (!u. u IN UNIONS {convex hull (c0 DELETE x) INTER
                                {z | t1 <= a dot z /\ a dot z <= t2} | x IN O} /\
                   ~(u IN je)
                   ==> t1 < a dot u /\ a dot u < t2 /\
                       !z. z IN c0 /\ ~(z IN O) ==> ~(u IN convex hull (c0 DELETE z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "out") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cross")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z0:real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
                     (LABEL_TAC "conn")))))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_INDEPENDENT_IMP_FINITE) THEN
  SUBGOAL_THEN `t1 < t2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `c0:real^3->bool`; `O:real^3->bool`]
    MOI_SSL_STRIP_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC
   `UNIONS {relative_frontier (convex hull (c0 DELETE x) INTER
                               {z:real^3 | t1 <= a dot z /\ a dot z <= t2}) | x IN O} DIFF
    UNIONS {convex hull ((c0 DELETE x) DELETE y) INTER
            {z:real^3 | t1 < a dot z /\ a dot z < t2} | x IN O /\ y IN O /\ ~(x = y)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THEN X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real^3) IN
      UNIONS {relative_frontier (convex hull (c0 DELETE x) INTER
                                 {z:real^3 | t1 <= a dot z /\ a dot z <= t2}) | x IN O} DIFF
      UNIONS {convex hull ((c0 DELETE x) DELETE y) INTER
              {z:real^3 | t1 < a dot z /\ a dot z < t2} | x IN O /\ y IN O /\ ~(x = y)}` THEN
    REWRITE_TAC[IN_DIFF]] THEN
  SUBGOAL_THEN `FINITE (O:real^3->bool) /\ CARD O < 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `CARD (c0:real^3->bool) = 4` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `O HAS_SIZE 1 \/ O HAS_SIZE 2 \/ (O:real^3->bool) HAS_SIZE 3`
  MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN
    SUBGOAL_THEN `~(CARD (O:real^3->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0]; UNDISCH_TAC `CARD (O:real^3->bool) < 4` THEN ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_TAC `x:real^3`) (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `x1:real^3` (X_CHOOSE_THEN `x2:real^3` (X_CHOOSE_THEN `x3:real^3`
       STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [(* one face *)
    MATCH_MP_TAC MOI_SSL_STRIP_C1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "cross" (MP_TAC o SPEC `x:real^3`) THEN REWRITE_TAC[IN_SING];
    (* two faces *)
    MATCH_MP_TAC MOI_SSL_STRIP_C2 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN c0 /\ y IN c0` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    REMOVE_THEN "conn" MP_TAC THEN REWRITE_TAC[MOI_SSL_UNIONS_IDX] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC
     [`convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = h}`;
      `convex hull (c0 DELETE y) INTER {y:real^3 | a dot y = h}`] THEN
    SUBGOAL_THEN `!w:real^3. w IN c0 ==> closed (convex hull (c0 DELETE w) INTER {y:real^3 | a dot y = h})`
    (fun th -> ASM_SIMP_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN
      SIMP_TAC[CLOSED_HYPERPLANE] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      ASM_SIMP_TAC[FINITE_DELETE];
      ALL_TAC] THEN
    SUBGOAL_THEN `!w:real^3. w IN {x,y}
                  ==> ~(convex hull (c0 DELETE w) INTER {y:real^3 | a dot y = h} = {})`
    (fun th -> REWRITE_TAC[SET_RULE `(s:real^3->bool) SUBSET s UNION t`] THEN
               MP_TAC(SPEC `x:real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THENL
     [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "cross" (fun th -> MP_TAC(MATCH_MP th (ASSUME `w:real^3 IN {x,y}`))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`convex hull (c0 DELETE w:real^3)`; `a:real^3`; `h:real`;
                     `p:real^3`; `q:real^3`] MOI_SSL_RELINT_LEVEL) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPEC `convex hull (c0 DELETE w:real^3)` RELATIVE_INTERIOR_SUBSET) THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT] THEN
    REPEAT(DISCH_THEN(ASSUME_TAC o REWRITE_RULE[])) THEN
    ASM_REWRITE_TAC[SET_RULE `(s:real^3->bool) UNION t SUBSET s UNION t`;
                    SET_RULE `(s:real^3->bool) INTER (s UNION t) = s`;
                    SET_RULE `(t:real^3->bool) INTER (s UNION t) = t`] THEN
    SUBGOAL_THEN
     `(convex hull (c0 DELETE x) INTER {y:real^3 | a dot y = h}) INTER (convex hull (c0 DELETE y) INTER {y:real^3 | a dot y = h}) =
      convex hull ((c0 DELETE x) DELETE y) INTER {y:real^3 | a dot y = h}`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `convex hull (c0 DELETE x) INTER convex hull (c0 DELETE y) =
                    convex hull ((c0 DELETE x) DELETE (y:real^3))` MP_TAC THENL
       [SUBGOAL_THEN `(c0 DELETE x) DELETE (y:real^3) = (c0 DELETE x) INTER (c0 DELETE y)`
        SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CONVEX_HULL_INTER THEN
        MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
        EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM; INTER_EMPTY] THEN
    X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(c0 DELETE x) DELETE (y:real^3)`; `a:real^3`; `t1:real`; `t2:real`;
                   `u:real^3`] MOI_SSL_HULL_CROSS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    (* three faces *)
    SUBGOAL_THEN `(x1:real^3) IN c0 /\ x2 IN c0 /\ x3 IN c0 /\
                  ~(x1 = z0) /\ ~(x2 = z0) /\ ~(x3 = z0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((z0:real^3) IN {x1,x2,x3})` THEN
      UNDISCH_TAC `{x1:real^3,x2,x3} SUBSET c0` THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^3`; `t1:real`; `t2:real`; `x1:real^3`; `x2:real^3`;
                   `x3:real^3`; `z0:real^3`] MOI_SSL_MIDDLE) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `c0 DELETE (z0:real^3) = {x1,x2,x3} /\ c0 DELETE x1 = {x2,x3,z0} /\
                    c0 DELETE x2 = {x1,x3,z0} /\ c0 DELETE x3 = {x1,x2,z0}`
      (fun th -> REWRITE_TAC[GSYM th]) THENL
       [SUBGOAL_THEN `c0 = {x1:real^3,x2,x3,z0}` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
          ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[EXTENSION; IN_DELETE; IN_INSERT; NOT_IN_EMPTY] THEN
        REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MAP_EVERY (fun t -> USE_THEN "cross" (fun th -> REWRITE_TAC[MATCH_MP th
        (EQT_ELIM(REWRITE_CONV[IN_INSERT] t))])) [`(x1:real^3) IN {x1,x2,x3}`;
        `(x2:real^3) IN {x1,x2,x3}`; `(x3:real^3) IN {x1,x2,x3}`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_INSERT; IN_DELETE] THEN X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
      USE_THEN "out" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `{x1:real^3,x2,x3} = {x2,x1,x3}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `{x1:real^3,x2,x3} = {x2,x1,x3}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `{x1:real^3,x2,x3} = {x1,x3,x2}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `{x1:real^3,x2,x3} = {x1,x3,x2}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SSL_STRIP_C3 THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The final gluing (Moise p.125): the spheres below the levels between      *)
(* vertex levels are glued slab by slab by Theorem 11 (THM11).               *)
(* ------------------------------------------------------------------------- *)

let MOI_SSL_GLUE_STEP = prove
 (`!s (a:real^3) lo hi t1 t2.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\ lo < t1 /\ t1 < hi /\ t1 < t2 /\
     moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = t1}) UNION
                      (s INTER {x | a dot x <= t1})) /\
     moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = t1}) UNION
                      ((s UNION inside s) INTER {x | a dot x = t2}) UNION
                      (s INTER {x | t1 <= a dot x /\ a dot x <= t2}))
     ==> moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = t2}) UNION
                          (s INTER {x | a dot x <= t2}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`]
    MOI_SSL_FIB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(SPEC `t1:real` (last(CONJUNCTS th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `{x:real^3 | a dot x = t2} INTER {x | a dot x <= t1} = {} /\
    {x:real^3 | a dot x <= t1} INTER {x | t1 <= a dot x /\ a dot x <= t2} =
      {x | a dot x = t1} /\
    {x:real^3 | a dot x <= t2} =
      {x | a dot x <= t1} UNION {x | t1 <= a dot x /\ a dot x <= t2} /\
    {x:real^3 | a dot x = t1} INTER {x | a dot x = t2} = {} /\
    {x:real^3 | a dot x = t1} SUBSET {x | t1 <= a dot x /\ a dot x <= t2} /\
    {x:real^3 | a dot x = t2} SUBSET {x | t1 <= a dot x /\ a dot x <= t2} /\
    {x:real^3 | a dot x = t1} SUBSET {x | a dot x <= t1} /\
    {x:real^3 | a dot x = t2} SUBSET {x | a dot x <= t2}`
  MP_TAC THENL
   [REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e1 = {x:real^3 | a dot x = t1}` THEN
  ABBREV_TAC `e2 = {x:real^3 | a dot x = t2}` THEN
  ABBREV_TAC `l1 = {x:real^3 | a dot x <= t1}` THEN
  ABBREV_TAC `l2 = {x:real^3 | a dot x <= t2}` THEN
  ABBREV_TAC `b = {x:real^3 | t1 <= a dot x /\ a dot x <= t2}` THEN
  ABBREV_TAC `m = (s:real^3->bool) UNION inside s` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(m INTER e1) UNION (s INTER l1):real^3->bool`;
    `(m INTER e1) UNION (m INTER e2) UNION (s INTER b):real^3->bool`;
    `m INTER e1:real^3->bool`; `s INTER e1:real^3->bool`] THM11) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[moi_sch3_plane_cell] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^3`; `t1:real`] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "e1" THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(s:real^3->bool) SUBSET m`;
        `e2 INTER l1:real^3->bool = {}`; `l1 INTER b:real^3->bool = e1`] THEN
      SET_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(s:real^3->bool) SUBSET m`; `e2 INTER l1:real^3->bool = {}`;
      `l1 INTER b:real^3->bool = e1`; `l2:real^3->bool = l1 UNION b`;
      `e1 INTER e2:real^3->bool = {}`; `e1 SUBSET (b:real^3->bool)`;
      `e2 SUBSET (b:real^3->bool)`; `e1 SUBSET (l1:real^3->bool)`;
      `e2 SUBSET (l2:real^3->bool)`] THEN
    SET_TAC[]]);;

let MOI_SSL_MAX_POINT = prove
 (`!(a:real^3) b. FINITE b /\ ~(b = {})
                  ==> ?v. v IN b /\ !w. w IN b ==> a dot w <= a dot v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\w:real^3. a dot w) b` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3` THEN ASM_MESON_TAC[]);;

let MOI_SSL_VERTEX_FACTS = prove
 (`!s (a:real^3) lo hi k.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w)
     ==> FINITE {w:real^3 | {w} IN k} /\
         (!w. {w} IN k ==> w IN s UNION inside s /\ lo <= a dot w /\ a dot w <= hi) /\
         (?p. {p} IN k /\ a dot p = lo) /\ (?q. {q} IN k /\ a dot q = hi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`]
    MOI_SSL_FIB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k ==> w IN s UNION inside s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS k = (s:real^3->bool) UNION inside s`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SCD_VERTICES_FINITE THEN ASM_MESON_TAC[simplicial_complex];
    ASM_MESON_TAC[];
    EXISTS_TAC `p:real^3` THEN
    SUBGOAL_THEN `(p:real^3) IN s UNION inside s /\ a dot p = lo` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `(s UNION inside s) INTER {x:real^3 | a dot x = lo} = {p}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SSL_EXTREME_VERTEX THEN
    EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `q:real^3` THEN
    SUBGOAL_THEN `(q:real^3) IN s UNION inside s /\ a dot q = hi` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `(s UNION inside s) INTER {x:real^3 | a dot x = hi} = {q}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SSL_EXTREME_VERTEX THEN
    EXISTS_TAC `--a:real^3` THEN ASM_REWRITE_TAC[DOT_LNEG; REAL_LE_NEG2] THEN
    REWRITE_TAC[REAL_ARITH `--x = --y <=> x = y`] THEN ASM_MESON_TAC[]]);;

(* The spheres below the non-vertex levels are simply imbedded: induction *)
(* on the number of vertices below the level (DG SublevelEmbedding).       *)

let MOI_SSL_SUBLEVEL = prove
 (mk_imp(MOI_SSL_SLAB_STMT,
  `!s (a:real^3) lo hi k.
     pl_sphere 2 s /\ moi_sch3_fibred s a lo hi /\
     simplicial_complex k /\ UNIONS k = s UNION inside s /\
     (!v w. {v} IN k /\ {w} IN k /\ a dot v = a dot w ==> v = w)
     ==> !n c. lo < c /\ c < hi /\ (!w. {w} IN k ==> ~(a dot w = c)) /\
               CARD {w:real^3 | {w} IN k /\ a dot w < c} = n
               ==> moi_sch3_simple (((s UNION inside s) INTER {x | a dot x = c}) UNION
                                    (s INTER {x | a dot x <= c}))`),
  DISCH_THEN(fun slab ->
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`] MOI_SSL_VERTEX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) (K ALL_TAC)))) THEN
  SUBGOAL_THEN `!c. FINITE {w:real^3 | {w} IN k /\ a dot w < c}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{w:real^3 | {w} IN k}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THEN X_GEN_TAC `c:real` THEN STRIP_TAC THENL
  [MATCH_MP_TAC(TAUT `F ==> p`) THEN
  UNDISCH_TAC `CARD {w:real^3 | {w} IN k /\ a dot w < c} = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[];
   ABBREV_TAC `bb = {w:real^3 | {w} IN k /\ a dot w < c}` THEN
  SUBGOAL_THEN `FINITE (bb:real^3->bool) /\ (p:real^3) IN bb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k /\ a dot w <= c ==> w IN bb` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "bb" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [SUBGOAL_THEN `bb = {p:real^3}` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:real^3`; `bb:real^3->bool`] CARD_DELETE) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FINITE_DELETE; CARD_EQ_0; ARITH] THEN
      UNDISCH_TAC `(p:real^3) IN bb` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_SSL_CONE_BOTTOM THEN
    MAP_EVERY EXISTS_TAC [`lo:real`; `hi:real`; `k:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN bb` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[IN_SING]] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `bb:real^3->bool`] MOI_SSL_MAX_POINT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^3`; `bb DELETE (v:real^3)`] MOI_SSL_MAX_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE] THEN
    DISCH_THEN(MP_TAC o AP_TERM `CARD:(real^3->bool)->num`) THEN
    ASM_SIMP_TAC[CARD_DELETE; CARD_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^3} IN k /\ a dot v < c /\ {v':real^3} IN k /\ a dot v' < c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^3) IN bb` THEN UNDISCH_TAC `(v':real^3) IN bb` THEN
    EXPAND_TAC "bb" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot v' < a dot v` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(v':real^3 = v)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!v w:real^3. {v} IN k /\ {w} IN k /\ a dot v = a dot w
                                       ==> v = w`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c' = ((a:real^3) dot v' + a dot v) / &2` THEN
  SUBGOAL_THEN `(a:real^3) dot v' < c' /\ c' < a dot v` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k /\ ~(w = v) /\ a dot w <= c ==> a dot w < c'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot w <= a dot v'` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!w:real^3. w IN bb /\ ~(w = v) ==> a dot w <= a dot v'`)
          (concl th))) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SSL_GLUE_STEP THEN
  MAP_EVERY EXISTS_TAC [`lo:real`; `hi:real`; `c':real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lo < c'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(a:real^3) dot v'` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CARD:(real^3->bool)->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `w:real^3 = v` THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^3) dot w < c'` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `{w:real^3 | {w} IN k /\ a dot w < c'} = bb DELETE v` SUBST1_TAC THENL
     [EXPAND_TAC "bb" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[CARD_DELETE] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC slab THEN
    MAP_EVERY EXISTS_TAC [`lo:real`; `hi:real`; `k:(real^3->bool)->bool`; `v:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot w < c'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]]));;

(* Moise 17.12 for fibred spheres (Lemmas 4-6 and the final gluing,         *)
(* pp.124-125), given the slab statement MOI_SSL_SLAB_STMT stated at the    *)
(* top of this file: the sphere below a level just under the top vertex,    *)
(* glued to the top cone along the level 2-cell by Theorem 11.              *)

let MOI_SSL_FIBRED_FROM_SLAB = prove
 (mk_imp(MOI_SSL_SLAB_STMT, MOI_SCH3_FIBRED_SIMPLE),
  DISCH_THEN(fun slab ->
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                       `k:(real^3->bool)->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`]
    MOI_SSL_FIB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "cells" (last(CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`] MOI_SSL_VERTEX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `p0:real^3` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `q0:real^3` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(p0:real^3 = q0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `{w:real^3 | {w} IN k} DELETE q0`] MOI_SSL_MAX_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE; GSYM MEMBER_NOT_EMPTY; IN_DELETE; IN_ELIM_THM] THEN
    EXISTS_TAC `p0:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k /\ ~(w = q0) ==> a dot w < hi` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w:real^3 = q0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!v w:real^3. {v} IN k /\ {w} IN k /\ a dot v = a dot w
                                       ==> v = w`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = ((a:real^3) dot u + hi) / &2` THEN
  SUBGOAL_THEN `(a:real^3) dot u < c /\ c < hi /\ lo < c` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^3) dot u < hi /\ lo <= a dot u` MP_TAC THENL
     [ASM_MESON_TAC[]; EXPAND_TAC "c" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN k /\ c <= a dot w ==> w = q0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot w <= a dot u` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`] (MP MOI_SSL_SUBLEVEL slab)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`CARD {w:real^3 | {w} IN k /\ a dot w < c}`; `c:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `w:real^3 = q0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(a:real^3) dot w <= a dot u` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `lo:real`; `hi:real`;
                 `k:(real^3->bool)->bool`; `c:real`] MOI_SSL_CONE_TOP) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `w:real^3 = q0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  USE_THEN "cells" (MP_TAC o SPEC `c:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`((s UNION inside s) INTER {x:real^3 | a dot x = c}) UNION
     (s INTER {x | a dot x <= c})`;
    `((s UNION inside s) INTER {x:real^3 | a dot x = c}) UNION
     (s INTER {x | c <= a dot x})`;
    `(s UNION inside s) INTER {x:real^3 | a dot x = c}`;
    `s INTER {x:real^3 | a dot x = c}`] THM11) THEN
  SUBGOAL_THEN
   `{x:real^3 | a dot x <= c} INTER {x | c <= a dot x} = {x | a dot x = c} /\
    {x:real^3 | a dot x <= c} UNION {x | c <= a dot x} = (:real^3)`
  MP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = {x:real^3 | a dot x = c}` THEN
  ABBREV_TAC `l = {x:real^3 | a dot x <= c}` THEN
  ABBREV_TAC `g = {x:real^3 | c <= a dot x}` THEN
  STRIP_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[moi_sch3_plane_cell] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^3`; `c:real`] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "e" THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`(l:real^3->bool) INTER g = e`] THEN SET_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(l:real^3->bool) INTER g = e`;
                           `(l:real^3->bool) UNION g = (:real^3)`] THEN
    SET_TAC[]]));;

