(* ========================================================================= *)
(* pc_moi_lt_sphere: the sphere case of the loop theorem (Moise GTM 47,      *)
(* p.183 Lemma 1).  Main theorems (statements of pc_moi_loop_stmt.ml):       *)
(*   SPHERE_HOLE  = MOI_LT_SPHERE_HOLE: a loop in the interior of UNIONS cb *)
(*     in a 2-sphere boundary component b, essential under g, gives a PL    *)
(*     disk in b with boundary in UNIONS cb whose boundary loop is          *)
(*     essential under g;                                                    *)
(*   PUSH_IN_DISK = MOI_LT_PUSH_IN_DISK: a PL disk in Bd c is pushed into a *)
(*     PL disk of |c| meeting Bd c exactly in its (unchanged) boundary.     *)
(* Route: PUSH_IN_DISK along the collar with the tent function of            *)
(* std_triangle; SPHERE_HOLE in a planar chart of b minus a 2-simplex, by    *)
(* grid-walk approximation of the loop, splitting of walks into simple grid  *)
(* polygons and the planar Schoenflies theorem.                              *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_fnd1.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_fnd_tubecm.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* PUSH_IN_DISK: push a disk of Bd c into |c| along the collar, by the tent  *)
(* function of std_triangle (zero exactly on its boundary).                  *)
(* ------------------------------------------------------------------------- *)

let moi_lsp_tent = new_definition
 `moi_lsp_tent (x:real^2) = &3 * min (min (x$1) (x$2)) (&1 - x$1 - x$2)`;;

let MOI_LSP_STD_TRIANGLE_EXPLICIT = prove
 (`std_triangle = {x:real^2 | &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1}`,
  REWRITE_TAC[std_triangle; CONVEX_HULL_3] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
      STRIP_ASSUME_TAC))) THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                 BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1 - (x:real^2)$1 - x$2`; `(x:real^2)$1`; `(x:real^2)$2`] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

let MOI_LSP_STD_FRONTIER_EXPLICIT = prove
 (`relative_frontier std_triangle =
   {x:real^2 | &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1 /\
               (x$1 = &0 \/ x$2 = &0 \/ x$1 + x$2 = &1)}`,
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_UNION; IN_SEGMENT; IN_ELIM_THM] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_LID; REAL_ADD_RID] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THENL
     [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `&1 - (x:real^2)$2` THEN ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN EXISTS_TAC `(x:real^2)$1` THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `(x:real^2)$2` THEN ASM_REAL_ARITH_TAC]]);;

let MOI_LSP_PL_AFFINE_FN = prove
 (`!(s:real^2->bool) a b c.
     locally_polyhedral s ==> pl_map_on s (\x. lift(a * x$1 + b * x$2 + c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^2. lift(a * x$1 + b * x$2 + c)) =
                (\x. (\x. lift(a * x$1 + b * x$2)) x + lift c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; REAL_ADD_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; GSYM LIFT_ADD; GSYM LIFT_CMUL; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; LIFT_EQ] THEN
  REAL_ARITH_TAC);;

let MOI_LSP_TENT_PL = prove
 (`pl_map_on std_triangle (\x. lift(moi_lsp_tent x))`,
  REWRITE_TAC[moi_lsp_tent; LIFT_CMUL] THEN MATCH_MP_TAC PL_MAP_ON_CMUL THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN CONJ_TAC; ALL_TAC] THENL
   [MP_TAC(SPECL [`std_triangle`; `&1`; `&0`; `&0`] MOI_LSP_PL_AFFINE_FN);
    MP_TAC(SPECL [`std_triangle`; `&0`; `&1`; `&0`] MOI_LSP_PL_AFFINE_FN);
    MP_TAC(SPECL [`std_triangle`; `-- &1`; `-- &1`; `&1`] MOI_LSP_PL_AFFINE_FN)] THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:real^2` THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_LSP_TENT_FACTS = prove
 (`!x:real^2. x IN std_triangle
             ==> &0 <= moi_lsp_tent x /\ moi_lsp_tent x <= &1 /\
                 (moi_lsp_tent x = &0 <=> x IN relative_frontier std_triangle)`,
  GEN_TAC THEN
  REWRITE_TAC[MOI_LSP_STD_TRIANGLE_EXPLICIT; MOI_LSP_STD_FRONTIER_EXPLICIT;
              IN_ELIM_THM; moi_lsp_tent] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_min] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let PUSH_IN_DISK = prove
 (MOI_LT_PUSH_IN_DISK,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `e0:real^2->real^N`;
                       `e0':real^N->real^2`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `UNIONS c:real^N->bool`] BOUNDARY_COLLAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV;
                    MOI_LTD_COMPLEX_BOUNDARY_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `q:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  (* facts on q and e0 *)
  SUBGOAL_THEN
   `(!z. z IN complex_boundary (c:(real^N->bool)->bool) PCROSS interval[vec 0:real^1,vec 1]
         ==> (q':real^N->real^(N,1)finite_sum) (q z) = z) /\
    IMAGE (q:real^(N,1)finite_sum->real^N)
          (complex_boundary c PCROSS interval[vec 0:real^1,vec 1]) = w /\
    pl_map_on (complex_boundary c PCROSS interval[vec 0:real^1,vec 1]) q`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `q:real^(N,1)finite_sum->real^N`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "pl_homeomorphism")) (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN std_triangle ==> (e0':real^N->real^2) (e0 x) = x) /\
    pl_map_on std_triangle (e0:real^2->real^N)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `e0:real^2->real^N`)) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "pl_homeomorphism")) (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = \x:real^2. (q:real^(N,1)finite_sum->real^N)
                               (pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)))` THEN
  SUBGOAL_THEN
   `!x:real^2. x IN std_triangle
               ==> pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)) IN
                   complex_boundary (c:(real^N->bool)->bool) PCROSS
                   interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[MOI_LSP_TENT_FACTS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on std_triangle (e:real^2->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN
     `(\x:real^2. (q:real^(N,1)finite_sum->real^N)
                    (pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)))) =
      q o (\x. pastecart (e0 x) (lift(moi_lsp_tent x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool) PCROSS
                interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_PASTECART THEN ASM_REWRITE_TAC[MOI_LSP_TENT_PL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN std_triangle /\ y IN std_triangle /\
                      (e:real^2->real^N) x = e y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)) =
                  pastecart (e0 y) (lift(moi_lsp_tent y))` MP_TAC THENL
     [UNDISCH_TAC `(e:real^2->real^N) x = e y` THEN EXPAND_TAC "e" THEN BETA_TAC THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `(q':real^N->real^(N,1)finite_sum)
          (q (pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)))) =
        pastecart (e0 x) (lift(moi_lsp_tent x)) /\
        q' (q (pastecart (e0 y) (lift(moi_lsp_tent y)))) =
        pastecart (e0 y) (lift(moi_lsp_tent y))`
      (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
       [CONJ_TAC THEN
        FIRST_ASSUM(fun th -> if is_forall(concl th) &&
          can (find_term ((=) `q':real^N->real^(N,1)finite_sum`)) (concl th)
          then MATCH_MP_TAC th else failwith "no") THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[PASTECART_INJ] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `e0':real^N->real^2`)) (concl th)
        then MP_TAC(CONJ (MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN std_triangle`))
                         (MP (SPEC `y:real^2` th) (ASSUME `(y:real^2) IN std_triangle`)))
        else failwith "no") THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `e:real^2->real^N`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':real^N->real^2` ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN relative_frontier std_triangle ==> (e:real^2->real^N) x = e0 x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_lsp_tent x = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LSP_TENT_FACTS]; ALL_TAC] THEN
    EXPAND_TAC "e" THEN ASM_REWRITE_TAC[LIFT_NUM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (e:real^2->real^N) std_triangle`; `e:real^2->real^N`;
                        `e':real^N->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^2->real^N) x IN w` MP_TAC THENL
     [EXPAND_TAC "e" THEN BETA_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `w:real^N->bool`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_lsp_tent x = &0` (fun th -> ASM_MESON_TAC[th; MOI_LSP_TENT_FACTS]) THEN
    SUBGOAL_THEN `pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)) =
                  pastecart y (vec 0)` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[PASTECART_INJ; GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN
      SIMP_TAC[]] THEN
    SUBGOAL_THEN `(q:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)) = y` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^(N,1)finite_sum->real^N)
                    (pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x))) =
                  q (pastecart y (vec 0))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if concl th =
        `(q:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)) = y`
        then REWRITE_TAC[th] else NO_TAC) THEN
      UNDISCH_TAC `(y:real^N) = (e:real^2->real^N) x` THEN EXPAND_TAC "e" THEN BETA_TAC THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(q':real^N->real^(N,1)finite_sum)
        (q (pastecart ((e0:real^2->real^N) x) (lift(moi_lsp_tent x)))) =
      pastecart (e0 x) (lift(moi_lsp_tent x)) /\
      q' (q (pastecart (y:real^N) (vec 0))) = pastecart y (vec 0)`
    (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
     [CONJ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term ((=) `q':real^N->real^(N,1)finite_sum`)) (concl th)
        then MATCH_MP_TAC th else failwith "no") THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_INTER; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET];
      SUBGOAL_THEN `(e:real^2->real^N) x = e0 x` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (e0:real^2->real^N) std_triangle SUBSET complex_boundary c` THEN
      MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Walks: lists of points whose consecutive members are related by r, and   *)
(* homotopy facts for their polygonal paths (HOL's polygonal_path of        *)
(* 100/pick.ml).  General: any relation, any dimension.                      *)
(* ------------------------------------------------------------------------- *)

let moi_lsp_walk = GEN_ALL(define
 `(moi_lsp_walk (r:real^N->real^N->bool) [] <=> F) /\
  (moi_lsp_walk r [a] <=> T) /\
  (moi_lsp_walk r (CONS a (CONS b t)) <=> r a b /\ moi_lsp_walk r (CONS b t))`);;

let MOI_LSP_PP_CONS = prove
 (`!(a:real^N) l.
     ~(l = [])
     ==> path_image(polygonal_path(CONS a l)) =
         segment[a,HD l] UNION path_image(polygonal_path l) /\
         homotopic_paths (path_image(polygonal_path(CONS a l)))
           (polygonal_path(CONS a l)) (linepath(a,HD l) ++ polygonal_path l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD] THEN
  STRUCT_CASES_TAC(ISPEC `t:(real^N)list` list_CASES) THENL
   [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real^N`; `h:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MP_TAC(ISPECL [`segment[a:real^N,h]`; `linepath(a:real^N,h)`] HOMOTOPIC_PATHS_RID) THEN
      REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH; SUBSET_REFL]];
    REWRITE_TAC[polygonal_path] THEN
    SUBGOAL_THEN `pathfinish(linepath(a:real^N,h)) =
                  pathstart(polygonal_path(CONS h (CONS h' t')))` ASSUME_TAC THENL
     [REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; HOMOTOPIC_PATHS_REFL; PATH_JOIN;
                 PATH_LINEPATH; PATH_POLYGONAL_PATH; SUBSET_REFL]]);;

let MOI_LSP_PP_APPEND = prove
 (`!l1 l2:(real^N)list.
     ~(l1 = []) /\ ~(l2 = []) /\ LAST l1 = HD l2
     ==> ~(APPEND l1 (TL l2) = []) /\
         HD(APPEND l1 (TL l2)) = HD l1 /\ LAST(APPEND l1 (TL l2)) = LAST l2 /\
         path_image(polygonal_path (APPEND l1 (TL l2))) =
         path_image(polygonal_path l1) UNION path_image(polygonal_path l2) /\
         homotopic_paths (path_image(polygonal_path (APPEND l1 (TL l2))))
           (polygonal_path (APPEND l1 (TL l2))) (polygonal_path l1 ++ polygonal_path l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `l2:(real^N)list` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:(real^N)list = []` THENL
   [SUBGOAL_THEN `(h:real^N) = HD l2` ASSUME_TAC THENL
     [UNDISCH_TAC `LAST (CONS (h:real^N) t) = HD l2` THEN ASM_REWRITE_TAC[LAST];
      ALL_TAC] THEN
    SUBGOAL_THEN `APPEND (CONS (h:real^N) t) (TL l2) = l2` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[CONS_HD_TL]; ALL_TAC] THEN
    SUBGOAL_THEN `pathstart(polygonal_path l2) = (h:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[HD; polygonal_path; PATH_IMAGE_LINEPATH; SEGMENT_REFL] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `polygonal_path(l2:(real^N)list)` PATHSTART_IN_PATH_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MP_TAC(ISPECL [`path_image(polygonal_path(l2:(real^N)list))`;
                     `polygonal_path(l2:(real^N)list)`] HOMOTOPIC_PATHS_LID) THEN
      ASM_REWRITE_TAC[PATH_POLYGONAL_PATH; SUBSET_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l2:(real^N)list`) THEN
  SUBGOAL_THEN `LAST (CONS (h:real^N) t) = LAST t` ASSUME_TAC THENL
   [REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LAST (t:(real^N)list) = HD l2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = APPEND (t:(real^N)list) (TL l2)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `APPEND (CONS (h:real^N) t) (TL l2) = CONS h X` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS (h:real^N) X)) =
    segment[h,HD t] UNION path_image(polygonal_path X) /\
    homotopic_paths (path_image(polygonal_path(CONS h X)))
      (polygonal_path(CONS h X)) (linepath(h,HD t) ++ polygonal_path X)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `HD (X:(real^N)list) = HD t`)) THEN
    MATCH_MP_TAC MOI_LSP_PP_CONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path(CONS (h:real^N) t)) =
    segment[h,HD t] UNION path_image(polygonal_path t) /\
    homotopic_paths (path_image(polygonal_path(CONS h t)))
      (polygonal_path(CONS h t)) (linepath(h,HD t) ++ polygonal_path t)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSP_PP_CONS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(polygonal_path X) = HD(t:(real^N)list) /\
                pathstart(polygonal_path t) = HD t /\
                pathfinish(polygonal_path t) = HD l2 /\
                pathstart(polygonal_path l2) = HD l2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH]; ALL_TAC] THEN
  REWRITE_TAC[NOT_CONS_NIL; HD] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LAST]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(h:real^N,HD t) ++ polygonal_path X` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `linepath(h:real^N,HD t) ++ (polygonal_path t ++ polygonal_path l2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[PATHFINISH_LINEPATH; HOMOTOPIC_PATHS_REFL; PATH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SUBSET_UNION] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
    EXISTS_TAC `path_image(polygonal_path(X:(real^N)list))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(linepath(h:real^N,HD t) ++ polygonal_path t) ++ polygonal_path l2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATH_POLYGONAL_PATH; PATH_IMAGE_LINEPATH;
                    PATHFINISH_LINEPATH] THEN
    SET_TAC[];
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[PATHFINISH_JOIN; HOMOTOPIC_PATHS_REFL; PATH_POLYGONAL_PATH] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
      EXISTS_TAC `path_image(polygonal_path(CONS (h:real^N) t))` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[] THEN SET_TAC[]];
      SET_TAC[]]]);;

let MOI_LSP_WALK_APPEND = prove
 (`!(r:real^N->real^N->bool) l1 l2.
     ~(l1 = []) /\ ~(l2 = []) /\ LAST l1 = HD l2
     ==> (moi_lsp_walk r (APPEND l1 (TL l2)) <=>
          moi_lsp_walk r l1 /\ moi_lsp_walk r l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(ISPEC `t:(real^N)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD; LAST; APPEND] THENL
   [X_GEN_TAC `l2:(real^N)list` THEN
    STRUCT_CASES_TAC(ISPEC `l2:(real^N)list` list_CASES) THEN
    REWRITE_TAC[NOT_CONS_NIL; HD; TL] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[moi_lsp_walk];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `l2:(real^N)list` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l2:(real^N)list`) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; HD] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[moi_lsp_walk; CONJ_ASSOC]);;

(* A list with a repeated member. *)
let MOI_LSP_NOT_PAIRWISE = prove
 (`!l:(real^N)list.
     ~PAIRWISE (\x y. ~(x = y)) l
     ==> ?A x B C. l = APPEND A (CONS x (APPEND B (CONS x C)))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[PAIRWISE; DE_MORGAN_THM] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `MEM (h:real^N) t` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        not (can (find_term (fun u -> is_const u && fst(dest_const u) = "PAIRWISE"))
                 (concl th)))) THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MEM_APPEND_DECOMPOSE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:(real^N)list` (X_CHOOSE_THEN `C:(real^N)list`
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`[]:(real^N)list`; `h:real^N`; `B:(real^N)list`;
                          `C:(real^N)list`] THEN
    REWRITE_TAC[APPEND];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:(real^N)list` (X_CHOOSE_THEN `x:real^N`
      (X_CHOOSE_THEN `B:(real^N)list` (X_CHOOSE_THEN `C:(real^N)list` SUBST1_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:real^N) A`; `x:real^N`; `B:(real^N)list`;
                          `C:(real^N)list`] THEN
    REWRITE_TAC[APPEND]]);;

(* ------------------------------------------------------------------------- *)
(* B2: a closed walk is null under g as soon as all its simple closed       *)
(* sub-walks with at least three edges are (split at a repeated vertex).    *)
(* ------------------------------------------------------------------------- *)

let MOI_LSP_SHORT_NULL = prove
 (`!(l:(real^N)list).
     ~(l = []) /\ HD l = LAST l /\ LENGTH l <= 3
     ==> homotopic_loops (path_image(polygonal_path l)) (polygonal_path l)
                         (linepath(HD l,HD l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  POP_ASSUM(K ALL_TAC) THEN
  STRUCT_CASES_TAC(ISPEC `t:(real^N)list` list_CASES) THEN
  REWRITE_TAC[HD; LAST; TL; LENGTH; NOT_CONS_NIL; polygonal_path] THENL
   [DISCH_TAC THEN
    REWRITE_TAC[HOMOTOPIC_LOOPS_REFL; PATH_LINEPATH; SUBSET_REFL;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t':(real^N)list` list_CASES) THEN
  REWRITE_TAC[HD; LAST; TL; LENGTH; NOT_CONS_NIL; polygonal_path] THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[HOMOTOPIC_LOOPS_REFL; PATH_LINEPATH; SUBSET_REFL;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC(SUC n)) <= 3 <=> n = 0`; LENGTH_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
  REWRITE_TAC[polygonal_path] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `linepath(h':real^N,h) = reversepath(linepath(h,h'))` SUBST1_TAC THENL
   [REWRITE_TAC[REVERSEPATH_LINEPATH]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
              PATHFINISH_REVERSEPATH; PATHSTART_REVERSEPATH] THEN
  MP_TAC(ISPECL [`path_image(linepath(h:real^N,h') ++ reversepath(linepath(h,h')))`;
                 `linepath(h:real^N,h')`] HOMOTOPIC_PATHS_RINV) THEN
  REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_REVERSEPATH; PATHFINISH_LINEPATH; SUBSET_UNION]);;

(* Cutting a null loop out of a path. *)
let MOI_LSP_CUT_NULL = prove
 (`!(s:real^N->bool) p c q.
     path p /\ path c /\ path q /\
     path_image p SUBSET s /\ path_image c SUBSET s /\ path_image q SUBSET s /\
     pathfinish p = pathstart c /\ pathfinish c = pathstart c /\
     pathstart q = pathstart c /\
     homotopic_loops s c (linepath(pathstart c,pathstart c))
     ==> homotopic_paths s ((p ++ c) ++ q) (p ++ q)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `(p ++ linepath(pathstart c,pathstart c)) ++ (q:real^1->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[PATHFINISH_JOIN; HOMOTOPIC_PATHS_REFL; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL THEN
    EXISTS_TAC `pathstart(c:real^1->real^N)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[PATHFINISH_JOIN; HOMOTOPIC_PATHS_REFL; PATHFINISH_LINEPATH] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `pathfinish (p:real^1->real^N) = pathstart c`)) THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_RID THEN ASM_REWRITE_TAC[]]);;

(* Path homotopies in a subset t of s map to path homotopies in v. *)
let MOI_LSP_G_HOM = prove
 (`!(g:real^N->real^M) s v t p q.
     g continuous_on s /\ IMAGE g s SUBSET v /\ t SUBSET s /\ homotopic_paths t p q
     ==> homotopic_paths v (g o p) (g o q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_PATHS_CONTINUOUS_IMAGE THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

let MOI_LSP_CLOSED_WALKS_NULL = prove
 (`!(r:real^N->real^N->bool) (s:real^N->bool) (g:real^N->real^M) v.
     g continuous_on s /\ IMAGE g s SUBSET v /\
     (!J. moi_lsp_walk r J /\ HD J = LAST J /\ 4 <= LENGTH J /\
          PAIRWISE (\x y. ~(x = y)) (TL J) /\
          path_image(polygonal_path J) SUBSET s
          ==> homotopic_loops v (g o polygonal_path J) (linepath(g(HD J),g(HD J))))
     ==> !l. moi_lsp_walk r l /\ HD l = LAST l /\
             path_image(polygonal_path l) SUBSET s
             ==> homotopic_loops v (g o polygonal_path l) (linepath(g(HD l),g(HD l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n l. LENGTH l = n /\ moi_lsp_walk (r:real^N->real^N->bool) l /\ HD l = LAST l /\
          path_image(polygonal_path l) SUBSET s
          ==> homotopic_loops v ((g:real^N->real^M) o polygonal_path l)
                                (linepath(g(HD l),g(HD l)))`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  X_GEN_TAC `l:(real^N)list` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(l:(real^N)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `moi_lsp_walk (r:real^N->real^N->bool) l` THEN
    ASM_REWRITE_TAC[moi_lsp_walk];
    ALL_TAC] THEN
  ASM_CASES_TAC `PAIRWISE (\x y:real^N. ~(x = y)) (TL l)` THENL
   [ASM_CASES_TAC `4 <= LENGTH (l:(real^N)list)` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `l:(real^N)list` MOI_LSP_SHORT_NULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`polygonal_path (l:(real^N)list)`; `linepath(HD l:real^N,HD l)`;
                   `g:real^N->real^M`; `path_image(polygonal_path (l:(real^N)list))`;
                   `v:real^M->bool`] HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[LINEPATH_REFL; o_DEF];
    ALL_TAC] THEN
  (* split at a repeated vertex *)
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_LSP_NOT_PAIRWISE) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(real^N)list` (X_CHOOSE_THEN `x:real^N`
    (X_CHOOSE_THEN `B:(real^N)list` (X_CHOOSE_THEN `C:(real^N)list` ASSUME_TAC)))) THEN
  SUBGOAL_THEN `APPEND (APPEND (CONS (HD l:real^N) (APPEND A [x]))
                               (TL (CONS x (APPEND B [x])))) (TL (CONS x C)) = l`
  ASSUME_TAC THENL
   [REWRITE_TAC[TL; GSYM APPEND_ASSOC; APPEND] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `TL (l:(real^N)list)`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONS_HD_TL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = CONS (HD l:real^N) (APPEND A [x])` THEN
  ABBREV_TAC `L1 = CONS (x:real^N) (APPEND B [x])` THEN
  ABBREV_TAC `S = CONS (x:real^N) C` THEN
  SUBGOAL_THEN
   `~(P:(real^N)list = []) /\ ~(L1:(real^N)list = []) /\ ~(S:(real^N)list = []) /\
    HD P = HD l /\ LAST P = x /\ HD L1 = x /\ LAST L1 = x /\ HD S = x /\
    ~(APPEND P (TL L1) = []) /\ LAST (APPEND P (TL L1)) = x`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "L1"; "S"] THEN
    REWRITE_TAC[NOT_CONS_NIL; HD; TL; LAST; APPEND; APPEND_EQ_NIL; LAST_APPEND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:(real^N)list`; `L1:(real^N)list`] MOI_LSP_PP_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`APPEND P (TL L1):(real^N)list`; `S:(real^N)list`] MOI_LSP_PP_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = `APPEND (APPEND P (TL L1)) (TL S) = l:(real^N)list`
    then REWRITE_TAC[th] else NO_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`P:(real^N)list`; `S:(real^N)list`] MOI_LSP_PP_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `l2 = APPEND P (TL S):(real^N)list` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_lsp_walk (r:real^N->real^N->bool) P /\ moi_lsp_walk r L1 /\
                moi_lsp_walk r S /\ moi_lsp_walk r l2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:real^N->real^N->bool`; `APPEND P (TL L1):(real^N)list`;
                   `S:(real^N)list`] MOI_LSP_WALK_APPEND) THEN
    MP_TAC(ISPECL [`r:real^N->real^N->bool`; `P:(real^N)list`; `L1:(real^N)list`]
      MOI_LSP_WALK_APPEND) THEN
    MP_TAC(ISPECL [`r:real^N->real^N->bool`; `P:(real^N)list`; `S:(real^N)list`]
      MOI_LSP_WALK_APPEND) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (L1:(real^N)list) < n /\ LENGTH (l2:(real^N)list) < n`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `LENGTH (l:(real^N)list) = n`)) THEN
    FIRST_ASSUM(fun th -> if concl th = `APPEND (APPEND P (TL L1)) (TL S) = l:(real^N)list`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MAP_EVERY EXPAND_TAC ["l2"; "P"; "L1"; "S"] THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; TL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(polygonal_path (L1:(real^N)list)) SUBSET s /\
    path_image(polygonal_path (l2:(real^N)list)) SUBSET s /\
    path_image(polygonal_path (P:(real^N)list)) SUBSET s /\
    path_image(polygonal_path (S:(real^N)list)) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image(polygonal_path (l:(real^N)list)) SUBSET s` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `HD (L1:(real^N)list) = LAST L1 /\ HD (l2:(real^N)list) = LAST l2 /\
                HD l2 = HD l`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops v ((g:real^N->real^M) o polygonal_path L1)
                  (linepath(g(HD L1),g(HD L1)))` ASSUME_TAC THENL
   [USE_THEN "IH" (MP_TAC o SPEC `LENGTH (L1:(real^N)list)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops v ((g:real^N->real^M) o polygonal_path l2)
                  (linepath(g(HD l2),g(HD l2)))` ASSUME_TAC THENL
   [USE_THEN "IH" (MP_TAC o SPEC `LENGTH (l2:(real^N)list)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:(real^N)list. path_image(polygonal_path X) SUBSET s
                 ==> path ((g:real^N->real^M) o polygonal_path X) /\
                     path_image (g o polygonal_path X) SUBSET v`
  (LABEL_TAC "GP") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LTD_PATH_IMAGE_IN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[PATH_POLYGONAL_PATH];
    ALL_TAC] THEN
  (* pp l ~ (pp P ++ pp L1) ++ pp S *)
  SUBGOAL_THEN
   `homotopic_paths (path_image(polygonal_path l))
      (polygonal_path l) ((polygonal_path P ++ polygonal_path L1) ++
                          polygonal_path (S:(real^N)list))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `polygonal_path (APPEND P (TL L1)) ++ polygonal_path (S:(real^N)list)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                PATHSTART_POLYGONAL_PATH] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
      EXISTS_TAC `path_image(polygonal_path (APPEND P (TL L1):(real^N)list))` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[] THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  (* compose with g *)
  SUBGOAL_THEN
   `homotopic_paths v ((g:real^N->real^M) o polygonal_path l)
      (((g o polygonal_path P) ++ (g o polygonal_path L1)) ++ (g o polygonal_path S))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_COMPOSE_JOIN] THEN MATCH_MP_TAC MOI_LSP_G_HOM THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `path_image(polygonal_path (l:(real^N)list))`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths v (((g:real^N->real^M) o polygonal_path P) ++ (g o polygonal_path S))
                      (g o polygonal_path l2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_COMPOSE_JOIN] THEN MATCH_MP_TAC MOI_LSP_G_HOM THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `path_image(polygonal_path (l2:(real^N)list))`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* cut the null loop g o pp L1 *)
  MAP_EVERY (fun t -> USE_THEN "GP" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME t))))
    [`path_image(polygonal_path (P:(real^N)list)) SUBSET s`;
     `path_image(polygonal_path (L1:(real^N)list)) SUBSET s`;
     `path_image(polygonal_path (S:(real^N)list)) SUBSET s`] THEN
  SUBGOAL_THEN `homotopic_loops v ((g:real^N->real^M) o polygonal_path L1)
                  (linepath(g x,g x))` ASSUME_TAC THENL
   [UNDISCH_TAC `homotopic_loops v ((g:real^N->real^M) o polygonal_path L1)
                   (linepath(g(HD L1),g(HD L1)))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_paths v
      ((((g:real^N->real^M) o polygonal_path P) ++ (g o polygonal_path L1)) ++
       (g o polygonal_path S))
      ((g o polygonal_path P) ++ (g o polygonal_path S))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LSP_CUT_NULL THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_POLYGONAL_PATH;
                PATHFINISH_POLYGONAL_PATH] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(g:real^N->real^M) o polygonal_path l2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `((g:real^N->real^M) o polygonal_path P) ++ (g o polygonal_path S)` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
      EXISTS_TAC `(((g:real^N->real^M) o polygonal_path P) ++ (g o polygonal_path L1)) ++
                  (g o polygonal_path S)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `homotopic_loops v ((g:real^N->real^M) o polygonal_path l2)
                   (linepath(g(HD l2),g(HD l2)))` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B3a: closed walks without repeated vertices are simple polygons, for any *)
(* edge relation whose distinct edges meet only in common endpoints.        *)
(* ------------------------------------------------------------------------- *)

let MOI_LSP_WALK_MONO = prove
 (`!(r:real^N->real^N->bool) r' l.
     moi_lsp_walk r l /\ (!u w. MEM u l /\ MEM w l /\ r u w ==> r' u w)
     ==> moi_lsp_walk r' l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[moi_lsp_walk] THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(ISPEC `t:(real^N)list` list_CASES) THEN
  REWRITE_TAC[moi_lsp_walk] THEN REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let MOI_LSP_EDGE_MEET = prove
 (`!(r:real^N->real^N->bool) a b l u.
     (!a b c d. r a b /\ r c d /\ ~({a,b} = {c,d})
                ==> segment[a,b] INTER segment[c,d] SUBSET {a,b} INTER {c,d}) /\
     r a b /\ ~(l = []) /\ moi_lsp_walk (\u w. r u w /\ ~({u,w} = {a,b})) (CONS u l)
     ==> segment[a,b] INTER path_image(polygonal_path (CONS u l)) SUBSET
         {a,b} INTER set_of_list (CONS u l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `u:real^N` THEN REWRITE_TAC[moi_lsp_walk] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N`; `CONS (h:real^N) t`] MOI_LSP_PP_CONS) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `segment[a:real^N,b] INTER segment[u,h] SUBSET {a,b} INTER {u,h}`
  ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t:(real^N)list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; SEGMENT_REFL; set_of_list] THEN
    UNDISCH_TAC `segment[a:real^N,b] INTER segment[u,h] SUBSET {a,b} INTER {u,h}` THEN
    MP_TAC(ISPECL [`u:real^N`; `h:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `t:(real^N)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `segment[a:real^N,b] INTER segment[u,h] SUBSET {a,b} INTER {u,h}` THEN
  UNDISCH_TAC `segment[a:real^N,b] INTER path_image(polygonal_path (CONS h t)) SUBSET
               {a,b} INTER set_of_list (CONS h t)` THEN
  REWRITE_TAC[set_of_list] THEN SET_TAC[]);;

let MOI_LSP_ARC = prove
 (`!(r:real^N->real^N->bool) t a.
     (!a b c d. r a b /\ r c d /\ ~({a,b} = {c,d})
                ==> segment[a,b] INTER segment[c,d] SUBSET {a,b} INTER {c,d}) /\
     ~(t = []) /\ moi_lsp_walk r (CONS a t) /\ PAIRWISE (\x y. ~(x = y)) (CONS a t)
     ==> arc(polygonal_path (CONS a t))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  X_GEN_TAC `a:real^N` THEN
  REWRITE_TAC[moi_lsp_walk; PAIRWISE; ALL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:(real^N)list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[polygonal_path] THEN
    MATCH_MP_TAC ARC_LINEPATH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `t:(real^N)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[PAIRWISE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `polygonal_path(CONS (a:real^N) (CONS h t)) =
                linepath(a,h) ++ polygonal_path(CONS h t)` SUBST1_TAC THENL
   [MATCH_MP_TAC POLYGONAL_PATH_CONS_CONS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`linepath(a:real^N,h)`; `polygonal_path(CONS (h:real^N) t)`]
    ARC_JOIN_EQ) THEN
  REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  SUBGOAL_THEN `~MEM (a:real^N) (CONS h t)` ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^N->real^N->bool`; `a:real^N`; `h:real^N`; `t:(real^N)list`;
                 `h:real^N`] MOI_LSP_EDGE_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LSP_WALK_MONO THEN
    EXISTS_TAC `r:real^N->real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N) IN {u,w}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `CONS (h:real^N) t`] IN_SET_OF_LIST) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_LSP_SIMPLE_POLYGON = prove
 (`!(r:real^N->real^N->bool) J.
     (!a b c d. r a b /\ r c d /\ ~({a,b} = {c,d})
                ==> segment[a,b] INTER segment[c,d] SUBSET {a,b} INTER {c,d}) /\
     moi_lsp_walk r J /\ HD J = LAST J /\ 4 <= LENGTH J /\
     PAIRWISE (\x y. ~(x = y)) (TL J)
     ==> simple_path(polygonal_path J) /\
         pathfinish(polygonal_path J) = pathstart(polygonal_path J)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `J:(real^N)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(4 <= 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t:(real^N)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(4 <= SUC 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t':(real^N)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(4 <= SUC(SUC 0))`] THEN
  REWRITE_TAC[ARITH_RULE `4 <= SUC(SUC(SUC n)) <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
  REWRITE_TAC[HD; TL; LAST; NOT_CONS_NIL] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o REWRITE_RULE[ASSUME `~(t:(real^N)list = [])`] o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `h:real^N`)) THEN
  SUBGOAL_THEN `MEM (h:real^N) t` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[MOI_SA2_MEM_HD_LAST]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[PAIRWISE; ALL] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "PAIRWISE")) (concl th))) THEN
  SUBGOAL_THEN `~(h':real^N = h) /\ ~(h'':real^N = h) /\ ~MEM (h':real^N) t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_lsp_walk] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_lsp_walk")) (concl th))) THEN
  SUBGOAL_THEN `polygonal_path(CONS (h:real^N) (CONS h' (CONS h'' t))) =
                linepath(h,h') ++ polygonal_path(CONS h' (CONS h'' t))` SUBST1_TAC THENL
   [MATCH_MP_TAC POLYGONAL_PATH_CONS_CONS THEN REWRITE_TAC[NOT_CONS_NIL]; ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish(polygonal_path(CONS (h':real^N) (CONS h'' t))) = h /\
                pathstart(polygonal_path(CONS (h':real^N) (CONS h'' t))) = h'`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH; NOT_CONS_NIL; HD;
                LAST] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
  MP_TAC(ISPECL [`linepath(h:real^N,h')`; `polygonal_path(CONS (h':real^N) (CONS h'' t))`]
    SIMPLE_PATH_JOIN_LOOP_EQ) THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(h:real^N = h')` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LSP_ARC THEN EXISTS_TAC `r:real^N->real^N->bool` THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; moi_lsp_walk];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^N`; `CONS (h'':real^N) t`] MOI_LSP_PP_CONS) THEN
  REWRITE_TAC[NOT_CONS_NIL; HD] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `segment[h:real^N,h'] INTER segment[h',h''] SUBSET {h,h'} INTER {h',h''}`
  MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 4
      then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N) IN {h',h''}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^N->real^N->bool`; `h:real^N`; `h':real^N`; `t:(real^N)list`;
                 `h'':real^N`] MOI_LSP_EDGE_MEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LSP_WALK_MONO THEN
    EXISTS_TAC `r:real^N->real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h':real^N) IN {u,w}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `MEM (u:real^N) (CONS h'' t)` THEN
    UNDISCH_TAC `MEM (w:real^N) (CONS h'' t)` THEN
    REWRITE_TAC[MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The square grid of mesh d in the plane: unit steps between lattice       *)
(* points.  Distinct grid edges meet only in common endpoints.               *)
(* ------------------------------------------------------------------------- *)

let moi_lsp_grid = new_definition
 `moi_lsp_grid (d:real) (a:real^2) (b:real^2) <=>
    integer(a$1 / d) /\ integer(a$2 / d) /\
    ((b$1 = a$1 + d \/ b$1 = a$1 - d) /\ b$2 = a$2 \/
     b$1 = a$1 /\ (b$2 = a$2 + d \/ b$2 = a$2 - d))`;;

let MOI_LSP_INT_UNIT = prove
 (`!m n u v. integer m /\ integer n /\ &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1 /\
             m + u = n + v
             ==> m = n /\ u = v \/ m = n + &1 /\ u = &0 /\ v = &1 \/
                 n = m + &1 /\ u = &1 /\ v = &0`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPECL [`m:real`; `n:real`] REAL_LT_TOTAL) THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `m + &1 <= n` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_INTEGERS]; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `n + &1 <= m` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LT_INTEGERS]; ASM_REAL_ARITH_TAC]]);;

let MOI_LSP_INT_01 = prove
 (`!m n u. integer m /\ integer n /\ &0 <= u /\ u <= &1 /\ m + u = n
           ==> u = &0 \/ u = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:real`; `n:real`; `u:real`; `&0`] MOI_LSP_INT_UNIT) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN REAL_ARITH_TAC);;

let MOI_LSP_BASIS2 = prove
 (`(basis 1:real^2)$1 = &1 /\ (basis 1:real^2)$2 = &0 /\
   (basis 2:real^2)$1 = &0 /\ (basis 2:real^2)$2 = &1`,
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH]);;

(* A common point of two distinct standard grid edges is an end of the first. *)
let MOI_LSP_GRID_STD_END = prove
 (`!d (p:real^2) q k l x.
     &0 < d /\ integer(p$1 / d) /\ integer(p$2 / d) /\
     integer(q$1 / d) /\ integer(q$2 / d) /\
     (k = 1 \/ k = 2) /\ (l = 1 \/ l = 2) /\
     ~({p, p + d % basis k} = {q, q + d % basis l}) /\
     x IN segment[p, p + d % basis k] /\ x IN segment[q, q + d % basis l]
     ==> x = p \/ x = p + d % basis k`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC o REWRITE_RULE[IN_SEGMENT]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC o REWRITE_RULE[IN_SEGMENT]) THEN
  SUBGOAL_THEN `(x:real^2)$1 = (p:real^2)$1 + u * d * (basis k:real^2)$1 /\
                (x:real^2)$2 = (p:real^2)$2 + u * d * (basis k:real^2)$2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `x = (&1 - u) % p + u % (p + d % basis k:real^2)`
      then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$1 = (q:real^2)$1 + v * d * (basis l:real^2)$1 /\
                (x:real^2)$2 = (q:real^2)$2 + v * d * (basis l:real^2)$2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `x = (&1 - v) % q + v % (q + d % basis l:real^2)`
      then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `x = (&1 - v) % q + v % (q + d % basis l:real^2)`)) THEN
  SUBGOAL_THEN `u = &0 \/ u = &1` MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL [DISJ1_TAC; DISJ2_TAC] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `x:real^2`
      then SUBST1_TAC th else NO_TAC) THEN VECTOR_ARITH_TAC] THEN
  ABBREV_TAC `P1 = (p:real^2)$1 / d` THEN ABBREV_TAC `P2 = (p:real^2)$2 / d` THEN
  ABBREV_TAC `Q1 = (q:real^2)$1 / d` THEN ABBREV_TAC `Q2 = (q:real^2)$2 / d` THEN
  SUBGOAL_THEN `(p:real^2)$1 = d * P1 /\ (p:real^2)$2 = d * P2 /\
                (q:real^2)$1 = d * Q1 /\ (q:real^2)$2 = d * Q2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P1"; "P2"; "Q1"; "Q2"] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. d * a = d * b ==> a = b` (LABEL_TAC "CANCEL") THENL
   [REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `k:num`)) (concl th))) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `l:num`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_LSP_BASIS2; REAL_MUL_RID; REAL_MUL_RZERO;
                              REAL_ADD_RID]) THENL
   [SUBGOAL_THEN `~((P1:real) = Q1 /\ (P2:real) = Q2)` ASSUME_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `p:real^2 = q` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        can (find_term ((=) `basis 1:real^2`)) (concl th))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(P2:real) = Q2 /\ P1 + u = Q1 + v` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "CANCEL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`P1:real`; `Q1:real`; `u:real`; `v:real`] MOI_LSP_INT_UNIT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `P1 + u = (Q1:real)` ASSUME_TAC THENL
     [USE_THEN "CANCEL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LSP_INT_01 THEN MAP_EVERY EXISTS_TAC [`P1:real`; `Q1:real`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `P2 + u = (Q2:real)` ASSUME_TAC THENL
     [USE_THEN "CANCEL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LSP_INT_01 THEN MAP_EVERY EXISTS_TAC [`P2:real`; `Q2:real`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~((P1:real) = Q1 /\ (P2:real) = Q2)` ASSUME_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `p:real^2 = q` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        can (find_term ((=) `basis 2:real^2`)) (concl th))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(P1:real) = Q1 /\ P2 + u = Q2 + v` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "CANCEL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`P2:real`; `Q2:real`; `u:real`; `v:real`] MOI_LSP_INT_UNIT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;


let MOI_LSP_GRID_STD = prove
 (`!d (a:real^2) b.
     &0 < d /\ moi_lsp_grid d a b
     ==> ?p k. integer(p$1 / d) /\ integer(p$2 / d) /\ (k = 1 \/ k = 2) /\
               {a,b} = {p, p + d % basis k}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsp_grid] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:real^2`; `1`];
    MAP_EVERY EXISTS_TAC [`b:real^2`; `1`];
    MAP_EVERY EXISTS_TAC [`a:real^2`; `2`];
    MAP_EVERY EXISTS_TAC [`b:real^2`; `2`]] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [SUBGOAL_THEN `((a:real^2)$1 - d) / d = a$1 / d - &1 /\
                   ((a:real^2)$2 - d) / d = a$2 / d - &1` (fun th -> REWRITE_TAC[th]) THENL
      [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
     ASM_SIMP_TAC[INTEGER_CLOSED];
     ALL_TAC] ORELSE ALL_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; MOI_LSP_BASIS2] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_LSP_GRID_NE = prove
 (`!d (a:real^2) b. &0 < d /\ moi_lsp_grid d a b ==> ~(a = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lsp_grid] THEN STRIP_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_GRID_MEET = prove
 (`!d (a:real^2) b c e.
     &0 < d /\ moi_lsp_grid d a b /\ moi_lsp_grid d c e /\ ~({a,b} = {c,e})
     ==> segment[a,b] INTER segment[c,e] SUBSET {a,b} INTER {c,e}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `a:real^2`; `b:real^2`] MOI_LSP_GRID_STD) THEN
  MP_TAC(SPECL [`d:real`; `c:real^2`; `e:real^2`] MOI_LSP_GRID_STD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^2` (X_CHOOSE_THEN `l:num`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `k:num`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN `segment[a:real^2,b] = segment[p,p + d % basis k] /\
                segment[c:real^2,e] = segment[q,q + d % basis l]`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[CONJUNCT1 SEGMENT_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LSP_GRID_STD_END THEN
    MAP_EVERY EXISTS_TAC [`q:real^2`; `l:num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_LSP_GRID_STD_END THEN
    MAP_EVERY EXISTS_TAC [`p:real^2`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let MOI_LSP_GRID_POLYGON = prove
 (`!d (J:(real^2)list).
     &0 < d /\ moi_lsp_walk (moi_lsp_grid d) J /\ HD J = LAST J /\ 4 <= LENGTH J /\
     PAIRWISE (\x y. ~(x = y)) (TL J)
     ==> simple_path(polygonal_path J) /\
         pathfinish(polygonal_path J) = pathstart(polygonal_path J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_LSP_SIMPLE_POLYGON THEN
  EXISTS_TAC `moi_lsp_grid d` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LSP_GRID_MEET THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3b: a simple closed PL loop g in the plane bounds a PL disk, with a PL  *)
(* homeomorphism e from std_triangle such that e o std_triangle_loop = g on *)
(* [0,1].  moi_lsp_tau inverts std_triangle_loop on the frontier.           *)
(* ------------------------------------------------------------------------- *)

let moi_lsp_tau = new_definition
 `moi_lsp_tau (x:real^2) =
    if x$2 = &0 then x$1 / &2
    else if x$1 = &0 then &1 - x$2 / &4
    else &1 / &2 + x$2 / &4`;;

let MOI_LSP_STL_EXPLICIT = prove
 (`!t. std_triangle_loop t =
       if drop t <= &1 / &2 then (&2 * drop t) % basis 1:real^2
       else if drop t <= &3 / &4
            then (&3 - &4 * drop t) % basis 1 + (&4 * drop t - &2) % basis 2
            else (&4 - &4 * drop t) % basis 2`,
  GEN_TAC THEN REWRITE_TAC[std_triangle_loop; joinpaths; linepath] THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  ASM_CASES_TAC `drop t <= &1 / &2` THEN ASM_REWRITE_TAC[] THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * drop t - &1 <= &1 / &2 <=> drop t <= &3 / &4` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_LSP_TAU_STL = prove
 (`!t. t IN interval[vec 0,vec 1] /\ drop t < &1
       ==> moi_lsp_tau(std_triangle_loop t) = drop t`,
  GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_LSP_STL_EXPLICIT] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[moi_lsp_tau; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; MOI_LSP_BASIS2] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_TAU_RF = prove
 (`!x:real^2. x IN relative_frontier std_triangle
              ==> &0 <= moi_lsp_tau x /\ moi_lsp_tau x < &1 /\
                  std_triangle_loop(lift(moi_lsp_tau x)) = x`,
  GEN_TAC THEN REWRITE_TAC[MOI_LSP_STD_FRONTIER_EXPLICIT; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lsp_tau] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[MOI_LSP_STL_EXPLICIT; LIFT_DROP] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              MOI_LSP_BASIS2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LSP_EDGE_PL = prove
 (`!(g:real^1->real^N) (s:real^2->bool) a b c.
     pl_map_on (interval[vec 0,vec 1]) g /\ locally_polyhedral s /\
     (!x. x IN s ==> &0 <= a * x$1 + b * x$2 + c /\ a * x$1 + b * x$2 + c <= &1)
     ==> pl_map_on s (\x. g(lift(a * x$1 + b * x$2 + c)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^2. (g:real^1->real^N)(lift(a * x$1 + b * x$2 + c))) =
                g o (\x. lift(a * x$1 + b * x$2 + c))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_SIMP_TAC[MOI_LSP_PL_AFFINE_FN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  ASM_SIMP_TAC[]);;

let MOI_LSP_STD_EDGES = prove
 (`(!x:real^2. x IN segment[vec 0,basis 1] ==> &0 <= x$1 /\ x$1 <= &1 /\ x$2 = &0) /\
   (!x:real^2. x IN segment[basis 1,basis 2]
               ==> &0 <= x$2 /\ x$2 <= &1 /\ x$1 + x$2 = &1) /\
   (!x:real^2. x IN segment[basis 2,vec 0] ==> x$1 = &0 /\ &0 <= x$2 /\ x$2 <= &1)`,
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
                  MOI_LSP_BASIS2] THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_EDGE_FACTS_TAC =
  FIRST_ASSUM(fun th -> FIRST (map (fun e g -> STRIP_ASSUME_TAC (MATCH_MP e th) g)
    [CONJUNCT1 MOI_LSP_STD_EDGES; CONJUNCT1(CONJUNCT2 MOI_LSP_STD_EDGES);
     CONJUNCT2(CONJUNCT2 MOI_LSP_STD_EDGES)]));;

let MOI_LSP_PL_LOOP_DISK = prove
 (`!g:real^1->real^2.
     simple_path g /\ pathfinish g = pathstart g /\ pl_map_on (interval[vec 0,vec 1]) g
     ==> ?e e'. pl_homeomorphism (std_triangle,path_image g UNION inside(path_image g))
                                 (e,e') /\
                IMAGE e (relative_frontier std_triangle) = path_image g /\
                !t. t IN interval[vec 0,vec 1] ==> e(std_triangle_loop t) = g t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `b = \x:real^2. (g:real^1->real^2)(lift(moi_lsp_tau x))` THEN
  SUBGOAL_THEN `(g:real^1->real^2)(vec 1) = g(vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  (* b is PL on the frontier *)
  SUBGOAL_THEN `pl_map_on (relative_frontier std_triangle) (b:real^2->real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_FRONTIER] THEN
    SUBGOAL_THEN
     `pl_map_on (segment[vec 0,basis 1]) (b:real^2->real^2) /\
      pl_map_on (segment[basis 1,basis 2]) (b:real^2->real^2) /\
      pl_map_on (segment[basis 2,vec 0]) (b:real^2->real^2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THENL
       [EXISTS_TAC `\x:real^2. (g:real^1->real^2)(lift(&1 / &2 * x$1 + &0 * x$2 + &0))`;
        EXISTS_TAC `\x:real^2. (g:real^1->real^2)(lift(&0 * x$1 + &1 / &4 * x$2 + &1 / &2))`;
        EXISTS_TAC `\x:real^2. (g:real^1->real^2)(lift(&0 * x$1 + -- (&1 / &4) * x$2 + &1))`]
      THEN
      (CONJ_TAC THENL
        [EXPAND_TAC "b" THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
         MOI_LSP_EDGE_FACTS_TAC THEN
         REWRITE_TAC[moi_lsp_tau] THEN REPEAT COND_CASES_TAC THEN
         TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC) THEN
         SUBGOAL_THEN `x:real^2 = vec 0` SUBST1_TAC THENL
          [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT]; ALL_TAC] THEN
         REWRITE_TAC[VEC_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
         ASM_REWRITE_TAC[LIFT_NUM];
         MATCH_MP_TAC MOI_LSP_EDGE_PL THEN
         ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_SEGMENT] THEN
         X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
         MOI_LSP_EDGE_FACTS_TAC THEN
         ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
      REWRITE_TAC[CLOSED_SEGMENT] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[CLOSED_SEGMENT] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* b is injective on the frontier *)
  SUBGOAL_THEN `!x y. x IN relative_frontier std_triangle /\
                      y IN relative_frontier std_triangle /\
                      (b:real^2->real^2) x = b y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real^2` MOI_LSP_TAU_RF) THEN MP_TAC(SPEC `y:real^2` MOI_LSP_TAU_RF) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `moi_lsp_tau x = moi_lsp_tau y` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`lift(moi_lsp_tau x)`; `lift(moi_lsp_tau y)`] o
        CONJUNCT2 o REWRITE_RULE[simple_path] o
        check (fun th -> concl th = `simple_path (g:real^1->real^2)`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(b:real^2->real^2) x = b y` THEN EXPAND_TAC "b" THEN REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* its image is the loop *)
  SUBGOAL_THEN `IMAGE (b:real^2->real^2) (relative_frontier std_triangle) = path_image g`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; path_image] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_TAC THEN EXPAND_TAC "b" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      MP_TAC(SPEC `x:real^2` MOI_LSP_TAU_RF) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      ASM_CASES_TAC `drop t < &1` THENL
       [EXISTS_TAC `std_triangle_loop t` THEN CONJ_TAC THENL
         [EXPAND_TAC "b" THEN ASM_SIMP_TAC[MOI_LSP_TAU_STL; LIFT_DROP];
          REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)))] THEN
          REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
        EXISTS_TAC `vec 0:real^2` THEN
        REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LTD_FRONTIER_SUBSET_TRIANGLE))] THEN
        SUBGOAL_THEN `t = vec 1:real^1` SUBST1_TAC THENL
         [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
          UNDISCH_TAC `~(drop t < &1)` THEN
          REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        EXPAND_TAC "b" THEN
        REWRITE_TAC[moi_lsp_tau; VEC_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC[LIFT_NUM]]];
    ALL_TAC] THEN
  (* the PL circle and its disk *)
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `b:real^2->real^2`]
    PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`std_triangle`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b':real^2->real^2`) THEN
  SUBGOAL_THEN `pl_sphere 1 (path_image (g:real^1->real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier std_triangle`; `b:real^2->real^2`;
                          `b':real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    REWRITE_TAC[ARITH_RULE `1 + 1 = 2`; MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `path_image (g:real^1->real^2)` MOI_S5C_PLANE_DISK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `std_triangle`; `relative_frontier std_triangle`;
                 `path_image g UNION inside(path_image (g:real^1->real^2))`;
                 `path_image (g:real^1->real^2)`;
                 `b:real^2->real^2`; `b':real^2->real^2`] MOI_S5C_CELL_EXT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`std_triangle`; `\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[IMAGE_ID; MOI_LTD_STD_TRIANGLE_SIMPLEX; pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->real^2` (X_CHOOSE_THEN `e':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real^2->real^2`; `e':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (b:real^2->real^2) (relative_frontier std_triangle)`)) THEN
    MATCH_MP_TAC MOI_LTD_IMAGE_EQ_RF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `std_triangle_loop t IN relative_frontier std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)))] THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `drop t < &1` THENL
   [ASM_SIMP_TAC[MOI_LSP_TAU_STL; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `t = vec 1:real^1` SUBST1_TAC THENL
   [UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
    UNDISCH_TAC `~(drop t < &1)` THEN
    REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REWRITE_RULE[pathfinish] (CONJUNCT1(CONJUNCT2(CONJUNCT2
    MOI_LTD_STD_TRIANGLE_LOOP)))] THEN
  REWRITE_TAC[moi_lsp_tau; VEC_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[LIFT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* B1: approximation of a loop in an open planar set by a closed grid walk. *)
(* ------------------------------------------------------------------------- *)

let moi_lsp_round = new_definition
 `moi_lsp_round (d:real) (x:real^2) =
    vector[d * floor(x$1 / d); d * floor(x$2 / d)]:real^2`;;

let MOI_LSP_NORM_L1 = prove
 (`!x:real^2. norm x <= abs(x$1) + abs(x$2) /\ abs(x$1) + abs(x$2) <= &2 * norm x`,
  GEN_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `x:real^2` NORM_LE_L1) THEN REWRITE_TAC[DIMINDEX_2; SUM_2];
    MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`x:real^2`; `2`] COMPONENT_LE_NORM) THEN REAL_ARITH_TAC]);;

let MOI_LSP_ROUND = prove
 (`!d (x:real^2).
     &0 < d
     ==> integer((moi_lsp_round d x)$1 / d) /\ integer((moi_lsp_round d x)$2 / d) /\
         dist(moi_lsp_round d x,x) < &2 * d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lsp_round; VECTOR_2] THEN
  SUBGOAL_THEN `!y. (d * floor(y / d)) / d = floor(y / d)` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[FLOOR] THEN
  SUBGOAL_THEN `!y. abs(d * floor(y / d) - y) < d` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `y / d` FLOOR) THEN
    SUBGOAL_THEN `y = d * (y / d)` MP_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SPEC_TAC(`y / d`,`z:real`) THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `d * floor z <= d * z /\ d * z < d * (floor z + &1)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LMUL_EQ]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `vector[d * floor((x:real^2)$1 / d); d * floor(x$2 / d)] - x:real^2`
    MOI_LSP_NORM_L1) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  MP_TAC(SPEC `(x:real^2)$1` (ASSUME `!y. abs(d * floor(y / d) - y) < d`)) THEN
  MP_TAC(SPEC `(x:real^2)$2` (ASSUME `!y. abs(d * floor(y / d) - y) < d`)) THEN
  REAL_ARITH_TAC);;

let MOI_LSP_WALK_CONS = prove
 (`!(r:real^N->real^N->bool) a l.
     ~(l = []) ==> (moi_lsp_walk r (CONS a l) <=> r a (HD l) /\ moi_lsp_walk r l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[moi_lsp_walk]);;

let MOI_LSP_COMPACT_CBALL = prove
 (`!k u:real^N->bool.
     compact k /\ open u /\ k SUBSET u
     ==> ?e. &0 < e /\ !x. x IN k ==> cball(x,e) SUBSET u`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(:real^N) DIFF u = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `setdist(k,(:real^N) DIFF u) / &2` THEN
  SUBGOAL_THEN `&0 < setdist(k,(:real^N) DIFF u)` ASSUME_TAC THENL
   [REWRITE_TAC[SETDIST_POS_LT] THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; GSYM OPEN_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF u`; `x:real^N`; `y:real^N`]
    SETDIST_LE_DIST) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_LATTICE_FACTS = prove
 (`!d. &0 < d
       ==> (!a. integer(a / d) ==> integer((a + d) / d) /\ integer((a - d) / d) /\
                                   integer((a + d * &1) / d) /\ integer((a - d * &1) / d)) /\
           (!a b. integer(a / d) /\ integer(b / d) /\ ~(a = b) ==> d <= abs(a - b)) /\
           (!a b. integer(a / d) /\ integer(b / d)
                  ==> ?n. abs(a - b) = &n * d)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a + d) / d = a / d + &1 /\ (a - d) / d = a / d - &1 /\
                  (a + d * &1) / d = a / d + &1 /\ (a - d * &1) / d = a / d - &1`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[INTEGER_CLOSED]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `a - b = d * (a / d - b / d)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(a:real = b)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `a / d - b / d = &0` THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `abs(a / d - b / d)` INTEGER_POS) THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    SUBGOAL_THEN `a - b = d * (a / d - b / d)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN REAL_ARITH_TAC]);;

let MOI_LSP_STAIR_STEP = prove
 (`!d (z:real^2) (z':real^2) m.
     &0 < d /\ integer(z$1 / d) /\ integer(z$2 / d) /\
     integer(z'$1 / d) /\ integer(z'$2 / d) /\
     abs(z'$1 - z$1) + abs(z'$2 - z$2) = &(SUC m) * d
     ==> ?z1. moi_lsp_grid d z z1 /\ integer(z1$1 / d) /\ integer(z1$2 / d) /\
              dist(z,z1) = d /\ abs(z'$1 - z1$1) + abs(z'$2 - z1$2) = &m * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSP_LATTICE_FACTS) THEN
  SUBGOAL_THEN `!k. k = 1 \/ k = 2 ==> norm(d % basis k:real^2) = d` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID]) THEN
  ASM_CASES_TAC `(z':real^2)$1 = (z:real^2)$1` THENL
   [SUBGOAL_THEN `~((z':real^2)$2 = (z:real^2)$2)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
        `abs((z':real^2)$1 - (z:real^2)$1) + abs((z':real^2)$2 - (z:real^2)$2) = &m * d + d` THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
      MP_TAC(SPEC `m:num` REAL_POS) THEN
      SUBGOAL_THEN `&0 <= &m * d` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `d <= abs((z':real^2)$2 - (z:real^2)$2)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `abs`)) (concl th) && not(is_exists(snd(strip_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^2)$2 < (z':real^2)$2` THENL
     [EXISTS_TAC `z + d % basis 2:real^2`; EXISTS_TAC `z - d % basis 2:real^2`];
    SUBGOAL_THEN `d <= abs((z':real^2)$1 - (z:real^2)$1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `abs`)) (concl th) && not(is_exists(snd(strip_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^2)$1 < (z':real^2)$1` THENL
     [EXISTS_TAC `z + d % basis 1:real^2`; EXISTS_TAC `z - d % basis 1:real^2`]] THEN
  ASM_SIMP_TAC[NORM_ARITH `dist(z:real^2,z + y) = norm y /\ dist(z,z - y) = norm y`;
               ARITH] THEN
  REWRITE_TAC[moi_lsp_grid; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; MOI_LSP_BASIS2; REAL_MUL_RID; REAL_MUL_RZERO;
              REAL_ADD_RID; REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_STAIRCASE = prove
 (`!d n (z:real^2) (z':real^2).
     &0 < d /\ integer(z$1 / d) /\ integer(z$2 / d) /\
     integer(z'$1 / d) /\ integer(z'$2 / d) /\
     abs(z'$1 - z$1) + abs(z'$2 - z$2) = &n * d
     ==> ?W. moi_lsp_walk (moi_lsp_grid d) W /\ ~(W = []) /\ HD W = z /\ LAST W = z' /\
             path_image(polygonal_path W) SUBSET cball(z,&n * d)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `[z:real^2]` THEN
    SUBGOAL_THEN `z':real^2 = z` SUBST1_TAC THENL
     [UNDISCH_TAC `abs((z':real^2)$1 - (z:real^2)$1) + abs((z':real^2)$2 - (z:real^2)$2) =
                   &0 * d` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[moi_lsp_walk; NOT_CONS_NIL; HD; LAST; polygonal_path; PATH_IMAGE_LINEPATH;
                SEGMENT_REFL; REAL_MUL_LZERO; SING_SUBSET; CENTRE_IN_CBALL; REAL_LE_REFL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `z:real^2`; `z':real^2`; `n:num`] MOI_LSP_STAIR_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z1:real^2`; `z':real^2`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^2)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (z:real^2) W` THEN
  ASM_SIMP_TAC[MOI_LSP_WALK_CONS; NOT_CONS_NIL; HD; LAST] THEN
  MP_TAC(ISPECL [`z:real^2`; `W:(real^2)list`] MOI_LSP_PP_CONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 <= &n * d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^2,d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CBALL; IN_CBALL; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_CBALL THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z1:real^2,&n * d)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^2` THEN
    MP_TAC(ISPECL [`z:real^2`; `z1:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LSP_STAIR = prove
 (`!d (z:real^2) (z':real^2).
     &0 < d /\ integer(z$1 / d) /\ integer(z$2 / d) /\
     integer(z'$1 / d) /\ integer(z'$2 / d)
     ==> ?W. moi_lsp_walk (moi_lsp_grid d) W /\ ~(W = []) /\ HD W = z /\ LAST W = z' /\
             path_image(polygonal_path W) SUBSET
             cball(z,abs(z'$1 - z$1) + abs(z'$2 - z$2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LSP_LATTICE_FACTS) THEN
  SUBGOAL_THEN `?n. abs((z':real^2)$1 - (z:real^2)$1) + abs((z':real^2)$2 - (z:real^2)$2) =
                    &n * d`
  (X_CHOOSE_TAC `n:num`) THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`(z':real^2)$1`; `(z:real^2)$1`] th) THEN
                            MP_TAC(SPECL [`(z':real^2)$2`; `(z:real^2)$2`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
    EXISTS_TAC `n1 + n2:num` THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LSP_STAIRCASE THEN ASM_REWRITE_TAC[]);;

(* Two pieces with connecting segments telescope. *)
let MOI_LSP_TELE2 = prove
 (`!s (c0:real^1->real^N) q1 d1 q2 c2.
     path c0 /\ path q1 /\ path d1 /\ path q2 /\ path c2 /\
     path_image c0 SUBSET s /\ path_image q1 SUBSET s /\ path_image d1 SUBSET s /\
     path_image q2 SUBSET s /\ path_image c2 SUBSET s /\
     pathfinish c0 = pathstart q1 /\ pathfinish q1 = pathstart d1 /\
     pathstart q2 = pathfinish q1 /\ pathfinish q2 = pathstart c2
     ==> homotopic_paths s ((c0 ++ q1 ++ d1) ++ (reversepath d1 ++ q2 ++ c2))
                           (c0 ++ (q1 ++ q2) ++ c2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a:real^N = pathstart d1` THEN
  SUBGOAL_THEN
   `!p q:real^1->real^N. path p /\ path q /\ path_image p SUBSET s /\
                          path_image q SUBSET s /\ pathfinish p = pathstart q
                          ==> path(p ++ q) /\ path_image(p ++ q) SUBSET s`
  (LABEL_TAC "J") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path(reversepath d1:real^1->real^N) /\ path_image(reversepath d1) SUBSET s /\
                pathstart(reversepath d1) = pathfinish d1 /\
                pathfinish(reversepath d1) = (a:real^N)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path(q2 ++ c2:real^1->real^N) /\ path_image(q2 ++ c2) SUBSET s /\
                pathstart(q2 ++ c2) = a /\ pathfinish(q2 ++ c2) = pathfinish c2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    USE_THEN "J" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path(reversepath d1 ++ q2 ++ c2:real^1->real^N) /\
                path_image(reversepath d1 ++ q2 ++ c2) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "J" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path(q1 ++ d1:real^1->real^N) /\ path_image(q1 ++ d1) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "J" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path(d1 ++ reversepath d1 ++ q2 ++ c2:real^1->real^N) /\
                path_image(d1 ++ reversepath d1 ++ q2 ++ c2) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "J" MATCH_MP_TAC THEN ASM_REWRITE_TAC[PATHSTART_JOIN]; ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish q1:real^N = a` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the chain *)
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `c0 ++ ((q1 ++ d1) ++ (reversepath d1 ++ q2 ++ c2)):real^1->real^N` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `c0 ++ (q1 ++ (d1 ++ (reversepath d1 ++ q2 ++ c2))):real^1->real^N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `c0 ++ (q1 ++ (linepath(a,a) ++ (q2 ++ c2))):real^1->real^N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(d1 ++ reversepath d1) ++ (q2 ++ c2):real^1->real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      FIRST_ASSUM(fun th -> if concl th = `pathstart d1:real^N = a`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      MATCH_MP_TAC HOMOTOPIC_PATHS_RINV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
  ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `q1 ++ (q2 ++ c2):real^1->real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
    SUBGOAL_THEN `linepath(a:real^N,a) =
                  linepath(pathstart(q2 ++ c2),pathstart(q2 ++ c2:real^1->real^N))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LID THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_LSP_SUBPATH_PROPS = prove
 (`!(q:real^1->real^N) a b n (P:real^N->bool) h.
     a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\ drop a <= drop b /\
     drop b - drop a <= &1 / &2 /\
     (!t. t IN interval[vec 0,vec 1] ==> P(q t)) /\
     (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
            abs(drop s - drop t) <= inv(&2 pow (SUC n)) ==> dist(q s,q t) <= h)
     ==> (!t. t IN interval[vec 0,vec 1] ==> P(subpath a b q t)) /\
         (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                abs(drop s - drop t) <= inv(&2 pow n)
                ==> dist(subpath a b q s,subpath a b q t) <= h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                    ==> a + drop(b - a) % t IN interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    UNDISCH_TAC `a IN interval[vec 0:real^1,vec 1]` THEN
    UNDISCH_TAC `b IN interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= x ==> &0 <= a + x`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(drop b - drop a) * drop t <= (drop b - drop a) * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[subpath] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_SUB;
              REAL_ARITH `(a + c * s) - (a + c * t) = c * (s - t)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; real_pow; REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LSP_ROUND_SEG = prove
 (`!d e (U:real^2->bool) x.
     &0 < d /\ &2 * d <= e /\ cball(x,e) SUBSET U
     ==> segment[moi_lsp_round d x,x] SUBSET U /\ segment[x,moi_lsp_round d x] SUBSET U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[SEGMENT_SYM]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^2,e)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
  REWRITE_TAC[CONVEX_CBALL; IN_CBALL; DIST_REFL] THEN
  MP_TAC(SPECL [`d:real`; `x:real^2`] MOI_LSP_ROUND) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC);;

let MOI_LSP_GRID_CORE = prove
 (`!(U:real^2->bool) d e h.
     &0 < d /\ &0 < h /\ &10 * d + &2 * h <= e
     ==> !n (q:real^1->real^2).
           path q /\
           (!t. t IN interval[vec 0,vec 1] ==> cball(q t,e) SUBSET U) /\
           (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                  abs(drop s - drop t) <= inv(&2 pow n) ==> dist(q s,q t) <= h)
           ==> ?W. moi_lsp_walk (moi_lsp_grid d) W /\ ~(W = []) /\
                   HD W = moi_lsp_round d (q(vec 0)) /\
                   LAST W = moi_lsp_round d (q(vec 1)) /\
                   path_image(polygonal_path W) SUBSET U /\
                   homotopic_paths U (polygonal_path W)
                     (linepath(moi_lsp_round d (q(vec 0)),q(vec 0)) ++ q ++
                      linepath(q(vec 1),moi_lsp_round d (q(vec 1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q:real^1->real^2.
                  (!t. t IN interval[vec 0,vec 1] ==> cball(q t,e) SUBSET U)
                  ==> path_image q SUBSET U /\
                      segment[moi_lsp_round d (q(vec 0)),q(vec 0)] SUBSET U /\
                      segment[q(vec 1),moi_lsp_round d (q(vec 1))] SUBSET U`
  (LABEL_TAC "IMG") THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^1->real^2) t IN cball(q t,e)` MP_TAC THENL
       [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      MP_TAC(ISPECL [`d:real`; `e:real`; `U:real^2->bool`; `(q:real^1->real^2)(vec 0)`]
        MOI_LSP_ROUND_SEG) THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MP_TAC(ISPECL [`d:real`; `e:real`; `U:real^2->bool`; `(q:real^1->real^2)(vec 1)`]
        MOI_LSP_ROUND_SEG) THEN
      ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  INDUCT_TAC THEN X_GEN_TAC `q:real^1->real^2` THEN STRIP_TAC THENL
   [(* one piece: everything in the ball of radius e about q(vec 0) *)
    SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                      ==> dist((q:real^1->real^2)(vec 0),q t) <= h`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; real_pow; REAL_INV_1; DROP_VEC] THEN
      UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`d:real`; `(q:real^1->real^2)(vec 0)`] MOI_LSP_ROUND) THEN
    MP_TAC(SPECL [`d:real`; `(q:real^1->real^2)(vec 1)`] MOI_LSP_ROUND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`d:real`; `moi_lsp_round d ((q:real^1->real^2)(vec 0))`;
                  `moi_lsp_round d ((q:real^1->real^2)(vec 1))`] MOI_LSP_STAIR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:(real^2)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:(real^2)list` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `K = cball((q:real^1->real^2)(vec 0),e)` THEN
    SUBGOAL_THEN `K SUBSET (U:real^2->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(moi_lsp_round d ((q:real^1->real^2)(vec 1)) -
                       moi_lsp_round d (q(vec 0))) < &4 * d + h`
    ASSUME_TAC THENL
     [MP_TAC(SPEC `vec 1:real^1` (ASSUME `!t. t IN interval[vec 0,vec 1]
                      ==> dist((q:real^1->real^2)(vec 0),q t) <= h`)) THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      UNDISCH_TAC `dist(moi_lsp_round d ((q:real^1->real^2)(vec 0)),q(vec 0)) < &2 * d` THEN
      UNDISCH_TAC `dist(moi_lsp_round d ((q:real^1->real^2)(vec 1)),q(vec 1)) < &2 * d` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `path_image(polygonal_path W) SUBSET (K:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(moi_lsp_round d ((q:real^1->real^2)(vec 0)),
                        abs(moi_lsp_round d (q(vec 1))$1 - moi_lsp_round d (q(vec 0))$1) +
                        abs(moi_lsp_round d (q(vec 1))$2 - moi_lsp_round d (q(vec 0))$2))` THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^2` THEN
      DISCH_TAC THEN
      MP_TAC(ISPEC `moi_lsp_round d ((q:real^1->real^2)(vec 1)) -
                    moi_lsp_round d ((q:real^1->real^2)(vec 0))` MOI_LSP_NORM_L1) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(q:real^1->real^2)(vec 0)`; `moi_lsp_round d ((q:real^1->real^2)(vec 0))`;
                     `y:real^2`] DIST_TRIANGLE) THEN
      MP_TAC(ISPECL [`moi_lsp_round d ((q:real^1->real^2)(vec 0))`;
                     `(q:real^1->real^2)(vec 0)`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `pathstart (q:real^1->real^2) = q(vec 0) /\ pathfinish q = q(vec 1)`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[pathstart; pathfinish]; ALL_TAC] THEN
    SUBGOAL_THEN
     `dist((q:real^1->real^2)(vec 0),moi_lsp_round d (q(vec 0))) <= e /\
      dist((q:real^1->real^2)(vec 0),q(vec 0)) <= e /\
      dist((q:real^1->real^2)(vec 0),q(vec 1)) <= e /\
      dist((q:real^1->real^2)(vec 0),moi_lsp_round d (q(vec 1))) <= e`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `vec 1:real^1` (ASSUME `!t. t IN interval[vec 0,vec 1]
                      ==> dist((q:real^1->real^2)(vec 0),q t) <= h`)) THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
      UNDISCH_TAC `dist(moi_lsp_round d ((q:real^1->real^2)(vec 0)),q(vec 0)) < &2 * d` THEN
      UNDISCH_TAC `dist(moi_lsp_round d ((q:real^1->real^2)(vec 1)),q(vec 1)) < &2 * d` THEN
      UNDISCH_TAC `&10 * d + &2 * h <= e` THEN UNDISCH_TAC `&0 < d` THEN
      UNDISCH_TAC `&0 < h` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    ABBREV_TAC `P = linepath(moi_lsp_round d ((q:real^1->real^2)(vec 0)),q(vec 0)) ++ q ++
                    linepath(q(vec 1),moi_lsp_round d (q(vec 1)))` THEN
    SUBGOAL_THEN `path (P:real^1->real^2) /\ path_image P SUBSET K /\
                  pathstart P = moi_lsp_round d ((q:real^1->real^2)(vec 0)) /\
                  pathfinish P = moi_lsp_round d ((q:real^1->real^2)(vec 1))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN
      ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_LINEPATH;
                   PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                   UNION_SUBSET] THEN
      REPEAT CONJ_TAC THEN
      (MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN EXPAND_TAC "K" THEN
       ASM_REWRITE_TAC[CONVEX_CBALL; IN_CBALL] ORELSE
       (REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN
        DISCH_TAC THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN_CBALL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h:real` THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC));
      ALL_TAC] THEN
    MP_TAC(ISPEC `K:real^2->bool` SIMPLY_CONNECTED_EQ_HOMOTOPIC_PATHS) THEN
    SUBGOAL_THEN `simply_connected (K:real^2->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "K" THEN SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_CBALL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`polygonal_path (W:(real^2)list)`; `P:real^1->real^2`] o
      CONJUNCT2) THEN
    ASM_REWRITE_TAC[PATH_POLYGONAL_PATH; PATHSTART_POLYGONAL_PATH;
                    PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS];
      MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN EXISTS_TAC `K:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    (* two halves *)
    ABBREV_TAC `m = lift(&1 / &2)` THEN
    SUBGOAL_THEN `m IN interval[vec 0:real^1,vec 1] /\ drop m = &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real^1->real^2`; `vec 0:real^1`; `m:real^1`; `n:num`;
                   `\x:real^2. cball(x,e) SUBSET U`; `h:real`] MOI_LSP_SUBPATH_PROPS) THEN
    MP_TAC(ISPECL [`q:real^1->real^2`; `m:real^1`; `vec 1:real^1`; `n:num`;
                   `\x:real^2. cball(x,e) SUBSET U`; `h:real`] MOI_LSP_SUBPATH_PROPS) THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C2") (LABEL_TAC "M2")) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "M1")) THEN
    SUBGOAL_THEN `path_image (q:real^1->real^2) SUBSET U` ASSUME_TAC THENL
     [USE_THEN "IMG" (MP_TAC o SPEC `q:real^1->real^2`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!u v. u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
                        ==> path(subpath u v (q:real^1->real^2)) /\
                            path_image(subpath u v q) SUBSET U`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[PATH_SUBPATH] THEN
      ASM_MESON_TAC[PATH_IMAGE_SUBPATH_SUBSET; SUBSET_TRANS];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `subpath (vec 0) m (q:real^1->real^2)` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> is_const u &&
        fst(dest_const u) = "moi_lsp_walk")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "C1" (fun th -> REWRITE_TAC[BETA_RULE th]);
        USE_THEN "M1" ACCEPT_TAC];
      DISCH_THEN(X_CHOOSE_THEN `W1:(real^2)list` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(MP_TAC o SPEC `subpath m (vec 1) (q:real^1->real^2)` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> is_const u &&
        fst(dest_const u) = "moi_lsp_walk")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "C2" (fun th -> REWRITE_TAC[BETA_RULE th]);
        USE_THEN "M2" ACCEPT_TAC];
      DISCH_THEN(X_CHOOSE_THEN `W2:(real^2)list` STRIP_ASSUME_TAC)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[pathstart] PATHSTART_SUBPATH;
                                REWRITE_RULE[pathfinish] PATHFINISH_SUBPATH]) THEN
    MP_TAC(ISPECL [`W1:(real^2)list`; `W2:(real^2)list`] MOI_LSP_PP_APPEND) THEN
    MP_TAC(ISPECL [`moi_lsp_grid d`; `W1:(real^2)list`; `W2:(real^2)list`]
      MOI_LSP_WALK_APPEND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
    EXISTS_TAC `APPEND W1 (TL W2):(real^2)list` THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `polygonal_path W1 ++ polygonal_path (W2:(real^2)list)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_SUBSET THEN
      EXISTS_TAC `path_image(polygonal_path(APPEND W1 (TL W2):(real^2)list))` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[UNION_SUBSET]];
      ALL_TAC] THEN
    USE_THEN "IMG" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `q:real^1->real^2` th)
      (ASSUME `!t. t IN interval[vec 0,vec 1] ==> cball((q:real^1->real^2) t,e) SUBSET U`))) THEN
    MP_TAC(ISPECL [`d:real`; `e:real`; `U:real^2->bool`; `(q:real^1->real^2) m`]
      MOI_LSP_ROUND_SEG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(linepath(moi_lsp_round d ((q:real^1->real^2)(vec 0)),q(vec 0)) ++
                 subpath (vec 0) m q ++ linepath(q m,moi_lsp_round d (q m))) ++
                (reversepath(linepath(q m,moi_lsp_round d (q m))) ++
                 subpath m (vec 1) q ++ linepath(q(vec 1),moi_lsp_round d (q(vec 1))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
      ASM_REWRITE_TAC[REVERSEPATH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                      PATHFINISH_POLYGONAL_PATH];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `linepath(moi_lsp_round d ((q:real^1->real^2)(vec 0)),q(vec 0)) ++
                (subpath (vec 0) m q ++ subpath m (vec 1) q) ++
                linepath(q(vec 1),moi_lsp_round d (q(vec 1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LSP_TELE2 THEN
      ASM_SIMP_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                   PATHSTART_SUBPATH; PATHFINISH_SUBPATH; ENDS_IN_UNIT_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_LINEPATH; PATH_IMAGE_LINEPATH;
                    PATHSTART_JOIN; PATHFINISH_LINEPATH; PATHSTART_SUBPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
    ASM_REWRITE_TAC[HOMOTOPIC_PATHS_REFL; PATH_LINEPATH; PATH_IMAGE_LINEPATH;
                    PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_SUBPATH] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUBPATH_TRIVIAL] THEN
    MATCH_MP_TAC HOMOTOPIC_JOIN_SUBPATHS THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]]);;

(* B1: a loop in an open planar set is freely homotopic there to a closed grid walk. *)
let MOI_LSP_GRID_APPROX = prove
 (`!(U:real^2->bool) (p:real^1->real^2).
     open U /\ path p /\ pathfinish p = pathstart p /\ path_image p SUBSET U
     ==> ?d W. &0 < d /\ moi_lsp_walk (moi_lsp_grid d) W /\ ~(W = []) /\ HD W = LAST W /\
               path_image(polygonal_path W) SUBSET U /\
               homotopic_loops U p (polygonal_path W)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`path_image (p:real^1->real^2)`; `U:real^2->bool`] MOI_LSP_COMPACT_CBALL) THEN
  ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] ==> cball((p:real^1->real^2) t,e) SUBSET U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `interval[vec 0:real^1,vec 1]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[path; COMPACT_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`inv(&2)`; `k:real`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `e / &20`; `e:real`; `e / &4`] MOI_LSP_GRID_CORE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `p:real^1->real^2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIST_REAL; GSYM drop] THEN
    UNDISCH_TAC `inv (&2) pow n < k` THEN
    UNDISCH_TAC `abs(drop s - drop t) <= inv(&2 pow n)` THEN
    REWRITE_TAC[REAL_POW_INV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^2)list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e / &20`; `W:(real^2)list`] THEN
  SUBGOAL_THEN `(p:real^1->real^2)(vec 1) = p(vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(p:real^1->real^2)(vec 1) = p(vec 0)`]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
  MP_TAC(ISPECL [`e / &20`; `e:real`; `U:real^2->bool`; `(p:real^1->real^2)(vec 0)`]
    MOI_LSP_ROUND_SEG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `linepath(moi_lsp_round (e / &20) ((p:real^1->real^2)(vec 0)),p(vec 0)) ++ p ++
              reversepath(linepath(moi_lsp_round (e / &20) (p(vec 0)),p(vec 0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
    ASM_REWRITE_TAC[REVERSEPATH_LINEPATH; PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                    PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[pathstart]]);;

(* ------------------------------------------------------------------------- *)
(* B1 + B2 + B3 in the plane: a loop in an open set U inside a convex set C, *)
(* essential under g, gives a PL disk in C whose boundary loop lies in U    *)
(* and is essential under g.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_LSP_PLANAR_ESSENTIAL_DISK = prove
 (`!(U:real^2->bool) C (p:real^1->real^2) (g:real^2->real^M) v.
     open U /\ convex C /\ U SUBSET C /\
     path p /\ pathfinish p = pathstart p /\ path_image p SUBSET U /\
     g continuous_on U /\ IMAGE g U SUBSET v /\
     ~homotopic_loops v (g o p) (linepath(g(pathstart p),g(pathstart p)))
     ==> ?e e'. pl_homeomorphism (std_triangle,IMAGE e std_triangle) (e,e') /\
                IMAGE e std_triangle SUBSET C /\
                IMAGE e (relative_frontier std_triangle) SUBSET U /\
                ~homotopic_loops v (g o e o std_triangle_loop)
                                   (linepath(g(e(vec 0)),g(e(vec 0))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `p:real^1->real^2`] MOI_LSP_GRID_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:(real^2)list` STRIP_ASSUME_TAC)) THEN
  (* the grid walk is essential *)
  SUBGOAL_THEN `~homotopic_loops v ((g:real^2->real^M) o polygonal_path W)
                                   (linepath(g(HD W),g(HD W)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops v ((g:real^2->real^M) o p)
                                   (linepath(g(pathstart p),g(pathstart p)))` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `g:real^2->real^M`; `v:real^M->bool`;
                   `polygonal_path (W:(real^2)list)`; `p:real^1->real^2`;
                   `(g:real^2->real^M)(HD W)`] MOI_LTD_NULL_TRANSFER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[PATHSTART_COMPOSE]];
    ALL_TAC] THEN
  (* a simple closed sub-walk is essential *)
  SUBGOAL_THEN
   `?J. moi_lsp_walk (moi_lsp_grid d) J /\ HD J = LAST J /\ 4 <= LENGTH J /\
        PAIRWISE (\x y. ~(x = y)) (TL J) /\
        path_image(polygonal_path J) SUBSET U /\
        ~homotopic_loops v ((g:real^2->real^M) o polygonal_path J)
                           (linepath(g(HD J),g(HD J)))`
  STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_lsp_grid d`; `U:real^2->bool`; `g:real^2->real^M`;
                   `v:real^M->bool`] MOI_LSP_CLOSED_WALKS_NULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `J:(real^2)list` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `J:(real^2)list` o REWRITE_RULE[NOT_EXISTS_THM] o
        check (fun th -> is_neg(concl th) && is_exists(dest_neg(concl th)))) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `W:(real^2)list`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `J:(real^2)list`] MOI_LSP_GRID_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `polygonal_path (J:(real^2)list)` MOI_LSP_PL_LOOP_DISK) THEN
  ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->real^2` (X_CHOOSE_THEN `e':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real^2->real^2`; `e':real^2->real^2`] THEN
  SUBGOAL_THEN `IMAGE (e:real^2->real^2) std_triangle =
                path_image(polygonal_path J) UNION inside(path_image(polygonal_path J))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS];
      MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(J:(real^2)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `4 <= LENGTH (J:(real^2)list)` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^2->real^2)(vec 0) = HD J` ASSUME_TAC THENL
   [MP_TAC(SPEC `vec 0:real^1` (ASSUME `!t. t IN interval[vec 0,vec 1]
        ==> (e:real^2->real^2)(std_triangle_loop t) = polygonal_path J t`)) THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL;
                REWRITE_RULE[pathstart] (CONJUNCT1(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP))] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `J:(real^2)list` PATHSTART_POLYGONAL_PATH) THEN
    ASM_REWRITE_TAC[pathstart];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~homotopic_loops v ((g:real^2->real^M) o polygonal_path J)
                                 (linepath(g(HD J),g(HD J)))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(g:real^2->real^M) o e o std_triangle_loop` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
  MP_TAC(ISPECL [`g:real^2->real^M`; `U:real^2->bool`; `v:real^M->bool`;
                 `polygonal_path (J:(real^2)list)`] MOI_LTD_PATH_IMAGE_IN) THEN
  ASM_REWRITE_TAC[PATH_POLYGONAL_PATH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_POLYGONAL_PATH;
              PATHFINISH_POLYGONAL_PATH; o_THM] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B0 and the assembly of SPHERE_HOLE: a free boundary 2-simplex of b off   *)
(* UNIONS cb, the planar chart of the complementary disk, and the planar    *)
(* theorem MOI_LSP_PLANAR_ESSENTIAL_DISK.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LSP_SPHERE_SC = prove
 (`!b:real^N->bool. pl_sphere 2 b ==> simply_connected b`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `b:real^N->bool`]
    HOMEOMORPHIC_SIMPLY_CONNECTED) THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE_GEN THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

(* A boundary 2-simplex of b through a point off UNIONS cb meets UNIONS cb  *)
(* only in its relative frontier.                                            *)
let MOI_LSP_FREE_FACE = prove
 (`!(c:(real^N->bool)->bool) b cb x.
     combinatorial_manifold_with_boundary 3 c /\
     b IN components (complex_boundary c) /\ cb SUBSET c /\
     x IN b /\ ~(x IN UNIONS cb)
     ==> ?s. s IN c /\ &2 simplex s /\ x IN s /\ s SUBSET b /\
             relative_interior s INTER UNIONS cb = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_boundary] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 simplex (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    SUBGOAL_THEN `n:int = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED] THEN CONJ_TAC THENL
     [REWRITE_TAC[complex_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!s:real^N->bool u. s IN u ==> s SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(s INTER t:real^N->bool) face_of s` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `t:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = s` THENL
   [UNDISCH_TAC `~((x:real^N) IN UNIONS cb)` THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s INTER t:real^N->bool`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ASM_REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

(* The relative interior of b near a face off w misses the face. *)
let MOI_LSP_OFF_FACE = prove
 (`!(b:real^N->bool) s w.
     s SUBSET b /\ convex s /\ closed s /\ relative_interior s INTER w = {}
     ==> ((subtopology euclidean b) interior_of w) INTER s = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; interior_of; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "open_in")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(u INTER closure(relative_interior s:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

(* The planar chart of the disk complementary to a 2-simplex of a 2-sphere. *)
let MOI_LSP_CHART = prove
 (`!(b:real^N->bool) s.
     pl_sphere 2 b /\ &2 simplex s /\ s SUBSET b
     ==> ?f f'. pl_homeomorphism (std_triangle,(b DIFF s) UNION relative_frontier s) (f,f') /\
                IMAGE f (relative_frontier std_triangle) = relative_frontier s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `s:real^N->bool`; `relative_frontier s:real^N->bool`]
    MOI_FTC_DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
    ASM_REWRITE_TAC[IMAGE_ID; pl_homeomorphism; HOMEOMORPHISM_ID;
                    GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_MESON_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `relative_frontier s:real^N->bool`)) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`]
    MOI_SS2_TRI_TRANSFER) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_NONCOLLINEAR; GSYM std_triangle] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^N` (X_CHOOSE_THEN `h':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f:real^N->real^N) o (h:real^2->real^N)`;
                        `(h':real^N->real^2) o (g:real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

let SPHERE_HOLE = prove
 (MOI_LT_SPHERE_HOLE,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `b:real^N->bool`;
                       `cb:(real^N->bool)->bool`; `p:real^1->real^N`;
                       `g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `W0 = (subtopology euclidean b) interior_of (UNIONS cb:real^N->bool)` THEN
  SUBGOAL_THEN `W0 SUBSET UNIONS cb /\ W0 SUBSET (b:real^N->bool) /\
                open_in (subtopology euclidean b) W0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN REWRITE_TAC[INTERIOR_OF_SUBSET; OPEN_IN_INTERIOR_OF] THEN
    MP_TAC(ISPECL [`subtopology euclidean (b:real^N->bool)`; `UNIONS cb:real^N->bool`]
      INTERIOR_OF_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart (p:real^1->real^N) IN W0` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  (* UNIONS cb is not all of b, b being simply connected *)
  SUBGOAL_THEN `?x:real^N. x IN b /\ ~(x IN UNIONS cb)` STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS cb = b:real^N->bool` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~homotopic_loops v ((g:real^N->real^M) o p)
                    (linepath(g(pathstart p),g(pathstart p)))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `homotopic_loops b (p:real^1->real^N) (linepath(pathstart p,pathstart p))`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `b:real^N->bool` SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY) THEN
      ASM_SIMP_TAC[MOI_LSP_SPHERE_SC] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^1->real^N`;
                   `linepath(pathstart p:real^N,pathstart p)`; `g:real^N->real^M`;
                   `b:real^N->bool`; `v:real^M->bool`] HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[LINEPATH_REFL; o_DEF];
    ALL_TAC] THEN
  (* a free face off UNIONS cb, and the chart of its complement *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `cb:(real^N->bool)->bool`;
                 `x:real^N`] MOI_LSP_FREE_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `W0 INTER (sg:real^N->bool) = {}` ASSUME_TAC THENL
   [EXPAND_TAC "W0" THEN MATCH_MP_TAC MOI_LSP_OFF_FACE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `sg:real^N->bool`] MOI_LSP_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `f':real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `E = (b DIFF sg) UNION relative_frontier sg:real^N->bool` THEN
  SUBGOAL_THEN `relative_frontier sg SUBSET (sg:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `W0 SUBSET (E:real^N->bool) /\ E SUBSET b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN std_triangle ==> (f':real^N->real^2) (f y) = y) /\
    IMAGE (f:real^2->real^N) std_triangle = E /\
    (!z. z IN E ==> f (f' z) = z) /\ IMAGE f' E = std_triangle /\
    f continuous_on std_triangle /\ f' continuous_on E /\ pl_map_on std_triangle f`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `f':real^N->real^2`))
      (concl th) && can (find_term (fun u -> is_const u &&
        fst(dest_const u) = "pl_homeomorphism")) (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the planar open set *)
  SUBGOAL_THEN `interior std_triangle = std_triangle DIFF relative_frontier std_triangle`
  ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle; INTERIOR_OF_TRIANGLE] THEN
    REWRITE_TAC[GSYM std_triangle; MOI_LTD_STD_TRIANGLE_FRONTIER];
    ALL_TAC] THEN
  ABBREV_TAC `U = {y | y IN std_triangle /\ (f:real^2->real^N) y IN W0}` THEN
  SUBGOAL_THEN `U SUBSET std_triangle /\ IMAGE (f:real^2->real^N) U SUBSET W0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (U:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `interior std_triangle` THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `std_triangle` THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^2->real^N`; `std_triangle`; `E:real^N->bool`]
        CONTINUOUS_ON_OPEN_GEN) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(MP_TAC o SPEC `W0:real^N->bool`) THEN
      EXPAND_TAC "U" THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `y:real^2` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^2->real^N) y IN relative_frontier sg` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `relative_frontier sg:real^N->bool`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the planar loop and map *)
  ABBREV_TAC `q = (f':real^N->real^2) o (p:real^1->real^N)` THEN
  SUBGOAL_THEN `path (q:real^1->real^2) /\ pathfinish q = pathstart q /\
                path_image q SUBSET U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    REWRITE_TAC[ASSUME `pathfinish (p:real^1->real^N) = pathstart p`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `E:real^N->bool` THEN
      ASM SET_TAC[];
      EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN E` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `h = (g:real^N->real^M) o (f:real^2->real^N)` THEN
  SUBGOAL_THEN `(h:real^2->real^M) continuous_on U /\ IMAGE h U SUBSET v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS cb:real^N->bool` THEN
        ASM SET_TAC[]];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~homotopic_loops v ((h:real^2->real^M) o (q:real^1->real^2))
                  (linepath(h(pathstart q),h(pathstart q)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^2->real^M)(pathstart (q:real^1->real^2)) =
                  g(pathstart (p:real^1->real^N))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["h"; "q"] THEN REWRITE_TAC[PATHSTART_COMPOSE; o_THM] THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops v ((g:real^N->real^M) o p)
                    (linepath(g(pathstart p),g(pathstart p)))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(h:real^2->real^M) o (q:real^1->real^2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
    MP_TAC(ISPECL [`g:real^N->real^M`; `UNIONS cb:real^N->bool`; `v:real^M->bool`;
                   `p:real^1->real^N`] MOI_LTD_PATH_IMAGE_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["h"; "q"] THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(p:real^1->real^N) t IN path_image p` MP_TAC THENL
     [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the planar theorem *)
  MP_TAC(ISPECL [`U:real^2->bool`; `std_triangle`; `q:real^1->real^2`; `h:real^2->real^M`;
                 `v:real^M->bool`] MOI_LSP_PLANAR_ESSENTIAL_DISK) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^2->real^2` (X_CHOOSE_THEN `e':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (e:real^2->real^2)`;
                        `(e':real^2->real^2) o (f':real^N->real^2)`] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (e:real^2->real^2) std_triangle)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_MESON_TAC[pl_homeomorphism; MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (e:real^2->real^2) std_triangle` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`std_triangle`; `E:real^N->bool`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ASM SET_TAC[];
    ASM SET_TAC[];
    SUBGOAL_THEN
     `(g:real^N->real^M) o (f o e) o std_triangle_loop = h o e o std_triangle_loop /\
      (g:real^N->real^M)(((f:real^2->real^N) o (e:real^2->real^2))(vec 0)) = h(e(vec 0))`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[o_ASSOC; o_THM]]);;

