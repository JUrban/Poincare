(* ========================================================================= *)
(* pc_moi_loop_stmt4: the double-arc cut with a boundary buffer.            *)
(*   MOI_LT2_CUT_ARC_SPLIT (pc_moi_loop_stmt2.ml) is false as stated: the   *)
(*   boundary loop of the second new disk D_2 passes each end P0, Q of the  *)
(*   double arc twice, pairing adjacent rays of the two crossing branches,  *)
(*   so the two passages touch there; D_2 is locally injective, so its      *)
(*   boundary is the cyclically reduced loop of its class in the graph      *)
(*   f(Bd T) and it touches itself at P0, which no crossing2 chart allows   *)
(*   (DG pushes the new boundary off f(Bd T) inside a buffer of the         *)
(*   boundary surface).                                                     *)
(*   Here: an open buffer w of complex_boundary c containing f(Bd T).  The  *)
(*   terms MOI_LT4_CUT_ARC_SPLIT and MOI_LT4_CUT_ARC are the stmt2 terms     *)
(*   with the variable w added, the hypotheses open_in (subtopology         *)
(*   euclidean (complex_boundary c)) w and f(Bd T) SUBSET w added, and      *)
(*   every occurrence of f(Bd T) in the conclusion replaced by w (built     *)
(*   mechanically below and checked).  The descent induction gets the       *)
(*   hypothesis that w0 is open in the boundary; the descent itself takes   *)
(*   w0 = the boundary interior of b1, which is open, so                    *)
(*   LOOP_DESCENT_STATEMENT and LOOP_THEOREM_3_STATEMENT need no buffer.    *)
(*   Glue: MOI_LT4D_CUT_ARC, MOI_LT4D_DESCENT_INDUCT, MOI_LT4D_DESCENT      *)
(*   (copies of the stmt2 glue with the buffer), the statement list         *)
(*   MOI_LT4_UNIT_TARGETS (the stmt3 list with CUT_ARC_SPLIT replaced) and  *)
(*   the C25 closure MOI_LT4D_C25_CLOSURE.                                  *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt3.ml";;

prioritize_real();;
type_invention_error := true;;

(* The buffer transformation of a term !c f. H ==> C: add !w, the two       *)
(* buffer hypotheses, and replace f(Bd T) by w in C.                         *)

let moi_lt4_lf (f:term) =
  mk_comb(mk_comb(`IMAGE:(real^2->real^N)->(real^2->bool)->real^N->bool`, f),
          `relative_frontier std_triangle`);;

let moi_lt4_add_w tm =
  let vs,body = strip_forall tm in
  let c,f = match vs with [c;f] -> c,f | _ -> failwith "moi_lt4_add_w: vars" in
  let _ = if name_of c = "c" && name_of f = "f" then () else failwith "moi_lt4_add_w: names" in
  let w = mk_var("w",`:real^N->bool`) in
  let h,cn = dest_imp body in
  let lf = moi_lt4_lf f in
  let cn' = subst [w,lf] cn in
  let h1 = mk_comb(mk_comb(`open_in:(real^N)topology->(real^N->bool)->bool`,
                     mk_comb(mk_comb(`subtopology:(real^N)topology->(real^N->bool)->(real^N)topology`,
                                     `euclidean:(real^N)topology`),
                             mk_comb(`complex_boundary:((real^N->bool)->bool)->real^N->bool`, c))), w) in
  let h2 = mk_comb(mk_comb(`(SUBSET):(real^N->bool)->(real^N->bool)->bool`, lf), w) in
  list_mk_forall([c;f;w], mk_imp(list_mk_conj(conjuncts h @ [h1;h2]), cn'));;

let MOI_LT4_CUT_ARC_SPLIT = moi_lt4_add_w MOI_LT2_CUT_ARC_SPLIT;;
let MOI_LT4_CUT_ARC = moi_lt4_add_w MOI_LT2_CUT_ARC;;

(* Mechanical check of the buffer transformation: undoing the substitution   *)
(* and dropping the two buffer hypotheses gives the stmt2 terms back; w      *)
(* occurs in the conclusions and f(Bd T) does not.                           *)

let moi_lt4_change_ok old nw =
  let vs,b = strip_forall old and vs',b' = strip_forall nw in
  let h,cn = dest_imp b and h',cn' = dest_imp b' in
  let f = el 1 vs in
  let w = el 2 vs' in
  let lf = moi_lt4_lf f in
  length vs' = 3 && fst(chop_list 2 vs') = vs &&
  aconv (subst [lf,w] cn') cn && not (free_in lf cn') && vfree_in w cn' &&
  forall2 aconv (fst(chop_list (length (conjuncts h)) (conjuncts h'))) (conjuncts h) &&
  length (conjuncts h') = length (conjuncts h) + 2 &&
  type_of nw = bool_ty && frees nw = [];;

let moi_lt4_text_ok =
  moi_lt4_change_ok MOI_LT2_CUT_ARC_SPLIT MOI_LT4_CUT_ARC_SPLIT &&
  moi_lt4_change_ok MOI_LT2_CUT_ARC MOI_LT4_CUT_ARC;;

if not moi_lt4_text_ok then failwith "moi_lt4_text_ok";;

(* Sanity: the buffer hypotheses can always be met with w = the boundary.  *)

let MOI_LT4D_SAN_BUFFER = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_normal2_disk c f
     ==> open_in (subtopology euclidean (complex_boundary c)) (complex_boundary c) /\
         IMAGE f (relative_frontier std_triangle) SUBSET complex_boundary c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk; moi_lt_singular_disk] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The glue with the buffer: copies of MOI_LT2D_CUT_ARC,                     *)
(* MOI_LT2D_DESCENT_INDUCT and MOI_LT2D_DESCENT of pc_moi_loop_stmt2.ml,     *)
(* with f(Bd T) replaced by the buffer w as the space of the boundary        *)
(* homotopies.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LT4D_CUT_ARC = prove
 (mk_imp(list_mk_conj[MOI_LT4_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4],
         MOI_LT4_CUT_ARC),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SPLIT")
   (CONJUNCTS_THEN2 (LABEL_TAC "W3") (LABEL_TAC "W4"))) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`] THEN
  DISCH_TAC THEN
  REMOVE_THEN "SPLIT" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> DISCH_THEN(X_CHOOSE_THEN t MP_TAC))
   [`f1:real^2->real^N`; `f2:real^2->real^N`; `s1:real^1->real^N`;
    `s2:real^1->real^N`; `s3:real^1->real^N`; `s4:real^1->real^N`] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MAP_EVERY EXISTS_TAC [`f1:real^2->real^N`; `f2:real^2->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the boundary images of the cut disks lie in w *)
  SUBGOAL_THEN
   `!h:real^2->real^N q. homotopic_loops w (h o std_triangle_loop) q
                         ==> IMAGE h (relative_frontier std_triangle) SUBSET w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->real^M`; `v:real^M->bool`] THEN
  STRIP_TAC THEN
  (* paths pushed forward by g *)
  SUBGOAL_THEN
   `path ((g:real^N->real^M) o (s1:real^1->real^N)) /\ path (g o s2) /\
    path (g o s3) /\ path (g o s4) /\
    path_image (g o s1) SUBSET v /\ path_image (g o s2) SUBSET v /\
    path_image (g o s3) SUBSET v /\ path_image (g o s4) SUBSET v`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LTD_PATH_IMAGE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pathfinish ((g:real^N->real^M) o (s1:real^1->real^N)) = pathstart (g o s2) /\
    pathfinish (g o s2) = pathstart (g o s3) /\
    pathfinish (g o s3) = pathstart (g o s4) /\
    pathfinish (g o s4) = pathstart (g o s1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE]; ALL_TAC] THEN
  (* it suffices to kill the four-arc word *)
  SUBGOAL_THEN
   `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                       (g o s2) ++ (g o s3) ++ (g o s4))
                      (linepath(pathstart (g o s1),pathstart (g o s1)))`
  ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL
     [`w:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
      `(s1:real^1->real^N) ++ s2 ++ s3 ++ s4`;
      `(f:real^2->real^N) o std_triangle_loop`;
      `pathstart ((g:real^N->real^M) o (s1:real^1->real^N))`]
     MOI_LTD_NULL_TRANSFER) THEN
    ASM_REWRITE_TAC[PATH_COMPOSE_JOIN] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM]; ALL_TAC] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP]] THEN
  (* the two cases of the cut *)
  FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         reversepath (g o s3))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`w:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f1:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ reversepath s3`;
        `(g:real^N->real^M) ((f1:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH;
                      PATHSTART_JOIN];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         (g o s4) ++ (g o s3) ++ (g o s2))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`w:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f2:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ s4 ++ s3 ++ s2`;
        `(g:real^N->real^M) ((f2:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATHSTART_JOIN];
      ALL_TAC] THEN
    USE_THEN "W3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++ (g o s3))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`w:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f1:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ s3`;
        `(g:real^N->real^M) ((f1:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATHSTART_JOIN];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `homotopic_loops v (((g:real^N->real^M) o (s1:real^1->real^N)) ++
                         reversepath (g o s2) ++ (g o s3) ++ reversepath (g o s4))
                        (linepath(pathstart (g o s1),pathstart (g o s1)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`w:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f2:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ reversepath s2 ++ s3 ++ reversepath s4`;
        `(g:real^N->real^M) ((f2:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH;
                      PATHSTART_JOIN];
      ALL_TAC] THEN
    USE_THEN "W4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[]]);;

(* The descent induction with the buffer: w0 is open in the boundary, the  *)
(* double-arc case cuts with w = w0, so the new disks keep their boundary  *)
(* in w0 and the g-clause applies on w0 directly.                          *)

let MOI_LT4D_DESCENT_INDUCT = prove
 (mk_imp(mk_conj(MOI_LT2_CUT_CLOSED,MOI_LT4_CUT_ARC),
 `!(c:(real^N->bool)->bool) (b1:real^N->bool) (g:real^N->real^M) v w0.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     orientable_complex c /\ w0 SUBSET b1 /\
     open_in (subtopology euclidean (complex_boundary c)) w0 /\
     g continuous_on w0 /\ IMAGE g w0 SUBSET v
     ==> !n (h:real^2->real^N).
           moi_lt_normal2_disk c h /\ moi_lt_disk_complexity h = n /\
           IMAGE h (relative_frontier std_triangle) SUBSET w0 /\
           ~homotopic_loops v (g o h o std_triangle_loop)
                              (linepath(g(h(vec 0)),g(h(vec 0))))
           ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
                 pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
                 d INTER complex_boundary c =
                 IMAGE e (relative_frontier std_triangle) /\
                 IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
                 ~homotopic_loops v (g o e o std_triangle_loop)
                                    (linepath(g(e(vec 0)),g(e(vec 0))))`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CLOSED") (LABEL_TAC "ARC")) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `b1:real^N->bool`; `g:real^N->real^M`;
    `v:real^M->bool`; `w0:real^N->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN X_GEN_TAC `h:real^2->real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^2->real^N) continuous_on std_triangle /\
                moi_lt_singular_disk c h` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk] o CONJUNCT1 o
                GEN_REWRITE_RULE I [moi_lt_normal2_disk]) THEN
    SIMP_TAC[] THEN REWRITE_TAC[moi_lt_singular_disk] THEN
    MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_CASES_TAC `moi_lt_double_image (h:real^2->real^N) = {}` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^2->real^N`]
      MOI_LTD_EMBEDDED_DISK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (h:real^2->real^N) std_triangle`; `h:real^2->real^N`;
      `h':real^N->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN components (moi_lt_double_image h)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h1:real^2->real^N.
       moi_lt_normal2_disk c h1 /\
       moi_lt_disk_complexity h1 < moi_lt_disk_complexity (h:real^2->real^N) /\
       IMAGE h1 (relative_frontier std_triangle) SUBSET w0 /\
       ~homotopic_loops v ((g:real^N->real^M) o h1 o std_triangle_loop)
                          (linepath(g(h1(vec 0)),g(h1(vec 0))))
       ==> ?(d:real^N->bool) (e:real^2->real^N) e'.
             pl_homeomorphism (std_triangle,d) (e,e') /\ d SUBSET UNIONS c /\
             d INTER complex_boundary c =
             IMAGE e (relative_frontier std_triangle) /\
             IMAGE e (relative_frontier std_triangle) SUBSET b1 /\
             ~homotopic_loops v (g o e o std_triangle_loop)
                                (linepath(g(e(vec 0)),g(e(vec 0))))`
  (LABEL_TAC "IH1") THENL
   [X_GEN_TAC `h1:real^2->real^N` THEN STRIP_TAC THEN
    REMOVE_THEN "IH" (MP_TAC o SPEC `moi_lt_disk_complexity (h1:real^2->real^N)`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `h1:real^2->real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(k:real^N->bool) INTER complex_boundary c = {}` THENL
   [(* a closed double curve: Cases 1-2 *)
    USE_THEN "CLOSED" (MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `h:real^2->real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h1:real^2->real^N` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (h1:real^2->real^N) (relative_frontier std_triangle) =
                  IMAGE (h:real^2->real^N) (relative_frontier std_triangle)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LTD_IMAGE_EQ_RF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h1:real^2->real^N) (vec 0) = (h:real^2->real^N) (vec 0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `~homotopic_loops v ((g:real^N->real^M) o (h:real^2->real^N) o std_triangle_loop)
                         (linepath(g(h(vec 0)),g(h(vec 0))))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(g:real^N->real^M) o (h1:real^2->real^N) o std_triangle_loop` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC MOI_LTD_LOOP_EQ_RF THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w0:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^N->real^M) w0` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
    (* a double arc: Cases 3-4 *)
    USE_THEN "ARC" (MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `h:real^2->real^N`; `w0:real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^N`
     (X_CHOOSE_THEN `h2:real^2->real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g:real^N->real^M`; `v:real^M->bool`]) THEN
    REWRITE_TAC[IMP_CONJ] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC
     `homotopic_loops v ((g:real^N->real^M) o (h1:real^2->real^N) o
                          std_triangle_loop)
                         (linepath(g(h1(vec 0)),g(h1(vec 0))))` THENL
     [ASM_CASES_TAC
       `homotopic_loops v ((g:real^N->real^M) o (h2:real^2->real^N) o
                            std_triangle_loop)
                           (linepath(g(h2(vec 0)),g(h2(vec 0))))` THENL
       [ASM_MESON_TAC[];
        USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h2:real^2->real^N` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      USE_THEN "IH1" MATCH_MP_TAC THEN EXISTS_TAC `h1:real^2->real^N` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

(* The descent: w0 is the boundary interior of b1, open in the boundary (as  *)
(* in the stmt2 proof), so the induction applies.                            *)

let MOI_LT4D_DESCENT = prove
 (mk_imp(list_mk_conj[MOI_LT2_GENERAL_POSITION; MOI_LT2_CUT_CLOSED; MOI_LT4_CUT_ARC],
         `!(u:N->bool) (w:M->bool). LOOP_DESCENT_STATEMENT u w`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GP") (LABEL_TAC "CUTS")) THEN
  USE_THEN "CUTS" (LABEL_TAC "IND" o MATCH_MP MOI_LT4D_DESCENT_INDUCT) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOP_DESCENT_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `b1:real^N->bool`;
    `g:real^N->real^M`; `v:real^M->bool`] THEN
  ABBREV_TAC `w0 = (subtopology euclidean (complex_boundary c)) interior_of
                   (b1:real^N->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w0:real^N->bool) SUBSET b1 /\
                open_in (subtopology euclidean (complex_boundary c)) w0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[INTERIOR_OF_SUBSET; OPEN_IN_INTERIOR_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^M) continuous_on w0 /\ IMAGE g w0 SUBSET v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `b1:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "GP" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w0:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_lt_singular_disk]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^2->real^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "IND" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `b1:real^N->bool`; `g:real^N->real^M`;
    `v:real^M->bool`; `w0:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`moi_lt_disk_complexity (f':real^2->real^N)`; `f':real^2->real^N`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `~homotopic_loops v ((g:real^N->real^M) o f o std_triangle_loop)
                       (linepath(g(f(vec 0)),g(f(vec 0))))` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`w0:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
    `(f':real^2->real^N) o std_triangle_loop`;
    `(f:real^2->real^N) o std_triangle_loop`;
    `(g:real^N->real^M) ((f':real^2->real^N) (vec 0))`]
   MOI_LTD_NULL_TRANSFER) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM]);;


(* ------------------------------------------------------------------------- *)
(* The statement list MOI_LT4_UNIT_TARGETS (the stmt3 list with              *)
(* CUT_ARC_SPLIT replaced by the buffered term) and the C25 closure over it. *)
(* ------------------------------------------------------------------------- *)

let MOI_LT4_UNIT_TARGETS =
  map (fun t -> if t = MOI_LT2_CUT_ARC_SPLIT then MOI_LT4_CUT_ARC_SPLIT else t)
      MOI_LT3_UNIT_TARGETS;;

let MOI_LT4D_C25_CLOSURE =
  let ity = [`:7`,`:N`; `:7`,`:M`] in
  let hs = map (inst ity) (MOI_LT4_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
           [MOI_CORE_GLUE_LOOP3] in
  let hconj = list_mk_conj hs in
  let asm = CONJUNCTS (ASSUME hconj) in
  let _ = if length asm = length hs then () else failwith "conjunct count" in
  let get t = find (fun th -> aconv (concl th) (inst ity t)) asm in
  let conjs ts = end_itlist CONJ (map get ts) in
  let it th = INST_TYPE ity th in
  let inn = MP (it MOI_LT3D_CUT_INNERMOST)
               (conjs [MOI_LT3_INNERMOST_FROM_EXCL; MOI_LT3_CASE1_FROM_ORIENT;
                       MOI_LT_ORIENT_SIGN]) in
  let swp = MP (it MOI_LT3D_CUT_SWAP)
               (conjs [MOI_LT3_SWAP_FROM_CAP; MOI_LT3_CLEAN_CAP]) in
  let gp = MP (it MOI_LT2D_GP)
              (conjs [MOI_LT_GP_SIMPLICIAL; MOI_LT2_GP_CROSSINGS;
                      MOI_LT2_CROSSINGS_NORMAL]) in
  let ca = MP (it MOI_LT4D_CUT_ARC)
              (conjs [MOI_LT4_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4]) in
  let cc = MP (it MOI_LT2D_CUT_CLOSED) (CONJ inn swp) in
  let ld = MP (it MOI_LT4D_DESCENT) (CONJ gp (CONJ cc ca)) in
  let lsc = MP (it MOI_LTD_SPHERE)
               (conjs [MOI_LT_SPHERE_HOLE; MOI_LT_PUSH_IN_DISK]) in
  let dc = MP (INST_TYPE [`:7`,`:N`] MOI_FD_DOUBLE_COVER_GLUE)
              (conjs [MOI_FND_COCYCLE_NONSPHERE_BOUNDARY;
                      MOI_FND_DOUBLE_COVER_OF_COCYCLE; MOI_FND_CM_WB_DIM]) in
  let prod = MP (it MOI_LTD_PROD_LOOP_NS)
                (conjs [MOI_LT_COVER_LIFT_CELLWISE; MOI_LT_COVER_BOUNDARY;
                        MOI_LT_NO_SECTION; MOI_LT_COMPLEXITY_LIFT;
                        MOI_LT_CELLWISE_FINITE; MOI_LT_NEXT_SYSTEM;
                        MOI_LT_SPHERE_STEP; MOI_LT_DESCENT_INPUT;
                        MOI_LT_FROZEN_TO_CELL]) in
  let u7 = `(:7)` in
  let lns = MP (SPECL [u7; u7] prod)
               (CONJ (SPECL [u7; u7] lsc) (CONJ dc (SPECL [u7; u7] ld))) in
  let loopn = MP (it MOI_LTD_LOOPN)
                 (conjs [MOI_LT_FILL; MOI_LT_NSYS; MOI_FND_BARYCENTRIC_CM_WB]) in
  let ltn = MP (SPEC u7 loopn) lns in
  let lt3 = MP (last asm) ltn in
  DISCH hconj lt3;;

(* Checks: the list differs from the stmt3 list in exactly the one entry; no *)
(* further term (the foundation terms and MOI_CORE_GLUE_LOOP3 are those of   *)
(* the other C25 closures); all glue without hypotheses; the closure         *)
(* concludes LOOP_THEOREM_3_STATEMENT from exactly the listed hypotheses.    *)

let moi_lt4_check =
  moi_lt4_text_ok &&
  length MOI_LT4_UNIT_TARGETS = length MOI_LT3_UNIT_TARGETS &&
  length (filter (fun (a,b) -> not (a = b))
                 (zip MOI_LT3_UNIT_TARGETS MOI_LT4_UNIT_TARGETS)) = 1 &&
  mem MOI_LT4_CUT_ARC_SPLIT MOI_LT4_UNIT_TARGETS &&
  not (mem MOI_LT2_CUT_ARC_SPLIT MOI_LT4_UNIT_TARGETS) &&
  forall (fun th -> hyp th = [])
         [MOI_LT4D_SAN_BUFFER; MOI_LT4D_CUT_ARC; MOI_LT4D_DESCENT_INDUCT;
          MOI_LT4D_DESCENT; MOI_LT4D_C25_CLOSURE] &&
  aconv (concl MOI_LT4D_C25_CLOSURE)
        (mk_imp(list_mk_conj(map (inst [`:7`,`:N`; `:7`,`:M`])
                  (MOI_LT4_UNIT_TARGETS @ MOI_LT_FND_TERMS) @ [MOI_CORE_GLUE_LOOP3]),
                `LOOP_THEOREM_3_STATEMENT`)) &&
  aconv (rand (concl MOI_LT4D_DESCENT)) (rand (concl MOI_LT2D_DESCENT));;

if not moi_lt4_check then failwith "moi_lt4_check";;

Printf.printf "LT4 %b %d\n%!" moi_lt4_check (length MOI_LT4_UNIT_TARGETS);;

