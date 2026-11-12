(* ========================================================================= *)
(* pc_moi_loop_stmt2: the C25 double-curve notions with genuine crossings.   *)
(* In moi_lt_crossing_at (pc_moi_loop_stmt.ml D5) the two sheets n1, n2 of   *)
(* the chart preimage need not be open, so a touching double curve (each     *)
(* source disk mapped onto the boundary of a quadrant, half of z1 = 0 plus   *)
(* half of z2 = 0) also counts as a crossing. A touching closed double curve *)
(* whose preimage is one polygon has monodromy a rotation by pi, so          *)
(* orientability does not exclude Case 1 of Moise p.185, and                 *)
(* MOI_LT_CUT_INNERMOST is false (c = RP^3 minus a ball, two projective      *)
(* planes meeting in a line). Here moi_lt_crossing2_at adds that n1 and n2   *)
(* are open in the preimage of the chart domain, which excludes touching;    *)
(* moi_lt_normal2_disk is a normal disk with such crossings everywhere. The  *)
(* statement terms mentioning the two notions are restated (MOI_LT2_..., by  *)
(* substituting the constants), with bridges where the term of               *)
(* pc_moi_loop_stmt.ml implies the restated one, and the glue of             *)
(* pc_moi_loop_stmt.ml (sections G2, G3, the descent and the closure) is     *)
(* repeated for them (MOI_LT2D_..., copies of the MOI_LTD_ proofs).          *)
(* Why GP_CROSSINGS_2 is the right producer statement: general position    *)
(* of a PL disk in a 3-manifold (Moise p.184) gives transverse double       *)
(* curves; at a double point y the two preimages x1, x2 have disjoint open  *)
(* neighbourhoods, each mapped injectively onto one of two PL sheets that  *)
(* cross like the planes z1 = 0 and z2 = 0 of a chart, so n1 and n2 can be *)
(* taken as the parts of the chart preimage in those two neighbourhoods:   *)
(* open in the preimage.  This is the book's transversality; touching      *)
(* sheets never arise from the perturbation.                                *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_lt_crossing2_at = new_definition
 `moi_lt_crossing2_at (c:(real^N->bool)->bool) (f:real^2->real^N) (y:real^N) <=>
    ?u (h:real^N->real^3) h' n1 n2.
       open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
       pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
       ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
         IMAGE h u = ball(vec 0,&1)) \/
        (y IN complex_boundary c /\
         IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
         IMAGE h (u INTER complex_boundary c) =
         IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
       {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
       IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
       IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
       IMAGE h (moi_lt_double_image f INTER u) =
       IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
       open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
       open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2`;;

let moi_lt_normal2_disk = new_definition
 `moi_lt_normal2_disk (c:(real^N->bool)->bool) (f:real^2->real^N) <=>
    moi_lt_normal_disk c f /\
    (!y. y IN moi_lt_double_image f ==> moi_lt_crossing2_at c f y)`;;

let MOI_LT2D_CROSSING2_IMP = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y.
     moi_lt_crossing2_at c f y ==> moi_lt_crossing_at c f y`,
  REWRITE_TAC[moi_lt_crossing2_at; moi_lt_crossing_at] THEN MESON_TAC[]);;

let MOI_LT2D_NORMAL2_IMP = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_normal2_disk c f ==> moi_lt_normal_disk c f`,
  SIMP_TAC[moi_lt_normal2_disk]);;

let MOI_LT2D_NORMAL2_FINITE = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_normal2_disk c f ==> FINITE (components (moi_lt_double_image f))`,
  MESON_TAC[MOI_LT2D_NORMAL2_IMP; MOI_LTD_NORMAL_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* The restated terms: every statement term of pc_moi_loop_stmt.ml that      *)
(* mentions moi_lt_normal_disk or moi_lt_crossing_at, with the two constants *)
(* replaced by moi_lt_normal2_disk and moi_lt_crossing2_at (nothing else     *)
(* differs).                                                                 *)
(* ------------------------------------------------------------------------- *)

let moi_lt2_subst tm =
  subst [`moi_lt_normal2_disk:((real^N->bool)->bool)->(real^2->real^N)->bool`,
         `moi_lt_normal_disk:((real^N->bool)->bool)->(real^2->real^N)->bool`;
         `moi_lt_crossing2_at:((real^N->bool)->bool)->(real^2->real^N)->real^N->bool`,
         `moi_lt_crossing_at:((real^N->bool)->bool)->(real^2->real^N)->real^N->bool`] tm;;

let MOI_LT2_GP_CROSSINGS = moi_lt2_subst MOI_LT_GP_CROSSINGS;;
let MOI_LT2_CROSSINGS_NORMAL = moi_lt2_subst MOI_LT_CROSSINGS_NORMAL;;
let MOI_LT2_GENERAL_POSITION = moi_lt2_subst MOI_LT_GENERAL_POSITION;;
let MOI_LT2_CUT_CLOSED = moi_lt2_subst MOI_LT_CUT_CLOSED;;
let MOI_LT2_CUT_INNERMOST = moi_lt2_subst MOI_LT_CUT_INNERMOST;;
let MOI_LT2_CUT_SWAP = moi_lt2_subst MOI_LT_CUT_SWAP;;
let MOI_LT2_CUT_ARC_SPLIT = moi_lt2_subst MOI_LT_CUT_ARC_SPLIT;;
let MOI_LT2_CUT_ARC = moi_lt2_subst MOI_LT_CUT_ARC;;
let MOI_LT2_SOURCE_STRUCTURE = moi_lt2_subst MOI_LT_SOURCE_STRUCTURE;;

(* Text check: each restated term differs from the term of                   *)
(* pc_moi_loop_stmt.ml, contains neither of the two constants, and gives     *)
(* that term back under the inverse substitution.                            *)

let moi_lt2_pairs =
  [MOI_LT_GP_CROSSINGS,MOI_LT2_GP_CROSSINGS; MOI_LT_CROSSINGS_NORMAL,MOI_LT2_CROSSINGS_NORMAL;
   MOI_LT_GENERAL_POSITION,MOI_LT2_GENERAL_POSITION; MOI_LT_CUT_CLOSED,MOI_LT2_CUT_CLOSED;
   MOI_LT_CUT_INNERMOST,MOI_LT2_CUT_INNERMOST; MOI_LT_CUT_SWAP,MOI_LT2_CUT_SWAP;
   MOI_LT_CUT_ARC_SPLIT,MOI_LT2_CUT_ARC_SPLIT; MOI_LT_CUT_ARC,MOI_LT2_CUT_ARC;
   MOI_LT_SOURCE_STRUCTURE,MOI_LT2_SOURCE_STRUCTURE];;

let moi_lt2_unsubst tm =
  subst [`moi_lt_normal_disk:((real^N->bool)->bool)->(real^2->real^N)->bool`,
         `moi_lt_normal2_disk:((real^N->bool)->bool)->(real^2->real^N)->bool`;
         `moi_lt_crossing_at:((real^N->bool)->bool)->(real^2->real^N)->real^N->bool`,
         `moi_lt_crossing2_at:((real^N->bool)->bool)->(real^2->real^N)->real^N->bool`] tm;;

let moi_lt2_old_consts =
  [`moi_lt_normal_disk:((real^N->bool)->bool)->(real^2->real^N)->bool`;
   `moi_lt_crossing_at:((real^N->bool)->bool)->(real^2->real^N)->real^N->bool`];;

let moi_lt2_text_ok =
  forall (fun (t0,t1) ->
            not (aconv t0 t1) && aconv (moi_lt2_unsubst t1) t0 &&
            type_of t1 = bool_ty && frees t1 = [] &&
            not (exists (fun k -> can (find_term ((=) k)) t1) moi_lt2_old_consts))
         moi_lt2_pairs;;

if not moi_lt2_text_ok then failwith "moi_lt2_text_ok";;

(* Bridges: SOURCE_STRUCTURE and CROSSINGS_NORMAL of pc_moi_loop_stmt.ml     *)
(* imply the restated terms.                                                *)

let MOI_LT2D_SOURCE_BRIDGE = prove
 (mk_imp(MOI_LT_SOURCE_STRUCTURE,MOI_LT2_SOURCE_STRUCTURE),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_LT2D_NORMAL2_IMP]);;

let MOI_LT2D_CROSSINGS_NORMAL_BRIDGE = prove
 (mk_imp(MOI_LT_CROSSINGS_NORMAL,MOI_LT2_CROSSINGS_NORMAL),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_lt_normal2_disk] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MOI_LT2D_CROSSING2_IMP]);;

(* ------------------------------------------------------------------------- *)
(* The glue for the crossing2 notions: copies of MOI_LTD_GP,                 *)
(* MOI_LTD_CUT_ARC, MOI_LTD_DESCENT_INDUCT, MOI_LTD_DESCENT and              *)
(* MOI_LTD_CUT_CLOSED of pc_moi_loop_stmt.ml with the restated terms (one    *)
(* unfolding step goes through moi_lt_normal2_disk first).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LT2D_GP = prove
 (mk_imp(list_mk_conj[MOI_LT_GP_SIMPLICIAL; MOI_LT2_GP_CROSSINGS;
                      MOI_LT2_CROSSINGS_NORMAL],
         MOI_LT2_GENERAL_POSITION),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SIMP")
   (CONJUNCTS_THEN2 (LABEL_TAC "CROSS") (LABEL_TAC "NORM"))) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "SIMP" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool`
   (X_CHOOSE_THEN `k:(real^2->bool)->bool` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "CROSS" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
    `k:(real^2->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^2->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "NORM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_LT2D_CUT_ARC = prove
 (mk_imp(list_mk_conj[MOI_LT2_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4],
         MOI_LT2_CUT_ARC),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SPLIT")
   (CONJUNCTS_THEN2 (LABEL_TAC "W3") (LABEL_TAC "W4"))) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  DISCH_TAC THEN
  REMOVE_THEN "SPLIT" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> DISCH_THEN(X_CHOOSE_THEN t MP_TAC))
   [`f1:real^2->real^N`; `f2:real^2->real^N`; `s1:real^1->real^N`;
    `s2:real^1->real^N`; `s3:real^1->real^N`; `s4:real^1->real^N`] THEN
  ABBREV_TAC `l = IMAGE (f:real^2->real^N) (relative_frontier std_triangle)` THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN MAP_EVERY EXISTS_TAC [`f1:real^2->real^N`; `f2:real^2->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the boundary images of the cut disks lie in l *)
  SUBGOAL_THEN
   `!h:real^2->real^N q. homotopic_loops l (h o std_triangle_loop) q
                         ==> IMAGE h (relative_frontier std_triangle) SUBSET l`
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
     [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
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
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
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
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
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
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
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
       [`l:real^N->bool`; `g:real^N->real^M`; `v:real^M->bool`;
        `(f2:real^2->real^N) o std_triangle_loop`;
        `(s1:real^1->real^N) ++ reversepath s2 ++ s3 ++ reversepath s4`;
        `(g:real^N->real^M) ((f2:real^2->real^N) (vec 0))`]
       MOI_LTD_NULL_TRANSFER) THEN
      ASM_REWRITE_TAC[PATH_COMPOSE_JOIN; PATH_COMPOSE_REVERSEPATH;
                      PATHSTART_JOIN];
      ALL_TAC] THEN
    USE_THEN "W4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_MESON_TAC[]]);;

let MOI_LT2D_DESCENT_INDUCT = prove
 (mk_imp(mk_conj(MOI_LT2_CUT_CLOSED,MOI_LT2_CUT_ARC),
 `!(c:(real^N->bool)->bool) (b1:real^N->bool) (g:real^N->real^M) v w0.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     orientable_complex c /\ w0 SUBSET b1 /\
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
     [`c:(real^N->bool)->bool`; `h:real^2->real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^N`
     (X_CHOOSE_THEN `h2:real^2->real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g:real^N->real^M`; `v:real^M->bool`]) THEN
    REWRITE_TAC[IMP_CONJ] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^N->real^M) w0` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      ALL_TAC] THEN
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

let MOI_LT2D_DESCENT = prove
 (mk_imp(list_mk_conj[MOI_LT2_GENERAL_POSITION; MOI_LT2_CUT_CLOSED; MOI_LT2_CUT_ARC],
         `!(u:N->bool) (w:M->bool). LOOP_DESCENT_STATEMENT u w`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GP") (LABEL_TAC "CUTS")) THEN
  USE_THEN "CUTS" (LABEL_TAC "IND" o MATCH_MP MOI_LT2D_DESCENT_INDUCT) THEN
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

let MOI_LT2D_CUT_CLOSED = prove
 (mk_imp(mk_conj(MOI_LT2_CUT_INNERMOST,MOI_LT2_CUT_SWAP), MOI_LT2_CUT_CLOSED),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IN") (LABEL_TAC "SW")) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "IN" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':real^N->bool` (X_CHOOSE_THEN `j1:real^2->bool`
    (X_CHOOSE_THEN `j2:real^2->bool` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "SW" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k':real^N->bool`;
    `j1:real^2->bool`; `j2:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The C25 closure with the restated terms: MOI_LT2_UNIT_TARGETS is          *)
(* MOI_LT_UNIT_TARGETS with CUT_INNERMOST, CUT_SWAP, CUT_ARC_SPLIT and       *)
(* GP_CROSSINGS, CROSSINGS_NORMAL replaced (a copy of MOI_LTD_C25_CLOSURE).  *)
(* ------------------------------------------------------------------------- *)

let moi_lt2_target_map =
  [MOI_LT_GP_CROSSINGS,MOI_LT2_GP_CROSSINGS; MOI_LT_CROSSINGS_NORMAL,MOI_LT2_CROSSINGS_NORMAL;
   MOI_LT_CUT_INNERMOST,MOI_LT2_CUT_INNERMOST; MOI_LT_CUT_SWAP,MOI_LT2_CUT_SWAP;
   MOI_LT_CUT_ARC_SPLIT,MOI_LT2_CUT_ARC_SPLIT];;

let MOI_LT2_UNIT_TARGETS =
  map (fun t -> try assoc t moi_lt2_target_map with Failure _ -> t) MOI_LT_UNIT_TARGETS;;

let moi_lt2_targets_ok =
  length MOI_LT2_UNIT_TARGETS = length MOI_LT_UNIT_TARGETS &&
  length (filter (fun (a,b) -> not (a = b)) (zip MOI_LT_UNIT_TARGETS MOI_LT2_UNIT_TARGETS)) = 5 &&
  forall (fun t -> mem t MOI_LT2_UNIT_TARGETS) (map snd moi_lt2_target_map);;

if not moi_lt2_targets_ok then failwith "moi_lt2_targets_ok";;

let MOI_LT2D_C25_CLOSURE =
  let ity = [`:7`,`:N`; `:7`,`:M`] in
  let hs = map (inst ity) (MOI_LT2_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
           [MOI_CORE_GLUE_LOOP3] in
  let hconj = list_mk_conj hs in
  let asm = CONJUNCTS (ASSUME hconj) in
  let _ = if length asm = length hs then () else failwith "conjunct count" in
  let get t = el (index (inst ity t) (map (inst ity)
                 (MOI_LT2_UNIT_TARGETS @ MOI_LT_FND_TERMS))) asm in
  let conjs ts = end_itlist CONJ (map get ts) in
  let it th = INST_TYPE ity th in
  let gp = MP (it MOI_LT2D_GP)
              (conjs [MOI_LT_GP_SIMPLICIAL; MOI_LT2_GP_CROSSINGS;
                      MOI_LT2_CROSSINGS_NORMAL]) in
  let ca = MP (it MOI_LT2D_CUT_ARC)
              (conjs [MOI_LT2_CUT_ARC_SPLIT; MOI_LT_WORD_3; MOI_LT_WORD_4]) in
  let cc = MP (it MOI_LT2D_CUT_CLOSED)
              (conjs [MOI_LT2_CUT_INNERMOST; MOI_LT2_CUT_SWAP]) in
  let ld = MP (it MOI_LT2D_DESCENT) (CONJ gp (CONJ cc ca)) in
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

(* The statement of the closure, for the record. *)
let MOI_LT2D_C25_CLOSURE_HYPS = length (hyp MOI_LT2D_C25_CLOSURE);;
concl MOI_LT2D_C25_CLOSURE = mk_imp(list_mk_conj(map (inst [`:7`,`:N`; `:7`,`:M`])
  (MOI_LT2_UNIT_TARGETS @ MOI_LT_FND_TERMS) @ [MOI_CORE_GLUE_LOOP3]),
  `LOOP_THEOREM_3_STATEMENT`);;

(* Sanity: embedded proper disks are normal2 disks of complexity 0.         *)

let MOI_LT2D_SAN_NORMAL_EMBEDDED = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N).
     moi_lt_singular_disk c f /\
     (!x y. x IN std_triangle /\ y IN std_triangle /\ f x = f y ==> x = y)
     ==> moi_lt_normal2_disk c f /\ moi_lt_disk_complexity f = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`]
               MOI_LTD_SAN_NORMAL_EMBEDDED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[moi_lt_normal2_disk] THEN
  SUBGOAL_THEN `moi_lt_double_image (f:real^2->real^N) = {}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MOI_LTD_SAN_DOUBLE_IMAGE_EMPTY]; REWRITE_TAC[NOT_IN_EMPTY]]);;

(* Final checks.                                                            *)

let moi_lt2_check =
  aconv (concl MOI_LT2D_C25_CLOSURE)
        (mk_imp(list_mk_conj(map (inst [`:7`,`:N`; `:7`,`:M`])
           (MOI_LT2_UNIT_TARGETS @ MOI_LT_FND_TERMS) @ [MOI_CORE_GLUE_LOOP3]),
         `LOOP_THEOREM_3_STATEMENT`)) &&
  hyp MOI_LT2D_C25_CLOSURE = [] && hyp MOI_LT2D_GP = [] && hyp MOI_LT2D_CUT_ARC = [] &&
  hyp MOI_LT2D_DESCENT = [] && hyp MOI_LT2D_CUT_CLOSED = [] &&
  hyp MOI_LT2D_SOURCE_BRIDGE = [] && hyp MOI_LT2D_CROSSINGS_NORMAL_BRIDGE = [] &&
  moi_lt2_text_ok && moi_lt2_targets_ok;;

Printf.printf "LT2 %b\n%!" moi_lt2_check;;

