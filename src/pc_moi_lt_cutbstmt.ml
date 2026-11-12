(* ========================================================================= *)
(* pc_moi_lt_cutbstmt: the two statements into which the arc case of the cut *)
(* step of the loop theorem (Moise GTM 47 p.185-187 Cases 3-4) is split;     *)
(* together they give MOI_LT4_CUT_ARC_SPLIT (pc_moi_loop_stmt4.ml).          *)
(*   moi_lcus_mr: the model rectangle [0,3] x [0,1]; the chords x = 1 and   *)
(*   x = 2 cut it into R1 (left), R0 (middle) and R2 (right).               *)
(*   moi_lcus_as, _at, _au, _av: the four arcs of its boundary between the  *)
(*   chord ends, counterclockwise from (1,1): A_s = (1,1) (0,1) (0,0) (1,0),*)
(*   A_t = (1,0) (2,0), A_u = (2,0) (3,0) (3,1) (2,1), A_v = (2,1) (1,1).    *)
(*   moi_lcus_model c f g e: g is a PL homeomorphism of the model onto the  *)
(*   source triangle, boundary onto boundary, carrying the two chords onto  *)
(*   the source of a double component k of f that meets the boundary of c, *)
(*   and e tells how f identifies the chords: Case 3 (e) f(g(1,t)) =       *)
(*   f(g(2,1-t)), Case 4 (not e) f(g(1,t)) = f(g(2,t)).                     *)
(*   MOI_LCUS_SEAM (pc_moi_lt_seam.ml): the disk D_2 = R1 + R0 + R2 reglued *)
(*   crosswise, with the touching seam along k pushed apart inside the     *)
(*   buffer w: a normal2 disk of smaller complexity whose boundary loop is  *)
(*   homotopic in w to the D_2 word (Case 3: s1 s4 s3 s2; Case 4:           *)
(*   s1 s2^-1 s3 s4^-1, with s1..s4 the images of A_s, A_t, A_u, A_v).      *)
(*   MOI_LCUS_ARC_FROM_SEAM (pc_moi_lt_cutb.ml): MOI_LCUS_SEAM ==>          *)
(*   MOI_LT4_CUT_ARC_SPLIT (source arcs, the model g, D_1 = R1 + R2 with no *)
(*   change in c, the paths s1..s4 and the words).                          *)
(* Sanity: the arc ends (MOI_LCUS_SAN_ENDS), the two words are loops under  *)
(* the model relation (MOI_LCUS_SAN_WORDS), and a mechanical check that the *)
(* two words are the f2 words of the two disjuncts of MOI_LT4_CUT_ARC_SPLIT *)
(* after s1..s4 are replaced by the arc images (moi_lcus_words_ok).          *)
(* Glue: MOI_LCUSD_CUT_ARC_SPLIT.                                            *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt4.ml";;

prioritize_real();;
type_invention_error := true;;

let moi_lcus_mr = new_definition
 `moi_lcus_mr = interval[vec 0:real^2,vector[&3; &1]]`;;

let moi_lcus_as = new_definition
 `moi_lcus_as = linepath(vector[&1; &1]:real^2,vector[&0; &1]) ++
                linepath(vector[&0; &1],vector[&0; &0]) ++
                linepath(vector[&0; &0],vector[&1; &0])`;;

let moi_lcus_at = new_definition
 `moi_lcus_at = linepath(vector[&1; &0]:real^2,vector[&2; &0])`;;

let moi_lcus_au = new_definition
 `moi_lcus_au = linepath(vector[&2; &0]:real^2,vector[&3; &0]) ++
                linepath(vector[&3; &0],vector[&3; &1]) ++
                linepath(vector[&3; &1],vector[&2; &1])`;;

let moi_lcus_av = new_definition
 `moi_lcus_av = linepath(vector[&2; &1]:real^2,vector[&1; &1])`;;

let moi_lcus_model = new_definition
 `moi_lcus_model (c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) (e:bool) <=>
    (?g'. pl_homeomorphism (moi_lcus_mr,std_triangle) (g,g')) /\
    IMAGE g (relative_frontier moi_lcus_mr) = relative_frontier std_triangle /\
    (?k. k IN components (moi_lt_double_image f) /\
         ~(k INTER complex_boundary c = {}) /\
         {x | x IN std_triangle /\ f x IN k} =
         IMAGE g (segment[vector[&1; &0],vector[&1; &1]] UNION
                  segment[vector[&2; &0],vector[&2; &1]])) /\
    (!t. &0 <= t /\ t <= &1
         ==> f (g (vector[&1; t])) = f (g (vector[&2; if e then &1 - t else t])))`;;

let MOI_LCUS_SEAM =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) w (g:real^2->real^2) e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal2_disk c f /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w /\
     moi_lcus_model c f g e
     ==> ?f2. moi_lt_normal2_disk c f2 /\
              moi_lt_disk_complexity f2 < moi_lt_disk_complexity f /\
              homotopic_loops w (f2 o std_triangle_loop)
               (if e then (f o g o moi_lcus_as) ++ (f o g o moi_lcus_av) ++
                          (f o g o moi_lcus_au) ++ (f o g o moi_lcus_at)
                else (f o g o moi_lcus_as) ++ reversepath (f o g o moi_lcus_at) ++
                     (f o g o moi_lcus_au) ++ reversepath (f o g o moi_lcus_av))`;;

let MOI_LCUS_ARC_FROM_SEAM = mk_imp(MOI_LCUS_SEAM,MOI_LT4_CUT_ARC_SPLIT);;

let MOI_LCUS_UNIT_TARGETS = [MOI_LCUS_ARC_FROM_SEAM; MOI_LCUS_SEAM];;

if not (forall (fun t -> type_of t = bool_ty && frees t = []) MOI_LCUS_UNIT_TARGETS)
then failwith "MOI_LCUS_UNIT_TARGETS: not closed booleans";;

(* Sanity: the ends of the four model arcs. *)

let MOI_LCUS_SAN_ENDS = prove
 (`pathstart moi_lcus_as = vector[&1; &1]:real^2 /\ pathfinish moi_lcus_as = vector[&1; &0] /\
   pathstart moi_lcus_at = vector[&1; &0]:real^2 /\ pathfinish moi_lcus_at = vector[&2; &0] /\
   pathstart moi_lcus_au = vector[&2; &0]:real^2 /\ pathfinish moi_lcus_au = vector[&2; &1] /\
   pathstart moi_lcus_av = vector[&2; &1]:real^2 /\ pathfinish moi_lcus_av = vector[&1; &1]`,
  REWRITE_TAC[moi_lcus_as; moi_lcus_at; moi_lcus_au; moi_lcus_av; PATHSTART_JOIN;
              PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH]);;

(* Sanity (teeth): under the model relation both words of MOI_LCUS_SEAM are *)
(* loops with matching joints, and in Case 3 s3 has the ends of s1, in Case *)
(* 4 s2 and s4 are loops (the side conditions of the two disjuncts).         *)

let MOI_LCUS_SAN_WORDS = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (g:real^2->real^2) e.
     moi_lcus_model c f g e
     ==> (if e
          then pathfinish (f o g o moi_lcus_as) = pathstart (f o g o moi_lcus_av) /\
               pathfinish (f o g o moi_lcus_av) = pathstart (f o g o moi_lcus_au) /\
               pathfinish (f o g o moi_lcus_au) = pathstart (f o g o moi_lcus_at) /\
               pathfinish (f o g o moi_lcus_at) = pathstart (f o g o moi_lcus_as) /\
               pathstart (f o g o moi_lcus_au) = pathstart (f o g o moi_lcus_as) /\
               pathfinish (f o g o moi_lcus_au) = pathfinish (f o g o moi_lcus_as)
          else pathfinish (f o g o moi_lcus_as) =
                 pathstart (reversepath (f o g o moi_lcus_at)) /\
               pathfinish (reversepath (f o g o moi_lcus_at)) =
                 pathstart (f o g o moi_lcus_au) /\
               pathfinish (f o g o moi_lcus_au) =
                 pathstart (reversepath (f o g o moi_lcus_av)) /\
               pathfinish (reversepath (f o g o moi_lcus_av)) =
                 pathstart (f o g o moi_lcus_as) /\
               pathfinish (f o g o moi_lcus_at) = pathstart (f o g o moi_lcus_at) /\
               pathfinish (f o g o moi_lcus_av) = pathstart (f o g o moi_lcus_av))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lcus_model] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `&0` th) THEN MP_TAC(SPEC `&1` th)) THEN
  REWRITE_TAC[REAL_POS; REAL_LE_REFL; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_REVERSEPATH;
              PATHFINISH_REVERSEPATH; MOI_LCUS_SAN_ENDS; o_THM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_CASES_TAC `e:bool` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Mechanical check: with s1, s2, s3, s4 replaced by the images of A_s,    *)
(* A_t, A_u, A_v, the f2 words of the two disjuncts of                      *)
(* MOI_LT4_CUT_ARC_SPLIT are the two branches of the word of MOI_LCUS_SEAM. *)

let moi_lcus_words_ok =
  let sv n = mk_var(n,`:real^1->real^N`) in
  let s1 = sv "s1" and s2 = sv "s2" and s3 = sv "s3" and s4 = sv "s4" in
  let im a = mk_comb(mk_comb(`(o):(real^2->real^N)->(real^1->real^2)->real^1->real^N`,
                             `f:real^2->real^N`),
                     mk_comb(mk_comb(`(o):(real^2->real^2)->(real^1->real^2)->real^1->real^2`,
                                     `g:real^2->real^2`), a)) in
  let th = [im `moi_lcus_as`,s1; im `moi_lcus_at`,s2; im `moi_lcus_au`,s3;
            im `moi_lcus_av`,s4] in
  let w3 = `s1 ++ s4 ++ s3 ++ (s2:real^1->real^N)` and
      w4 = `s1 ++ reversepath s2 ++ s3 ++ reversepath (s4:real^1->real^N)` in
  let cb = snd(dest_exists(snd(dest_imp(snd(strip_forall MOI_LCUS_SEAM))))) in
  let wd = rand(last(conjuncts cb)) in
  let a = rand(rator wd) and b = rand wd in
  aconv (subst th w3) a && aconv (subst th w4) b &&
  can (find_term (aconv w3)) MOI_LT4_CUT_ARC_SPLIT &&
  can (find_term (aconv w4)) MOI_LT4_CUT_ARC_SPLIT;;

if not moi_lcus_words_ok then failwith "moi_lcus_words_ok";;

(* Glue: the two statements give MOI_LT4_CUT_ARC_SPLIT. *)

let MOI_LCUSD_CUT_ARC_SPLIT = prove
 (mk_imp(list_mk_conj MOI_LCUS_UNIT_TARGETS, MOI_LT4_CUT_ARC_SPLIT),
  DISCH_THEN(fun th -> ACCEPT_TAC(MP (CONJUNCT1 th) (CONJUNCT2 th))));;

