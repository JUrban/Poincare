(* ========================================================================= *)
(* pc_moi_lt_gpbstmt: the statements into which general position for the     *)
(* loop theorem (GP_CROSSINGS_2 = MOI_LT2_GP_CROSSINGS of                    *)
(* pc_moi_loop_stmt2.ml, Moise p.184) is split.                              *)
(*   moi_lgb_tlinear tt L g : every simplex of the source triangulation L  *)
(*     goes affinely into one simplex of the target complex tt;            *)
(*   moi_lgb_tgeneric tt L g Q : tlinear, and at the points of Q the map is *)
(*     in general position measured inside the simplices of tt (chart      *)
(*     independent);                                                        *)
(*   moi_lgb_atlas c tt A : tt a triangulation of a neighbourhood refining  *)
(*     c, A a finite atlas of charts (as in MOI_LT_MANIFOLD_CHARTS) with    *)
(*     compact cores, each chart affine on the simplices of tt in its      *)
(*     domain;                                                              *)
(*   MOI_LGB_CHART_STEP : the chart step, proved in pc_moi_lt_gpb1;         *)
(*   MOI_LGB_GP_FROM_STEP : MOI_LGB_CHART_STEP ==> MOI_LT2_GP_CROSSINGS,    *)
(*     proved in pc_moi_lt_gpb2;                                            *)
(*   MOI_LGB_ATLAS_EXISTS : the adapted atlas exists (a lemma of gpb2,      *)
(*     given here as a term only).                                          *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The three definitions and the statements.                                *)
(* ------------------------------------------------------------------------- *)

(* T-linear maps: each simplex of L is mapped affinely into one simplex of  *)
(* tt.  In the users tt is a simplicial complex (moi_lgb_atlas).            *)

let moi_lgb_tlinear = new_definition
 `moi_lgb_tlinear (tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (g:real^2->real^N) <=>
    simplicial_complex L /\ UNIONS L = std_triangle /\
    !r. r IN L ==> (?s. s IN tt /\ IMAGE g r SUBSET s) /\
                   (?l y. linear l /\ !x. x IN r ==> g x = l x + y)`;;

(* T-generic at the points of Q.  Clauses, all restricted to Q:             *)
(* (1) g is injective on the union of two meeting simplices of L at points  *)
(*     mapped into Q (so the simplices at a double point in Q are disjoint);*)
(* (2) no triangle of L mapped into a wall (2-simplex) of tt meets Q;       *)
(* (3) no fold along a wall: an edge of L mapped into a wall at a point of  *)
(*     Q has its two triangles in different cells (3-simplices);           *)
(* (4) two disjoint simplices of L meeting in Q are transverse inside the   *)
(*     smallest simplex s of tt containing both images (dimension count in  *)
(*     the affine hull of s; for tt a simplicial complex this smallest      *)
(*     simplex exists as soon as one simplex contains both images, see      *)
(*     MOI_LGB_MIN_SIMPLEX; sheets in two cells meeting on their common     *)
(*     wall are covered through their traces, which are faces in the wall); *)
(* (5) double points in Q avoid the 1-skeleton of tt.                       *)

let moi_lgb_tgeneric = new_definition
 `moi_lgb_tgeneric (tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (g:real^2->real^N)
                   (Q:real^N->bool) <=>
    moi_lgb_tlinear tt L g /\
    (!r r' x x'. r IN L /\ r' IN L /\ ~(r INTER r' = {}) /\ x IN r /\ x' IN r' /\
                 g x = g x' /\ g x IN Q ==> x = x') /\
    (!r s. r IN L /\ aff_dim r = &2 /\ s IN tt /\ aff_dim s <= &2 /\ IMAGE g r SUBSET s
           ==> IMAGE g r INTER Q = {}) /\
    (!e r1 r2 s. e IN L /\ r1 IN L /\ r2 IN L /\ ~(r1 = r2) /\ aff_dim e = &1 /\
                 aff_dim r1 = &2 /\ aff_dim r2 = &2 /\ e SUBSET r1 /\ e SUBSET r2 /\
                 s IN tt /\ aff_dim s = &2 /\ IMAGE g e SUBSET s /\
                 ~(IMAGE g e INTER Q = {})
                 ==> !s'. s' IN tt /\ aff_dim s' = &3
                          ==> ~(IMAGE g r1 UNION IMAGE g r2 SUBSET s')) /\
    (!r r' s. r IN L /\ r' IN L /\ DISJOINT r r' /\ s IN tt /\
              IMAGE g r UNION IMAGE g r' SUBSET s /\
              (!s'. s' IN tt /\ IMAGE g r UNION IMAGE g r' SUBSET s' ==> s SUBSET s') /\
              ~(IMAGE g r INTER IMAGE g r' INTER Q = {})
              ==> aff_dim s <= aff_dim (IMAGE g r) + aff_dim (IMAGE g r') /\
                  aff_dim (affine hull (IMAGE g r) INTER affine hull (IMAGE g r')) =
                  aff_dim (IMAGE g r) + aff_dim (IMAGE g r') - aff_dim s) /\
    (!r r' s. r IN L /\ r' IN L /\ DISJOINT r r' /\ s IN tt /\ aff_dim s <= &1
              ==> DISJOINT (IMAGE g r INTER IMAGE g r' INTER Q) s)`;;

(* The adapted atlas: tt a simplicial complex refining c and subdividing    *)
(* each simplex of c inside UNIONS tt; A a finite set of charts (u,h,h',kk) *)
(* of UNIONS c onto the unit ball or the unit half ball (the clauses of     *)
(* MOI_LT_MANIFOLD_CHARTS without the centre point), inside UNIONS tt,      *)
(* with a compact core kk; the simplices of tt within three steps of kk     *)
(* (s1 meets kk, s2 meets s1, s3 meets s2) lie in u and the chart is affine *)
(* on each of them (the margin used by the moves of the chart step; it is   *)
(* kept by refining tt, so the atlas can be adapted chart by chart).        *)

let moi_lgb_atlas = new_definition
 `moi_lgb_atlas (c:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
     (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool) <=>
    simplicial_complex tt /\
    (!s. s IN tt ==> ?s'. s' IN c /\ s SUBSET s') /\
    (!s'. s' IN c ==> ?d. d SUBSET tt /\ UNIONS d = s' INTER UNIONS tt) /\
    FINITE A /\
    (!u h h' kk.
       (u,h,h',kk) IN A
       ==> open_in (subtopology euclidean (UNIONS c)) u /\ u SUBSET UNIONS tt /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\
           ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
            (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
             IMAGE h (u INTER complex_boundary c) =
             IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
           compact kk /\ kk SUBSET u /\
           (!s1 s2 s3. s1 IN tt /\ s2 IN tt /\ s3 IN tt /\ ~(s1 INTER kk = {}) /\
                       ~(s1 INTER s2 = {}) /\ ~(s2 INTER s3 = {})
                       ==> s3 SUBSET u /\
                           ?l y. linear l /\ !x. x IN s3 ==> h x = l x + y))`;;

(* The chart step (proved in pc_moi_lt_gpb1): a T-linear singular disk,     *)
(* T-generic at the points of a closed set Q, is moved inside one chart of  *)
(* the atlas to a singular disk T-generic at the points of Q UNION kk, close *)
(* to it, equal to it off the preimage of the chart, with the boundary in w *)
(* and the boundary loop homotopic in w.                                    *)

let MOI_LGB_CHART_STEP =
 `!(c:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
    (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)
    u h h' kk (L:(real^2->bool)->bool) (g:real^2->real^N) Q w e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lgb_atlas c tt A /\
     (u,h,h',kk) IN A /\ moi_lt_singular_disk c g /\ moi_lgb_tgeneric tt L g Q /\
     closed Q /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE g (relative_frontier std_triangle) SUBSET w /\ &0 < e
     ==> ?g' L'. moi_lt_singular_disk c g' /\ moi_lgb_tgeneric tt L' g' (Q UNION kk) /\
                 (!x. x IN std_triangle ==> dist(g' x,g x) < e) /\
                 (!x. x IN std_triangle /\ ~(g x IN u) ==> g' x = g x) /\
                 IMAGE g' (relative_frontier std_triangle) SUBSET w /\
                 homotopic_loops w (g o std_triangle_loop) (g' o std_triangle_loop)`;;

(* The second half (proved in pc_moi_lt_gpb2).                              *)

let MOI_LGB_GP_FROM_STEP = mk_imp(MOI_LGB_CHART_STEP,MOI_LT2_GP_CROSSINGS);;

(* The adapted atlas exists for every compact set ks in |c| and every       *)
(* finite subdivision t of c: tt also refines t near ks, and the cores      *)
(* cover an r-neighbourhood of ks in |c|.  A lemma of pc_moi_lt_gpb2, given *)
(* here as a term only.                                                     *)

let MOI_LGB_ATLAS_EXISTS =
 `!(c:(real^N->bool)->bool) (t:(real^N->bool)->bool) (ks:real^N->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE t /\ lf_simplicial_complex t /\ subdivides t c /\
     compact ks /\ ks SUBSET UNIONS c
     ==> ?tt (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool) r.
           moi_lgb_atlas c tt A /\
           (!s. s IN tt ==> ?s'. s' IN t /\ s SUBSET s') /\
           (!s'. s' IN t ==> ?d. d SUBSET tt /\ UNIONS d = s' INTER UNIONS tt) /\
           &0 < r /\
           (!x y. x IN UNIONS c /\ y IN ks /\ dist(x,y) < r
                  ==> ?u h h' kk. (u,h,h',kk) IN A /\ x IN kk)`;;

(* ------------------------------------------------------------------------- *)
(* Sanity theorems (all with no hypotheses) and the checks.                 *)
(* ------------------------------------------------------------------------- *)

(* (a) A simplicial map of a triangulation of the triangle into tt is       *)
(* tlinear (so pulling back a triangulation starts the iteration).          *)

let MOI_LGB_TLINEAR_SIMPLICIAL = prove
 (`!(tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (g:real^2->real^N).
     simplicial_complex L /\ UNIONS L = std_triangle /\ simplicial_map_on L tt g
     ==> moi_lgb_tlinear tt L g`,
  REWRITE_TAC[moi_lgb_tlinear; simplicial_map_on] THEN MESON_TAC[SUBSET_REFL]);;

(* (b) Every tlinear map is tgeneric over the empty set (the start).        *)

let MOI_LGB_TGENERIC_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (g:real^2->real^N).
     moi_lgb_tlinear tt L g ==> moi_lgb_tgeneric tt L g {}`,
  SIMP_TAC[moi_lgb_tgeneric; NOT_IN_EMPTY; INTER_EMPTY; DISJOINT_EMPTY]);;

(* (c) tgeneric is monotone in Q.                                            *)

let MOI_LGB_TGENERIC_MONO = prove
 (`!(tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (g:real^2->real^N) Q Q'.
     moi_lgb_tgeneric tt L g Q /\ Q' SUBSET Q ==> moi_lgb_tgeneric tt L g Q'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb_tgeneric] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g1")
      (CONJUNCTS_THEN2 (LABEL_TAC "g2") (CONJUNCTS_THEN2 (LABEL_TAC "g3")
        (CONJUNCTS_THEN2 (LABEL_TAC "g4") (LABEL_TAC "g5"))))))
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`; `x:real^2`; `x':real^2`] THEN
    STRIP_TAC THEN USE_THEN "g1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `r':real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `s:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "g2" (MP_TAC o SPECL [`r:real^2->bool`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
                         `s:real^N->bool`] THEN
    STRIP_TAC THEN
    USE_THEN "g3" (MP_TAC o SPECL [`e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
                                   `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`] THEN
    STRIP_TAC THEN
    USE_THEN "g4" (MP_TAC o SPECL [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`] THEN
    STRIP_TAC THEN
    USE_THEN "g5" (MP_TAC o SPECL [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]]);;

(* (d) Teeth: a constant map is never tgeneric at its value (clause (1)).   *)

let MOI_LGB_TGENERIC_TEETH = prove
 (`!(tt:(real^N->bool)->bool) (L:(real^2->bool)->bool) (y:real^N) Q.
     y IN Q ==> ~moi_lgb_tgeneric tt L (\x:real^2. y) Q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lgb_tgeneric] THEN
  MATCH_MP_TAC(TAUT `(p ==> F) ==> ~p`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[moi_lgb_tlinear])
    (CONJUNCTS_THEN2 (LABEL_TAC "g1") (K ALL_TAC))) THEN
  SUBGOAL_THEN `?r (x:real^2) x'. r IN L /\ x IN r /\ x' IN r /\ ~(x = x')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(a /\ b /\ c /\ ~d) <=> a /\ b /\ c ==> d`]) THEN
    SUBGOAL_THEN `FINITE (std_triangle)` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `UNIONS (L:(real^2->bool)->bool) = std_triangle`)) THEN
      REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex];
        X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
        ASM_CASES_TAC `r:real^2->bool = {}` THEN ASM_REWRITE_TAC[FINITE_EMPTY] THEN
        FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:real^2}` THEN
        REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN ASM_MESON_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `FINITE(segment[vec 0:real^2,basis 1])` MP_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `std_triangle` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[std_triangle; SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        REWRITE_TAC[FINITE_SEGMENT] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
        SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH]]];
    ALL_TAC] THEN
  USE_THEN "g1" (MP_TAC o SPECL [`r:real^2->bool`; `r:real^2->bool`; `x:real^2`; `x':real^2`]) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN ASM SET_TAC[]);;

(* (e) The atlas predicate is satisfiable (empty triangulation, no charts);  *)
(* the content is MOI_LGB_ATLAS_EXISTS (cores covering a neighbourhood).    *)

let MOI_LGB_ATLAS_EMPTY = prove
 (`!c:(real^N->bool)->bool. moi_lgb_atlas c {} {}`,
  GEN_TAC THEN REWRITE_TAC[moi_lgb_atlas; NOT_IN_EMPTY; FINITE_EMPTY; UNIONS_0;
                           INTER_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex; NOT_IN_EMPTY; FINITE_EMPTY];
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; UNIONS_0]]);;

(* (f) The smallest simplex of clause (4) exists in a simplicial complex.   *)

let MOI_LGB_MIN_SIMPLEX = prove
 (`!(tt:(real^N->bool)->bool) a s.
     simplicial_complex tt /\ s IN tt /\ a SUBSET s
     ==> ?s0. s0 IN tt /\ a SUBSET s0 /\ !s'. s' IN tt /\ a SUBSET s' ==> s0 SUBSET s'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  MP_TAC(BETA_RULE(INST [`\n:int. ?s1:real^N->bool. s1 IN tt /\ a SUBSET s1 /\
                                                    aff_dim s1 + &1 = n`, `P:int->bool`]
                        INT_WOP)) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `aff_dim (s:real^N->bool) + &1` THEN
    CONJ_TAC THENL [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) (LABEL_TAC "min")))) THEN
  EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s0 INTER s':real^N->bool = s0` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s0 INTER s':real^N->bool) face_of s0 /\ (s0 INTER s') IN tt`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (s0 INTER s':real^N->bool) < aff_dim s0` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o SPEC `aff_dim (s0 INTER s':real^N->bool) + &1`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `s0 INTER s':real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `s0 INTER s':real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN ASM_INT_ARITH_TAC]);;

(* The checks: every statement term is a closed boolean term, the second    *)
(* half composes with the first by one MP, and all sanity theorems have no  *)
(* hypotheses.                                                               *)

let MOI_LGB_COMPOSE = prove
 (mk_imp(mk_conj(MOI_LGB_CHART_STEP,MOI_LGB_GP_FROM_STEP),MOI_LT2_GP_CROSSINGS),
  DISCH_THEN(fun th -> ACCEPT_TAC(MP (CONJUNCT2 th) (CONJUNCT1 th))));;

Printf.printf "GPBSTMT_CHECK %b\n%!"
  (type_of MOI_LGB_CHART_STEP = bool_ty && frees MOI_LGB_CHART_STEP = [] &&
   type_of MOI_LGB_GP_FROM_STEP = bool_ty && frees MOI_LGB_GP_FROM_STEP = [] &&
   type_of MOI_LGB_ATLAS_EXISTS = bool_ty && frees MOI_LGB_ATLAS_EXISTS = [] &&
   aconv (rand MOI_LGB_GP_FROM_STEP) MOI_LT2_GP_CROSSINGS &&
   forall (fun th -> hyp th = [])
     [MOI_LGB_TLINEAR_SIMPLICIAL; MOI_LGB_TGENERIC_EMPTY; MOI_LGB_TGENERIC_MONO;
      MOI_LGB_TGENERIC_TEETH; MOI_LGB_ATLAS_EMPTY; MOI_LGB_MIN_SIMPLEX; MOI_LGB_COMPOSE]);;

