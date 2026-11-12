(* ========================================================================= *)
(* pc_moi_s26_nbhd: the compact reduction of Moise 26.4 (GTM 47, p.192).     *)
(* Main theorem                                                              *)
(*   COMPACT_NBHD |- MOI_S26_COMPACT_NBHD   (pc_moi_s2628_stmt.ml)           *)
(* Route: a 3-simplex D around k; the common subdivision of the faces of D  *)
(* and the simplices of c (SIMPLICIAL_COMPLEX_REFINE_POLYTOPES); a fine      *)
(* barycentric subdivision T; the simplices L of T meeting k; a derived     *)
(* neighbourhood of L inside u (DERIVED_NBHD_SMALL), which is a             *)
(* combinatorial 3-manifold by the antecedent DERIVED_NBHD_MANIFOLD; the    *)
(* subdivided c is the subcomplex s.                                         *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* A margin around k in u, a 3-simplex around k, the common                 *)
(* subdivision of the simplex with c, the part of a refinement lying in |c| *)
(* (a subcomplex refining c), and refinement under iterated barycentric     *)
(* subdivision.                                                              *)
(* ========================================================================= *)

let MOI_S6N_MARGIN = prove
 (`!(u:real^3->bool) k.
     open u /\ compact k /\ k SUBSET u
     ==> ?e. &0 < e /\ !x. x IN k ==> ball(x,e) SUBSET u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:real^3->bool` HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{u:real^3->bool}`) THEN
  ASM_REWRITE_TAC[UNIONS_1; IN_SING] THEN ASM_MESON_TAC[]);;

let MOI_S6N_BIG_SIMPLEX = prove
 (`!s:real^3->bool. bounded s ==> ?k. &3 simplex k /\ s SUBSET interior k`,
  GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `vec 0:real^3` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `vec 0 IN interior (k0:real^3->bool)` THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &2 * r / d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^3. (&2 * r / d) % x) k0` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^3. (&2 * r / d) % x`; `k0:real^3->bool`; `&3:int`]
      SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL] THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&2 * r)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < r /\ x <= r ==> x < &2 * r`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `d:real`]
      (MP (ISPEC `&2 * r / d` BALL_SCALING) (ASSUME `&0 < &2 * r / d`))) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    SUBGOAL_THEN `(&2 * r / d) * d = &2 * r` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < d`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* The common subdivision of a 3-simplex dd with a complex c inside it. *)

let MOI_S6N_REFINE = prove
 (`!(dd:real^3->bool) (c:(real^3->bool)->bool).
     &3 simplex dd /\ simplicial_complex c /\ UNIONS c SUBSET dd
     ==> ?t. simplicial_complex t /\ UNIONS t = dd /\
             (!s. s IN c ==> ?f. f SUBSET t /\ s = UNIONS f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&3:int`; `dd:real^3->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{f:real^3->bool | f face_of dd}`; `c:(real^3->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE];
      MAP_EVERY UNDISCH_TAC
       [`UNIONS c SUBSET (dd:real^3->bool)`; `(s:real^3->bool) IN c`] THEN
      SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]);;

(* The part of a refinement t lying in |c| is a subcomplex with union |c|; *)
(* its nonempty members lie in members of c (carrier argument).            *)

let MOI_S6N_PART = prove
 (`!(t:(real^3->bool)->bool) c.
     simplicial_complex t /\ simplicial_complex c /\
     (!s. s IN c ==> ?f. f SUBSET t /\ s = UNIONS f)
     ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS c} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS c} = UNIONS c /\
         (!s. s IN t /\ s SUBSET UNIONS c /\ ~(s = {})
              ==> ?r. r IN c /\ s SUBSET r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET_RESTRICT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `f:real^3->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET UNIONS c` THEN
      UNDISCH_TAC `(x:real^3) IN s` THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
      MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^3) IN r` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^3->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]];
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex (s:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^3. x IN relative_interior s` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS c` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN relative_interior s`; `(s:real^3->bool) SUBSET UNIONS c`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^3->bool` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?s':real^3->bool. s' IN f /\ (x:real^3) IN s'` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN r` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[IN_UNIONS];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s':real^3->bool` THEN CONJ_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    SUBGOAL_THEN `(s':real^3->bool) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^3->bool) INTER s' face_of s` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_CASES_TAC `(s:real^3->bool) INTER s' = s` THENL
     [UNDISCH_TAC `(s:real^3->bool) INTER s' = s` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `(s:real^3->bool) INTER s'`]
      FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
    ASM_REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `s:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN relative_interior s`; `(x:real^3) IN s'`] THEN
    SET_TAC[]]);;

(* Nonempty simplices of iterated barycentric subdivisions lie in simplices *)
(* of the original complex.                                                  *)

let MOI_S6N_ITER_REFINES = prove
 (`!(c:(real^N->bool)->bool) n.
     simplicial_complex c
     ==> !s. s IN ITER n barycentric_subdivision c /\ ~(s = {})
             ==> ?t. t IN c /\ s SUBSET t`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ITER] THEN MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[ITER] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`
      BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_FMB_SC_LF THEN ASM_MESON_TAC[MOI_BAR_ITER_SUBDIVISION];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t':real^N->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((s:real^N->bool) = {})` THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET t'` THEN SET_TAC[];
      ASM_MESON_TAC[SUBSET_TRANS]]]);;

(* ========================================================================= *)
(* The ambient triangulation.  ITER_UNIONS: a simplex of c is the union of   *)
(* the simplices of an iterated barycentric subdivision inside it.  AMBIENT: *)
(* a fine triangulation of a 3-simplex around k in which c is a union of     *)
(* simplices and the simplices meeting k lie in u.  SIMPLEX_CMWB: a finite   *)
(* triangulation of a 3-simplex is a combinatorial 3-manifold with boundary. *)
(* INTERIOR_TRANSFER: interior relative to D at an interior point of D is    *)
(* interior.                                                                 *)
(* ========================================================================= *)

let MOI_S6N_ITER_UNIONS = prove
 (`!(c:(real^N->bool)->bool) n t.
     simplicial_complex c /\ t IN c
     ==> t = UNIONS {s | s IN ITER n barycentric_subdivision c /\ s SUBSET t}`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ITER] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET_REFL; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[ITER] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN ITER n barycentric_subdivision c
        ==> s = UNIONS {r | r IN barycentric_subdivision
                                   (ITER n barycentric_subdivision c) /\ r SUBSET s}`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `ITER n barycentric_subdivision (c:(real^N->bool)->bool)`
      BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MOI_FMB_SC_LF THEN ASM_MESON_TAC[MOI_BAR_ITER_SUBDIVISION];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) = UNIONS f` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                           ASSUME_TAC th) THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(s:real^N->bool) = UNIONS f` THEN
      UNDISCH_TAC `(r:real^N->bool) IN f` THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [UNDISCH_TAC
     `t = UNIONS {s | s IN ITER n barycentric_subdivision (c:(real^N->bool)->bool) /\
                      s SUBSET t}` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^N) IN s` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SET_TAC[]]);;

let MOI_S6N_AMBIENT = prove
 (`!(u:real^3->bool) k (c:(real^3->bool)->bool).
     open u /\ compact k /\ k SUBSET u /\ simplicial_complex c /\ UNIONS c SUBSET k
     ==> ?dd tt. &3 simplex dd /\ k SUBSET interior dd /\
                 simplicial_complex tt /\ UNIONS tt = dd /\
                 (!r. r IN c ==> ?f. f SUBSET tt /\ r = UNIONS f) /\
                 (!s. s IN tt /\ ~(s INTER k = {}) ==> s SUBSET u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `k:real^3->bool`] MOI_S6N_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_S6N_BIG_SIMPLEX) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `c:(real^3->bool)->bool`] MOI_S6N_REFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `dd:real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`UNIONS c SUBSET (k:real^3->bool)`; `(k:real^3->bool) SUBSET interior dd`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t1:(real^3->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`dd:real^3->bool`; `ITER n barycentric_subdivision (t1:(real^3->bool)->bool)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_ITER_SUBDIVISION];
    MP_TAC(ISPECL [`t1:(real^3->bool)->bool`; `t1:(real^3->bool)->bool`; `n:num`]
      MOI_FDN_ITER_SUBCOMPLEX) THEN
    ASM_SIMP_TAC[MOI_FMB_SC_LF; simplicial_subcomplex; SUBSET_REFL] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SIMP_TAC[]];
    X_GEN_TAC `r:real^3->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^3->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `t1:(real^3->bool)->bool`)) (concl th) &&
      can (find_term (fun t -> t = `c:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `{s | s IN ITER n barycentric_subdivision (t1:(real^3->bool)->bool) /\
           s SUBSET r}` THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    UNDISCH_TAC `(r:real^3->bool) = UNIONS f` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                         ASSUME_TAC th) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t1:(real^3->bool)->bool`; `n:num`; `q:real^3->bool`]
      MOI_S6N_ITER_UNIONS) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^3) IN q` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `q:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:real^3->bool) = UNIONS f` THEN
    UNDISCH_TAC `(q:real^3->bool) IN f` THEN SET_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `~((s:real^3->bool) INTER k = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,e)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(s:real^3->bool)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `simplicial_complex (ITER n barycentric_subdivision
                    (t1:(real^3->bool)->bool))` MP_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_ITER_SUBDIVISION]; ALL_TAC] THEN
    REWRITE_TAC[simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]]);;

let MOI_S6N_SIMPLEX_CMWB = prove
 (`!(d:(real^3->bool)->bool) dd.
     simplicial_complex d /\ UNIONS d = dd /\ &3 simplex dd
     ==> combinatorial_manifold_with_boundary 3 d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^3->bool)->bool`; `relative_frontier dd:real^3->bool`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`dd:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_S6N_INTERIOR_TRANSFER = prove
 (`!(dd:real^3->bool) nn x.
     x IN (subtopology euclidean dd) interior_of nn /\ x IN interior dd
     ==> x IN interior nn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))
    ASSUME_TAC) THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  EXISTS_TAC `oo INTER interior (dd:real^3->bool)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `dd:real^3->bool` INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC [`(v:real^3->bool) SUBSET nn`; `v:real^3->bool = dd INTER oo`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* The main theorem.  REFINE_ITER: the members of c stay unions of          *)
(* simplices under iterated barycentric subdivision of tt.  COMPACT_NBHD:    *)
(* w is a derived neighbourhood of the simplices meeting k in a fine        *)
(* subdivision of the ambient triangulation, s the simplices of its second  *)
(* derived lying in members of c.                                            *)
(* ========================================================================= *)

let MOI_S6N_REFINE_ITER = prove
 (`!(tt:(real^3->bool)->bool) c.
     simplicial_complex tt /\ (!r. r IN c ==> ?f. f SUBSET tt /\ r = UNIONS f)
     ==> !n r. r IN c
               ==> r = UNIONS {s | s IN ITER n barycentric_subdivision tt /\ s SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  X_GEN_TAC `r:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  UNDISCH_TAC `(r:real^3->bool) = UNIONS f` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] THEN
                       ASSUME_TAC th) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `n:num`; `q:real^3->bool`]
    MOI_S6N_ITER_UNIONS) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^3) IN q` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `q:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(q:real^3->bool) IN f` THEN SET_TAC[]);;

let COMPACT_NBHD = prove
 (MOI_S26_COMPACT_NBHD,
  DISCH_THEN(LABEL_TAC "dnm") THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `k:real^3->bool`; `c:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `k:real^3->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`{}:(real^3->bool)->bool`; `{}:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; UNIONS_0; EMPTY_SUBSET; NOT_IN_EMPTY;
                    simplicial_subcomplex; SUBSET_REFL] THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex;
                NOT_IN_EMPTY; UNIONS_0] THEN
    UNDISCH_TAC `UNIONS c SUBSET (k:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `k:real^3->bool`; `c:(real^3->bool)->bool`]
    MOI_S6N_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real^3->bool` (X_CHOOSE_THEN `tt:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (tt:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  (* the simplices meeting k and their faces *)
  ABBREV_TAC `L = {s:real^3->bool | ?r. r IN tt /\ ~(r INTER k = {}) /\ s face_of r}` THEN
  SUBGOAL_THEN
   `simplicial_subcomplex L (tt:(real^3->bool)->bool) /\ FINITE L /\
    (k:real^3->bool) SUBSET UNIONS L /\ UNIONS L SUBSET dd INTER u`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `k:real^3->bool`]
      MOI_FDN_MEETS_FACES_SUBCOMPLEX) THEN
    MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `k:real^3->bool`]
      MOI_FDN_MEETS_FACES_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `tt:(real^3->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS tt` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `dd:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET interior dd` THEN
        UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `UNIONS tt = (dd:real^3->bool)` THEN
        UNDISCH_TAC `(s:real^3->bool) IN tt` THEN UNDISCH_TAC `(x:real^3) IN s` THEN
        SET_TAC[];
        SUBGOAL_THEN `(s:real^3->bool) SUBSET u` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* a derived neighbourhood inside u *)
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `L:(real^3->bool)->bool`;
                 `dd INTER u:real^3->bool`] DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `m:num`)] THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `L:(real^3->bool)->bool`; `m:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t' = ITER m barycentric_subdivision (tt:(real^3->bool)->bool)` THEN
  ABBREV_TAC `l' = ITER m barycentric_subdivision (L:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN
   `simplicial_complex (t':(real^3->bool)->bool) /\ FINITE (l':(real^3->bool)->bool) /\
    combinatorial_manifold_with_boundary 3 t'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (t':(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "t'" THEN ASM_MESON_TAC[MOI_BAR_ITER_SUBDIVISION]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t':(real^3->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      MATCH_MP_TAC MOI_S6N_SIMPLEX_CMWB THEN EXISTS_TAC `dd:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t':(real^3->bool)->bool`; `l':(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "dnm" (MP_TAC o SPECL [`t':(real^3->bool)->bool`; `l':(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the second derived of t' and the subdivided c *)
  SUBGOAL_THEN
   `simplicial_complex (barycentric_subdivision (barycentric_subdivision
      (t':(real^3->bool)->bool))) /\
    UNIONS (barycentric_subdivision (barycentric_subdivision t')) = dd`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
    ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION; BARYCENTRIC_SUBDIVISION_LF;
                 MOI_FMB_SC_LF; BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                    (t':(real^3->bool)->bool))`; `c:(real^3->bool)->bool`]
    MOI_S6N_PART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^3->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{s | s IN barycentric_subdivision (barycentric_subdivision
                      (t':(real^3->bool)->bool)) /\ s SUBSET r}` THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `c:(real^3->bool)->bool`]
      MOI_S6N_REFINE_ITER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`SUC(SUC m)`; `r:real^3->bool`]) THEN
    ASM_REWRITE_TAC[ITER];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd_complex (t':(real^3->bool)->bool) l'`;
    `{s | s IN barycentric_subdivision (barycentric_subdivision
            (t':(real^3->bool)->bool)) /\ ?r. r IN c /\ s SUBSET r}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* k in the interior *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S6N_INTERIOR_TRANSFER THEN EXISTS_TAC `dd:real^3->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS (L:(real^3->bool)->bool) SUBSET
                   subtopology euclidean (dd:real^3->bool) interior_of
                   derived_nbhd (t':(real^3->bool)->bool) l'` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET UNIONS L` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
      UNDISCH_TAC `(k:real^3->bool) SUBSET interior dd` THEN
      UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[]];
    (* inside u *)
    UNDISCH_TAC `derived_nbhd (t':(real^3->bool)->bool) l' SUBSET dd INTER u` THEN
    SET_TAC[];
    (* the subcomplex *)
    REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^3->bool`
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      ASM_CASES_TAC `s:real^3->bool = {}` THENL
       [UNDISCH_TAC `~(k:real^3->bool = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
        SUBGOAL_THEN `(x:real^3) IN UNIONS (barycentric_subdivision
                        (barycentric_subdivision t'))` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `dd:real^3->bool` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(k:real^3->bool) SUBSET interior dd` THEN
          UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `q:real^3->bool` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[EMPTY_FACE_OF] THEN
        UNDISCH_TAC `(x:real^3) IN q` THEN UNDISCH_TAC `(x:real^3) IN k` THEN
        UNDISCH_TAC `(k:real^3->bool) SUBSET UNIONS L` THEN
        UNDISCH_TAC `UNIONS (l':(real^3->bool)->bool) = UNIONS L` THEN SET_TAC[];
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `~(s:real^3->bool = {})` THEN
          UNDISCH_TAC `(s:real^3->bool) SUBSET r` THEN
          UNDISCH_TAC `(r:real^3->bool) IN c` THEN
          UNDISCH_TAC `UNIONS c SUBSET (k:real^3->bool)` THEN
          UNDISCH_TAC `(k:real^3->bool) SUBSET UNIONS L` THEN
          UNDISCH_TAC `UNIONS (l':(real^3->bool)->bool) = UNIONS L` THEN SET_TAC[];
          MATCH_MP_TAC FACE_OF_REFL THEN
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `f:real^3->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
    (* the union *)
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real^3->bool` THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS {s | s IN barycentric_subdivision
                      (barycentric_subdivision (t':(real^3->bool)->bool)) /\
                      s SUBSET UNIONS c}` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN s` THEN SET_TAC[]];
    (* refinement *)
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

