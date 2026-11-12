(* ========================================================================= *)
(* pc_moi_fnd_stmt5: the simplicial approximation theorem, which HOL Light  *)
(* does not provide; LT_FILL (pc_moi_lt_fill) and PL_FILL (pc_moi_s26_fill, *)
(* Secs 26-28) use it or its lemmas.                                        *)
(*   MOI_FND_SIMPLICIAL_APPROX: a continuous map f from a simplicial        *)
(*   complex k to a simplicial complex l (both finite, by the definition)  *)
(*   has, after n barycentric subdivisions of k, a simplicial approximation *)
(*   g from ITER n barycentric_subdivision k to l: g x lies in every       *)
(*   simplex of l that contains f x (so in the carrier of f x, and g maps  *)
(*   into any subcomplex that f maps into), f and g are homotopic in       *)
(*   UNIONS l (straight lines inside the carriers), and, relative part, g  *)
(*   misses a FULL subcomplex l0 of l on a compact set c on which f misses *)
(*   it (full: a nonempty simplex of l with all its vertices in l0 is in   *)
(*   l0; without fullness the relative part fails, e.g. a point mapped to *)
(*   the barycentre of a triangle, l0 its boundary).  Take l0 = {} and     *)
(*   c = {} for the plain theorem.                                          *)
(*   The hypothesis ~(l = {}) excludes the degenerate case k = {{}} (only  *)
(*   the empty simplex), l = {}: every barycentric subdivision contains the *)
(*   empty simplex, whose image {} is not in the empty l.                   *)
(*   MOI_FS5_SAN_ID: for nonempty k the hypotheses hold with l = k, l0 = {} *)
(*   and the conclusion is satisfiable (the identity of k, n = 0).         *)
(* pc_moi_fnd_sapprox proves SIMPLICIAL_APPROX :                             *)
(*   |- MOI_FND_SIMPLICIAL_APPROX.                                           *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FND_SIMPLICIAL_APPROX =
 `!(k:(real^M->bool)->bool) (l:(real^N->bool)->bool) (l0:(real^N->bool)->bool)
   (f:real^M->real^N) (c:real^M->bool).
     simplicial_complex k /\ simplicial_complex l /\ ~(l = {}) /\
     simplicial_subcomplex l0 l /\
     (!s. s IN l /\ ~(s = {}) /\ (!v. {v} IN l /\ v IN s ==> {v} IN l0) ==> s IN l0) /\
     f continuous_on UNIONS k /\ IMAGE f (UNIONS k) SUBSET UNIONS l /\
     compact c /\ c SUBSET UNIONS k /\ DISJOINT (IMAGE f c) (UNIONS l0)
     ==> ?n (g:real^M->real^N).
           simplicial_map_on (ITER n barycentric_subdivision k) l g /\
           (!x s. x IN UNIONS k /\ s IN l /\ f x IN s ==> g x IN s) /\
           (!x. x IN c ==> ~(g x IN UNIONS l0)) /\
           homotopic_with (\h:real^M->real^N. T)
             (subtopology euclidean (UNIONS k),subtopology euclidean (UNIONS l)) f g`;;

let MOI_FS5_SAN_ID = prove
 (`!(k:(real^M->bool)->bool).
     simplicial_complex k /\ ~(k = {})
     ==> ~(k = {}) /\ simplicial_subcomplex ({}:(real^M->bool)->bool) k /\
         (!s. s IN k /\ ~(s = {}) /\
              (!v. {v} IN k /\ v IN s ==> {v} IN ({}:(real^M->bool)->bool))
              ==> s IN ({}:(real^M->bool)->bool)) /\
         simplicial_map_on (ITER 0 barycentric_subdivision k) k (\x:real^M. x) /\
         (!x s. x IN UNIONS k /\ s IN k /\ x IN s ==> x IN s) /\
         homotopic_with (\h:real^M->real^M. T)
           (subtopology euclidean (UNIONS k),subtopology euclidean (UNIONS k))
           (\x. x) (\x. x)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[simplicial_subcomplex; EMPTY_SUBSET; NOT_IN_EMPTY];
    REWRITE_TAC[NOT_IN_EMPTY] THEN X_GEN_TAC `s:real^M->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?v:real^M. v IN s /\ {v} IN k` STRIP_ASSUME_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real^M->bool`)
      (CONJUNCTS_THEN2 (LABEL_TAC "face") (K ALL_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `m:int`) THEN
    SUBGOAL_THEN `?v:real^M. v extreme_point_of s` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
      EXISTS_TAC `v:real^M` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[extreme_point_of];
        USE_THEN "face" MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_REWRITE_TAC[FACE_OF_SING]]];
    REWRITE_TAC[ITER; simplicial_map_on; IMAGE_ID] THEN
    X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`\x:real^M. x`; `vec 0:real^M`] THEN
    REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID];
    MESON_TAC[];
    REWRITE_TAC[HOMOTOPIC_WITH_REFL; CONTINUOUS_MAP_ID]]);;

print_string ("FS5 " ^
   string_of_bool ((type_of MOI_FND_SIMPLICIAL_APPROX = bool_ty &&
                            frees MOI_FND_SIMPLICIAL_APPROX = [] &&
                            hyp MOI_FS5_SAN_ID = [])) ^
   "\n");;

