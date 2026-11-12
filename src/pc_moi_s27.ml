(* ========================================================================= *)
(* pc_moi_s27: Moise GTM 47, Thm 27.3 (p.198): a polygon J in a PL annulus  *)
(* A bounds a 2-cell in A or carries all loops of A (the map form of: J    *)
(* carries a generator of pi(A)).  Route: transport by the PL homeomorphism  *)
(* of pl_annulus to the square annulus model in real^2; there the closed     *)
(* inside of J (PL Schoenflies) either misses the hole, giving the 2-cell,  *)
(* or contains it; then J winds once around the hole, and loops in the      *)
(* model are classified by their winding number around the origin           *)
(* (WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ and a radial retraction).             *)
(*                                                                           *)
(* First, affine transfer of 2-simplices between real^2 and real^N.        *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_cone.ml";;

prioritize_real();;
type_invention_error := true;;

(* Copied, with its proof, from MOI_CEL_PLH_RESTRICT of pc_moi_cells.ml     *)
(* (not in the load closure of this file).                                   *)

let MOI_S27_PLH_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ locally_polyhedral s'
     ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* An injective affine map carries a simplex onto a simplex of the same     *)
(* dimension, relative frontier onto relative frontier, PL homeomorphically. *)

let MOI_S27_INJ_AFFINE_SIMPLEX = prove
 (`!(l:real^M->real^N) (y:real^N) n (k:real^M->bool).
     linear l /\ (!x x'. l x = l x' ==> x = x') /\ n simplex k
     ==> n simplex (IMAGE (\x. l x + y) k) /\
         relative_frontier (IMAGE (\x. l x + y) k) =
         IMAGE (\x. l x + y) (relative_frontier k) /\
         ?h'. pl_homeomorphism (k,IMAGE (\x. l x + y) k) ((\x. l x + y),h')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s:real^M->bool. IMAGE (\x. (l:real^M->real^N) x + y) s =
                     IMAGE (\x:real^N. y + x) (IMAGE l s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `n simplex (IMAGE (\x. (l:real^M->real^N) x + y) k) /\
    relative_frontier (IMAGE (\x. (l:real^M->real^N) x + y) k) =
    IMAGE (\x. l x + y) (relative_frontier k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[SIMPLEX_TRANSLATION_EQ] THEN
      MP_TAC(ISPECL [`l:real^M->real^N`; `k:real^M->bool`; `n:int`]
        SIMPLEX_LINEAR_IMAGE_EQ) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!s:real^M->bool. IMAGE (\x. (l:real^M->real^N) x + y) s =
                     IMAGE (\x:real^N. y + x) (IMAGE l s)` THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `l:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^N. (l':real^N->real^M) z + --(l' y)` THEN
  SUBGOAL_THEN
   `!x:real^M. (l':real^N->real^M) ((l:real^M->real^N) x + y) + --(l' y) = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l':real^N->real^M)`)] THEN
    UNDISCH_TAC `(l':real^N->real^M) o (l:real^M->real^N) = I` THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (k:real^M->bool) /\
                polytope (IMAGE (\x. (l:real^M->real^N) x + y) k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `n:int` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE]] THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
    MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `--((l':real^N->real^M) y)`] THEN
    ASM_REWRITE_TAC[]]);;

(* Two noncollinear vectors are linearly independent.                      *)

let MOI_S27_NONCOLLINEAR_INDEP = prove
 (`!(u:real^N) v s t.
     ~collinear{vec 0,u,v} /\ s % u + t % v = vec 0 ==> s = &0 /\ t = &0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [UNDISCH_TAC `s % (u:real^N) + t % v = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(s / t):real`) THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  SUBGOAL_THEN `t % (v:real^N) = t % (--(s / t) % u)` MP_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `t * --(s / t) = --s` SUBST1_TAC THENL
     [UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `s % (u:real^N) + t % v = vec 0` THEN VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]);;

(* The linear map of the plane sending the standard basis to u and v.      *)

let MOI_S27_PLANE_LINEAR = prove
 (`!u v:real^N.
     ~collinear{vec 0,u,v}
     ==> linear (\x:real^2. x$1 % u + x$2 % v) /\
         (!x x'. (\x:real^2. x$1 % u + x$2 % v) x =
                 (\x:real^2. x$1 % u + x$2 % v) x' ==> x = x')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^N`; `v:real^N`; `(x:real^2)$1 - (x':real^2)$1`;
                 `(x:real^2)$2 - (x':real^2)$2`] MOI_S27_NONCOLLINEAR_INDEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2)$1 % (u:real^N) + x$2 % v = (x':real^2)$1 % u + x'$2 % v` THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN REAL_ARITH_TAC]);;

let MOI_S27_STD_TRIANGLE = prove
 (`~collinear{vec 0:real^2,basis 1,basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let MOI_S27_BASIS_NONCOLLINEAR = prove
 (`2 <= dimindex(:N) ==> ~collinear{vec 0:real^N,basis 1,basis 2}`,
  DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    X_GEN_TAC `r:real` THEN DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$2`) THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `1 <= 2 /\ 2 <= dimindex(:N)`
     (fun th -> SIMP_TAC[BASIS_COMPONENT; th; ARITH]) THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

let MOI_S27_SIMPLEX_DIMINDEX = prove
 (`!k:real^N->bool. &2 simplex k ==> 2 <= dimindex(:N)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* Every 2-simplex of real^N is an injective affine image of the standard  *)
(* triangle of the plane.                                                   *)

let MOI_S27_STD_SIMPLEX_2 = prove
 (`&2 simplex (convex hull {vec 0:real^2,basis 1,basis 2})`,
  REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] THEN
  REWRITE_TAC[MOI_S27_STD_TRIANGLE]);;

let MOI_S27_SIMPLEX_FROM_PLANE = prove
 (`!k:real^N->bool.
     &2 simplex k
     ==> ?k0:real^2->bool h h'.
           &2 simplex k0 /\ pl_homeomorphism (k0,k) (h,h') /\
           IMAGE h (relative_frontier k0) = relative_frontier k`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `~collinear{vec 0:real^N,a - b,c - b}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(a:real^N) - b`; `(c:real^N) - b`] MOI_S27_PLANE_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. (x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)) + b)
          (convex hull {vec 0:real^2,basis 1,basis 2}) = convex hull {a,b,c}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^2. x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)`;
                   `b:real^N`; `{vec 0:real^2,basis 1,basis 2}`]
      MOI_REAL_AFFINE_IMAGE_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID;
                VECTOR_ADD_RID; VECTOR_SUB_ADD] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)`;
                 `b:real^N`; `&2:int`;
                 `convex hull {vec 0:real^2,basis 1,basis 2}`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_S27_STD_SIMPLEX_2]; ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {vec 0:real^2,basis 1,basis 2}`;
    `\x:real^2. (x$1 % ((a:real^N) - b) + x$2 % ((c:real^N) - b)) + b`;
    `h':real^N->real^2`] THEN
  ASM_REWRITE_TAC[MOI_S27_STD_SIMPLEX_2]);;

(* Every 2-simplex of the plane maps onto a 2-simplex of real^N, N >= 2.    *)

let MOI_S27_SIMPLEX_TO_SPACE = prove
 (`!k0:real^2->bool.
     &2 simplex k0 /\ 2 <= dimindex(:N)
     ==> ?k:real^N->bool h h'.
           &2 simplex k /\ pl_homeomorphism (k0,k) (h,h') /\
           IMAGE h (relative_frontier k0) = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S27_PLANE_LINEAR
   (MATCH_MP MOI_S27_BASIS_NONCOLLINEAR (ASSUME `2 <= dimindex(:N)`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^2. x$1 % basis 1 + x$2 % basis 2:real^N`;
                 `vec 0:real^N`; `&2:int`; `k0:real^2->bool`]
    MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (\x:real^2. (x$1 % basis 1 + x$2 % basis 2) + vec 0:real^N) k0`;
    `\x:real^2. (x$1 % basis 1 + x$2 % basis 2) + vec 0:real^N`;
    `h':real^N->real^2`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Polygons in the square annulus model                                      *)
(*   A0 = [-2,2]^2 minus the open square (-1,1)^2 (the hole)                 *)
(* of pl_annulus.  The hole lies in one component of the complement of J;   *)
(* if J does not enclose the origin, J with its inside is a PL 2-ball in A0 *)
(* with frontier J; if it does, J winds once around the origin and carries  *)
(* every loop of A0.                                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S27_ORIGIN_IN_HOLE = prove
 (`(vec 0:real^2) IN interval(--vector[&1;&1],vector[&1;&1]) /\
   ~((vec 0:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                       interval(--vector[&1;&1],vector[&1;&1]))`,
  REWRITE_TAC[MOI_FH1_SQUARE_ANNULUS_INFNORM; INFNORM_0] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S27_HOLE_COMPONENT = prove
 (`!J:real^2->bool.
     J SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
              interval(--vector[&1;&1],vector[&1;&1])
     ==> !x. x IN interval(--vector[&1;&1],vector[&1;&1])
             ==> connected_component ((:real^2) DIFF J) (vec 0) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  ASM_REWRITE_TAC[MOI_S27_ORIGIN_IN_HOLE] THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL] THEN ASM SET_TAC[]);;

let MOI_S27_PLANE_CELL = prove
 (`!J:real^2->bool.
     pl_sphere 1 J /\
     J SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
              interval(--vector[&1;&1],vector[&1;&1]) /\
     ~(vec 0 IN inside J)
     ==> pl_ball 2 (J UNION inside J) /\
         J UNION inside J SUBSET
           interval[--vector[&2;&2],vector[&2;&2]] DIFF
           interval(--vector[&1;&1],vector[&1;&1]) /\
         frontier(J UNION inside J) = J`,
  REPEAT STRIP_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
    DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC MOI_PL2_FRONTIER_JORDAN_REGION THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `inside J SUBSET interval[--vector[&2;&2]:real^2,vector[&2;&2]]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_INTERVAL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^2. x IN interval(--vector[&1;&1],vector[&1;&1])
               ==> ~(x IN inside J)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((vec 0:real^2) IN inside J)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
    MP_TAC(ISPEC `J:real^2->bool` MOI_S27_HOLE_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Powers of a loop, and a loop in path_image c with any integral winding  *)
(* number when c winds once (in either sense) around z.                     *)

let MOI_S27_LOOP_POWERS = prove
 (`!(c:real^1->real^2) z.
     path c /\ pathfinish c = pathstart c /\ ~(z IN path_image c)
     ==> !n. ?h. path h /\ pathstart h = pathstart c /\
                 pathfinish h = pathstart c /\ path_image h SUBSET path_image c /\
                 winding_number(h,z) = Cx(&n) * winding_number(c,z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathstart(c:real^1->real^2) IN path_image c` ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_IN_PATH_IMAGE]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `linepath(pathstart c:real^2,pathstart c)` THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET;
                    COMPLEX_MUL_LZERO] THEN
    MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^1->real^2) ++ c` THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN;
               UNION_SUBSET; SUBSET_REFL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN CONV_TAC COMPLEX_RING);;

let MOI_S27_LOOP_WITH_WINDING = prove
 (`!(c:real^1->real^2) z w.
     path c /\ pathfinish c = pathstart c /\ ~(z IN path_image c) /\
     (winding_number(c,z) = Cx(&1) \/ winding_number(c,z) = --Cx(&1)) /\
     complex_integer w
     ==> ?h. path h /\ pathfinish h = pathstart h /\
             path_image h SUBSET path_image c /\ winding_number(h,z) = w`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES) THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `z:real^2`] MOI_S27_LOOP_POWERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC o
    SPEC `n:num`) THEN
  SUBGOAL_THEN `~((z:real^2) IN path_image h)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `winding_number(h,z) = w \/ winding_number(reversepath h,z) = w`
  MP_TAC THENL
   [ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
    ((DISJ1_TAC THEN CONV_TAC COMPLEX_RING) ORELSE
     (DISJ2_TAC THEN CONV_TAC COMPLEX_RING));
    ALL_TAC] THEN
  UNDISCH_TAC
   `winding_number(h:real^1->real^2,z) = Cx(&n) * winding_number(c,z)` THEN
  DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THENL
   [EXISTS_TAC `h:real^1->real^2` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `reversepath h:real^1->real^2` THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH]]);;

(* The radial projection to the inner square deforms each loop of A0.      *)

let MOI_S27_A0_DEFORM = prove
 (`!g:real^1->real^2.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
                         interval(--vector[&1;&1],vector[&1;&1])
     ==> homotopic_loops (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1]))
           g ((\x:real^2. (&1 * inv(infnorm x)) % x) o g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&1` MOI_FH1_ANNULUS_RETRACT) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; o_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1])` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC
   `path_image (g:real^1->real^2) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1])` THEN
  UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[path_image] THEN SET_TAC[]);;

(* Loops of A0 with the same winding number around the origin are           *)
(* homotopic in A0.                                                          *)

let MOI_S27_A0_HOMOTOPIC_WINDING = prove
 (`!p q:real^1->real^2.
     path p /\ pathfinish p = pathstart p /\
     path_image p SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
                         interval(--vector[&1;&1],vector[&1;&1]) /\
     path q /\ pathfinish q = pathstart q /\
     path_image q SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
                         interval(--vector[&1;&1],vector[&1;&1]) /\
     winding_number(p,vec 0) = winding_number(q,vec 0)
     ==> homotopic_loops (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1])) p q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `q:real^1->real^2`; `vec 0:real^2`]
    WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC MOI_S27_ORIGIN_IN_HOLE THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPEC `&1` MOI_FH1_ANNULUS_RETRACT) THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^2. (&1 * inv(infnorm x)) % x) continuous_on ((:real^2) DELETE vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FH1_CONTINUOUS_ON_INFNORM_SCALE THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV; INFNORM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. (&1 * inv(infnorm x)) % x) ((:real^2) DELETE vec 0) SUBSET
    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SIMP_TAC[MOI_FH1_SQUARE_FRONTIER_INFNORM; REAL_LT_01] THEN
    REWRITE_TAC[INFNORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_INFNORM;
                REAL_ABS_NUM; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[INFNORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]))
      ((\x:real^2. (&1 * inv(infnorm x)) % x) o (p:real^1->real^2))
      ((\x:real^2. (&1 * inv(infnorm x)) % x) o (q:real^1->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `(:real^2) DELETE vec 0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(\x:real^2. (&1 * inv(infnorm x)) % x) o (p:real^1->real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S27_A0_DEFORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(\x:real^2. (&1 * inv(infnorm x)) % x) o (q:real^1->real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
    MATCH_MP_TAC MOI_S27_A0_DEFORM THEN ASM_REWRITE_TAC[]]);;

(* A PL circle in A0 enclosing the origin carries every loop of A0.        *)

let MOI_S27_PLANE_CARRIED = prove
 (`!J:real^2->bool.
     pl_sphere 1 J /\
     J SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
              interval(--vector[&1;&1],vector[&1;&1]) /\
     vec 0 IN inside J
     ==> loops_carried J (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1]))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ABBREV_TAC `c = polygonal_path(pp:(real^2)list)` THEN
  SUBGOAL_THEN `path(c:real^1->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN path_image c)` ASSUME_TAC THENL
   [MP_TAC MOI_S27_ORIGIN_IN_HOLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `winding_number(c,vec 0) = Cx(&1) \/ winding_number(c,vec 0) = --Cx(&1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^1->real^2` SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[loops_carried] THEN X_GEN_TAC `p:real^1->real^2` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN path_image p)` ASSUME_TAC THENL
   [MP_TAC MOI_S27_ORIGIN_IN_HOLE THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^1->real^2`; `vec 0:real^2`;
                 `winding_number(p:real^1->real^2,vec 0)`]
    MOI_S27_LOOP_WITH_WINDING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:real^1->real^2` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S27_A0_HOMOTOPIC_WINDING THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transport between the PL annulus a in real^N and the model A0 in real^2,  *)
(* and the theorem MOISE_273.                                                *)
(* ------------------------------------------------------------------------- *)

(* A PL homeomorphism of a 2-simplex restricts to its relative frontier     *)
(* (as MOI_CEL_PLH_SIMPLEX_RF of pc_moi_cells.ml, for dimension 2).         *)

let MOI_S27_PLH_SIMPLEX_RF = prove
 (`!(k:real^M->bool) (s:real^N->bool) f g.
     &2 simplex k /\ pl_homeomorphism (k,s) (f,g)
     ==> pl_homeomorphism (relative_frontier k,IMAGE f (relative_frontier k))
                          (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MP_TAC(ISPECL [`k:real^M->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]]);;

(* Homeomorphisms transport loops_carried.                                   *)

let MOI_S27_LOOPS_CARRIED_HOMEO = prove
 (`!(m:real^M->bool) (s:real^N->bool) k f g.
     homeomorphism (m,s) (f,g) /\ k SUBSET m /\ loops_carried k m
     ==> loops_carried (IMAGE f k) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN
  REWRITE_TAC[loops_carried] THEN X_GEN_TAC `p:real^1->real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `path ((g:real^N->real^M) o (p:real^1->real^N)) /\
    pathfinish (g o p) = pathstart (g o p) /\ path_image (g o p) SUBSET m`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [loops_carried]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^N->real^M) o (p:real^1->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) o (q:real^1->real^M)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `m:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(f:real^M->real^N) o (g:real^N->real^M) o (p:real^1->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET s` THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[path_image] THEN SET_TAC[];
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `m:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

(* The PL circle j in a goes to a PL circle in A0.                          *)

let MOI_S27_SPHERE_TO_PLANE = prove
 (`!(a:real^N->bool) (j:real^N->bool) f g.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     pl_sphere 1 j /\ j SUBSET a
     ==> pl_sphere 1 (IMAGE g j) /\
         IMAGE g j SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1]) /\
         IMAGE f (IMAGE g j) = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (IMAGE g j) = j` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^2) j SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1])`
  ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_sphere 1 (j:real^N->bool)` THEN
  REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k0,relative_frontier k)
                     ((h:real^2->real^N),(h':real^N->real^2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (h:real^2->real^N) (relative_frontier k0) = relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S27_PLH_SIMPLEX_RF THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (j,IMAGE (g:real^N->real^2) j) (g,(f:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`a:real^N->bool`;
      `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `j = IMAGE (F1:real^N->real^N) (relative_frontier k)`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  EXISTS_TAC `k0:real^2->bool` THEN
  EXISTS_TAC `(g:real^N->real^2) o (F1:real^N->real^N) o (h:real^2->real^N)` THEN
  EXISTS_TAC `((h':real^N->real^2) o (G1:real^N->real^N)) o (f:real^2->real^N)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* A PL 2-ball d in A0 with frontier g(j) gives the PL 2-cell f(d) in a.    *)

let MOI_S27_CELL_FROM_PLANE = prove
 (`!(a:real^N->bool) (j:real^N->bool) f g d.
     pl_homeomorphism
       (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
        interval(--vector[&1;&1]:real^2,vector[&1;&1]),a) (f,g) /\
     pl_ball 2 d /\
     d SUBSET interval[--vector[&2;&2],vector[&2;&2]] DIFF
              interval(--vector[&1;&1],vector[&1;&1]) /\
     frontier d = IMAGE g j /\ j SUBSET a /\ 2 <= dimindex(:N)
     ==> pl_cell_with_boundary 2 (IMAGE f d) j /\ IMAGE f d SUBSET a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `pl_ball 2 (d:real^2->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^2`
    (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k1:real^2->bool`; `d:real^2->bool`; `f1:real^2->real^2`;
                 `g1:real^2->real^2`] MOI_PL2_FRONTIER_PL_BALL_2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k1:real^2->bool` MOI_S27_SIMPLEX_TO_SPACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^N->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (d,IMAGE (f:real^2->real^N) d) (f,(g:real^N->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`; `a:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `d = IMAGE (f1:real^2->real^2) k1` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((f:real^2->real^N) o (f1:real^2->real^2) o (h':real^N->real^2))
          (relative_frontier kk) = j`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `relative_frontier k1 SUBSET (k1:real^2->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN (k1:real^2->bool) ==> (h':real^N->real^2) (h x) = x`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC
     `IMAGE (h:real^2->real^N) (relative_frontier k1) = relative_frontier kk` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `IMAGE (h':real^N->real^2) (IMAGE (h:real^2->real^N) (relative_frontier k1)) =
      relative_frontier k1`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `IMAGE (g:real^N->real^2) j = IMAGE (f1:real^2->real^2) (relative_frontier k1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  EXISTS_TAC `kk:real^N->bool` THEN
  EXISTS_TAC `(f:real^2->real^N) o (f1:real^2->real^2) o (h':real^N->real^2)` THEN
  EXISTS_TAC `((h:real^2->real^N) o (g1:real^2->real^2)) o (g:real^N->real^2)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: Moise 27.3.                                             *)
(* ------------------------------------------------------------------------- *)

let MOISE_273 = prove
 (`!u:N->bool. MOISE_273_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOISE_273_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `j:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_annulus]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_TAC `g:real^N->real^2`)) THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_sphere 1 (j:real^N->bool)` THEN
    REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
    MESON_TAC[MOI_S27_SIMPLEX_DIMINDEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `j:real^N->bool`; `f:real^2->real^N`;
                 `g:real^N->real^2`] MOI_S27_SPHERE_TO_PLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(vec 0:real^2) IN inside(IMAGE (g:real^N->real^2) j)` THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPEC `IMAGE (g:real^N->real^2) j` MOI_S27_PLANE_CARRIED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `j = IMAGE (f:real^2->real^N) (IMAGE g j)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S27_LOOPS_CARRIED_HOMEO THEN
    MAP_EVERY EXISTS_TAC
     [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`; `g:real^N->real^2`] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    DISJ1_TAC THEN
    MP_TAC(ISPEC `IMAGE (g:real^N->real^2) j` MOI_S27_PLANE_CELL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N)
                      (IMAGE g j UNION inside(IMAGE (g:real^N->real^2) j))` THEN
    MATCH_MP_TAC MOI_S27_CELL_FROM_PLANE THEN
    EXISTS_TAC `g:real^N->real^2` THEN ASM_REWRITE_TAC[]]);;

