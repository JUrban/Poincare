needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_tubed.ml";;
needs "src/pc_moi_fnd_tubeb.ml";;
needs "src/pc_moi_fnd_rn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s33_frame: the basic facts of the canonical tube N = derived_nbhd *)
(* t l and of its image under the embedding h (Moise GTM 47, 33.1 p.223,    *)
(* p.234).  Main theorem                                                    *)
(*   TUBE_FACTS : |- MOI_S33_TUBE_FACTS   (pc_moi_s33_stmt.ml)              *)
(* (Lemma 2, MOI_S33_X2, is proved in pc_moi_s33_x2.)  Route: the frontier  *)
(* and interior clauses from GRAPH_TUBE_FRONTIER_3 and invariance of        *)
(* domain; R^3 - h(N) is connected by Borsuk separation, since h(N) is      *)
(* homotopy equivalent to the graph |l| (deformation retraction             *)
(* DERIVED_NBHD_DEFORMATION_RETRACT) and every map from a finite union of   *)
(* segments into S^2 is inessential (polynomial approximation and a         *)
(* negligible cone, MOI_S3FR_SEGMENTS_SPHEREMAP); Bd N is connected by      *)
(* unicoherence (CONNECTED_FRONTIER_SIMPLE, with h = identity) and locally  *)
(* path connected (a finite union of simplices); W is the product           *)
(* GRAPH_TUBE_PRODUCT on Bd N x (0,1) followed by h.  General lemmas:       *)
(* MOI_S3FR_SEGMENTS_SPHEREMAP, MOI_S3FR_COMPLEMENT_CONNECTED.              *)
(* ========================================================================= *)


(* Basic facts of the canonical tube.                                        *)

let MOI_S3FR_TUBE_BASIC = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> FINITE l /\ graph_in_complex t l /\ lf_simplicial_complex t /\ FINITE t /\
         l SUBSET t /\
         frontier (derived_nbhd t l) = derived_frontier t l /\
         interior (derived_nbhd t l) = derived_nbhd t l DIFF derived_frontier t l /\
         UNIONS l SUBSET interior (derived_nbhd t l) /\
         compact (derived_nbhd t l) /\ derived_nbhd t l SUBSET UNIONS t /\
         derived_nbhd t l SUBSET interior (UNIONS t) /\
         derived_frontier t l SUBSET derived_nbhd t l /\
         compact (UNIONS l) /\ UNIONS l SUBSET UNIONS t /\
         h continuous_on UNIONS t /\
         (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_tube] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex]) THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_TUBE_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhand (concl th) = `interior (derived_nbhd (t:(real^3->bool)->bool) l)`)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS l:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(derived_nbhd t l) = derived_nbhd t (l:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `derived_frontier t l SUBSET derived_nbhd t (l:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `frontier (derived_nbhd (t:(real^3->bool)->bool) l)`)) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (derived_nbhd t l) =
                derived_nbhd t l DIFF derived_frontier t (l:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `frontier (derived_nbhd (t:(real^3->bool)->bool) l)`)) THEN
    REWRITE_TAC[frontier] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhand (concl th) = `closure (derived_nbhd (t:(real^3->bool)->bool) l)`)) THEN
    MP_TAC(ISPEC `derived_nbhd (t:(real^3->bool)->bool) l` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTB_NBHD_INTERIOR]);;

let MOI_S3FR_DUAL_COMPACT = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h ==> !v. compact (derived_dual_cell t l v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  REWRITE_TAC[derived_dual_cell] THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GRAPH_IN_COMPLEX_BARYCENTRIC; graph_in_complex]]);;


(* The image of the tube under h: interior, frontier and the graph inside.   *)

let MOI_S3FR_IMAGE_FACTS = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> compact (IMAGE h (UNIONS l)) /\ compact (IMAGE h (derived_nbhd t l)) /\
         interior (IMAGE h (derived_nbhd t l)) =
         IMAGE h (derived_nbhd t l DIFF derived_frontier t l) /\
         frontier (IMAGE h (derived_nbhd t l)) = IMAGE h (derived_frontier t l) /\
         IMAGE h (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  ABBREV_TAC `N = derived_nbhd (t:(real^3->bool)->bool) l` THEN
  ABBREV_TAC `B = derived_frontier (t:(real^3->bool)->bool) l` THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) N) /\ compact (IMAGE h (UNIONS l))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (IMAGE (h:real^3->real^3) N) = IMAGE h (N DIFF B)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (h:real^3->real^3) N` MP_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
      UNDISCH_TAC `(h:real^3->real^3) x IN interior (IMAGE h N)` THEN
      REWRITE_TAC[IN_INTERIOR] THEN
      DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
      (* continuity of h at x within |t| *)
      UNDISCH_TAC `(h:real^3->real^3) continuous_on UNIONS t` THEN
      REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
      (* x is interior to |t| *)
      SUBGOAL_THEN `(x:real^3) IN interior (UNIONS t)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERIOR] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      (* every point near x is in N, so x is interior to N, not on Bd N *)
      SUBGOAL_THEN `(x:real^3) IN interior N` MP_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[IN_DIFF]] THEN
      REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min dl r` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN UNIONS t` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(x:real^3,r) SUBSET UNIONS t` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(h:real^3->real^3) z IN IMAGE h N` MP_TAC THENL
       [UNDISCH_TAC `ball((h:real^3->real^3) x,ee) SUBSET IMAGE h N` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^3) = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
          lhand (concl th) = `interior N:real^3->bool`)) THEN
        REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^3->bool` THEN
          ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN
          ASM SET_TAC[];
          MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `!x y:real^3. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^3->real^3) x = h y ==> x = y` THEN
    UNDISCH_TAC `(N:real^3->bool) SUBSET UNIONS t` THEN
    UNDISCH_TAC `(B:real^3->bool) SUBSET N` THEN SET_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Maps from a finite union of segments into the unit sphere of real^N,     *)
(* 3 <= dimindex(:N), are inessential: a polynomial approximation g within  *)
(* 1/2 gives the radial projection p = g / |g|, never antipodal to f; p     *)
(* misses a point of the sphere, since otherwise the ball of radius 1/2     *)
(* would lie in the union of the cones {r g(x)} over the segments, which    *)
(* are polynomial images of the plane, hence negligible.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3FR_UNIT_SCALE = prove
 (`!y:real^N. ?a. a IN sphere(vec 0,&1) /\ norm y % a = y`,
  GEN_TAC THEN ASM_CASES_TAC `y:real^N = vec 0` THENL
   [EXISTS_TAC `basis 1:real^N` THEN
    ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_GE_1; LE_REFL; NORM_0;
                 VECTOR_MUL_LZERO];
    EXISTS_TAC `inv(norm y) % y:real^N` THEN
    ASM_SIMP_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
                 NORM_EQ_0; VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID]]);;

let MOI_S3FR_NONANTIPODAL_AUX = prove
 (`!u v:real^N. norm(u - v) < inv(&2) /\ inv(&2) < norm v
                ==> ~(u = --(inv(norm v) % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `norm(--(inv(norm v) % v) - v:real^N) < inv(&2)` THEN
  REWRITE_TAC[VECTOR_ARITH `--(c % y) - y:real^N = --((c + &1) % y)`; NORM_NEG;
              NORM_MUL] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(norm(v:real^N)) + &1) = inv(norm v) + &1` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(x + &1) = x + &1`) THEN
    ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3FR_SEG_CONE_NEGLIGIBLE = prove
 (`!(g:real^M->real^N) (a:real^M) b.
     vector_polynomial_function g /\ 2 < dimindex(:N)
     ==> negligible (IMAGE (\z:real^2. z$2 % g(a + z$1 % (b - a))) (:real^2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_VECTOR_POLYNOMIAL_FUNCTION THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> vector_polynomial_function (\z:real^2. lift(z$i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^2. x`; `i:num`] VECTOR_POLYNOMIAL_FUNCTION_COMPONENT) THEN
    ASM_REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_ID; DIMINDEX_2];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. (g:real^M->real^N) (a + z$1 % (b - a))) =
                g o (\z. a + z$1 % (b - a))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_o THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_ADD THEN
  REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST] THEN
  MATCH_MP_TAC VECTOR_POLYNOMIAL_FUNCTION_MUL THEN
  REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_CONST; o_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let MOI_S3FR_SEGMENTS_SPHEREMAP = prove
 (`!(f:real^M->real^N) s.
     FINITE s /\ (!k. k IN s ==> ?a b. k = segment[a,b]) /\ 3 <= dimindex(:N) /\
     f continuous_on UNIONS s /\ IMAGE f (UNIONS s) SUBSET sphere(vec 0,&1)
     ==> ?c. homotopic_with (\x. T)
               (subtopology euclidean (UNIONS s),subtopology euclidean (sphere(vec 0,&1)))
               f (\x. c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS s:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_SEGMENT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    check (fun th -> can (term_match []
      `!k:real^M->bool. k IN s ==> ?a b. k = segment[a,b]`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(real^M->bool)->real^M`
    (X_CHOOSE_THEN `B:(real^M->bool)->real^M` (ASSUME_TAC o GSYM))) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `UNIONS s:real^M->bool`; `inv(&2)`]
    STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. x IN UNIONS s ==> norm((f:real^M->real^N) x) = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) x IN sphere(vec 0,&1)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN UNIONS s ==> inv(&2) < norm((g:real^M->real^N) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `norm((f:real^M->real^N) x) = &1 /\
                  norm(f x - (g:real^M->real^N) x) < inv(&2)` MP_TAC THENL
     [ASM_SIMP_TAC[]; CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `p = \x:real^M. inv(norm((g:real^M->real^N) x)) % g x` THEN
  SUBGOAL_THEN `(p:real^M->real^N) continuous_on UNIONS s` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION; ETA_AX] THEN
    MP_TAC(REWRITE_RULE[o_DEF] (ISPECL
      [`\x:real^M. norm((g:real^M->real^N) x)`; `UNIONS s:real^M->bool`]
      CONTINUOUS_ON_INV)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `inv(&2) < norm((g:real^M->real^N) x)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN UNIONS s ==> norm((p:real^M->real^N) x) = &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN
    SUBGOAL_THEN `inv(&2) < norm((g:real^M->real^N) x)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^M->real^N) (UNIONS s) SUBSET sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* f and p are homotopic: never antipodal *)
  SUBGOAL_THEN
   `homotopic_with (\x. T)
      (subtopology euclidean (UNIONS s),subtopology euclidean (sphere(vec 0,&1)))
      (f:real^M->real^N) p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_NON_ANTIPODAL_SPHEREMAPS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXPAND_TAC "p" THEN
    MATCH_MP_TAC MOI_S3FR_NONANTIPODAL_AUX THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* p misses a point of the sphere *)
  SUBGOAL_THEN `?a:real^N. a IN sphere(vec 0,&1) /\ ~(a IN IMAGE (p:real^M->real^N) (UNIONS s))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    MP_TAC(ISPEC `ball(vec 0:real^N,inv(&2))` OPEN_NOT_NEGLIGIBLE) THEN
    ANTS_TAC THENL [REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
                    ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `UNIONS (IMAGE (\k:real^M->bool.
                  IMAGE (\z:real^2. z$2 % (g:real^M->real^N)
                                     ((A:(real^M->bool)->real^M) k +
                                      z$1 % ((B:(real^M->bool)->real^M) k - A k)))
                        (:real^2)) s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3FR_SEG_CONE_NEGLIGIBLE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `y:real^N` MOI_S3FR_UNIT_SCALE) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N` o check (fun th -> can (term_match []
      `!a:real^N. a IN sphere(vec 0,&1) ==> a IN IMAGE (p:real^M->real^N) (UNIONS s)`)
      (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^M) IN segment[(A:(real^M->bool)->real^M) k,B k]` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vector[u; norm(y:real^N) * inv(norm((g:real^M->real^N) x))]:real^2` THEN
    REWRITE_TAC[VECTOR_2] THEN
    SUBGOAL_THEN `(A:(real^M->bool)->real^M) k + u % (B k - A k) = x` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(y:real^N) % (e:real^N)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `e:real^N = (p:real^M->real^N) x`)) THEN
    EXPAND_TAC "p" THEN REWRITE_TAC[VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^M->real^N`; `UNIONS s:real^M->bool`;
                 `sphere(vec 0:real^N,&1) DELETE a`] NULLHOMOTOPIC_INTO_CONTRACTIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`IMAGE (p:real^M->real^N) (UNIONS s) SUBSET sphere(vec 0,&1)`;
        `~((a:real^N) IN IMAGE (p:real^M->real^N) (UNIONS s))`] THEN
      SET_TAC[];
      MATCH_MP_TAC CONTRACTIBLE_PUNCTURED_SPHERE THEN ASM_REWRITE_TAC[REAL_LT_01]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` ASSUME_TAC) THEN
  EXISTS_TAC `c:real^N` THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `p:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN
  EXISTS_TAC `sphere(vec 0:real^N,&1) DELETE a` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Complements: a compact set of real^N (3 <= dimindex(:N)) homotopy        *)
(* equivalent to a finite union of segments does not separate real^N        *)
(* (Borsuk separation with MOI_S3FR_SEGMENTS_SPHEREMAP, cobounded sets have *)
(* one unbounded component).  Note: the dimension criterion of degree.ml    *)
(* (complements of sets of dimension <= n-2) does not apply to the tube.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3FR_COMPLEMENT_CONNECTED = prove
 (`!(S:real^N->bool) (k:(real^M->bool)->bool).
     compact S /\ 3 <= dimindex(:N) /\ FINITE k /\
     (!c. c IN k ==> ?a b. c = segment[a,b]) /\
     S homotopy_equivalent UNIONS k
     ==> connected((:real^N) DIFF S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c. c IN components((:real^N) DIFF S) ==> ~bounded c` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^N->bool` BORSUK_SEPARATION_THEOREM_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`S:real^N->bool`; `UNIONS k:real^M->bool`; `sphere(vec 0:real^N,&1)`]
      HOMOTOPY_EQUIVALENT_COHOMOTOPIC_TRIVIALITY_NULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3FR_SEGMENTS_SPHEREMAP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DIFF S`; `x:real^N`; `y:real^N`]
    COBOUNDED_UNIQUE_UNBOUNDED_COMPONENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[SET_RULE `(:real^N) DIFF ((:real^N) DIFF S) = S`] THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_COMPONENTS] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_COMPONENTS] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ]);;

(* Nonempty simplices of dimension at most 1 are segments. *)

let MOI_S3FR_SIMPLEX_SEGMENT = prove
 (`!(s:real^N->bool) n. n simplex s /\ aff_dim s <= &1 /\ ~(s = {})
                        ==> ?a b. s = segment[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
  ASM_REWRITE_TAC[COLLINEAR_AFF_DIM] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX]);;

let MOI_S3FR_TUBE_NONEMPTY = prove
 (`!(t:(real^3->bool)->bool) l h. moi_s33_tube t l h ==> ~(UNIONS l = {})`,
  REWRITE_TAC[moi_s33_tube] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^3->bool) = -- &1` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_S3FR_TUBE_SEGMENTS = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> FINITE {c | c IN l /\ ~(c = {})} /\
         (!c. c IN {c | c IN l /\ ~(c = {})} ==> ?a b. c = segment[a,b]) /\
         UNIONS {c | c IN l /\ ~(c = {})} = UNIONS l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3FR_SIMPLEX_SEGMENT THEN
    SUBGOAL_THEN `aff_dim(c:real^3->bool) <= &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1(GEN_REWRITE_RULE I [lf_simplicial_complex]
      (ASSUME `lf_simplicial_complex (t:(real^3->bool)->bool)`))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    SET_TAC[]]);;

(* The tube and its image are homotopy equivalent to the graph. *)

let MOI_S3FR_TUBE_HEQ = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> derived_nbhd t l homotopy_equivalent UNIONS l /\
         IMAGE h (derived_nbhd t l) homotopy_equivalent UNIONS l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `derived_nbhd t l homotopy_equivalent (UNIONS l:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      DERIVED_NBHD_DEFORMATION_RETRACT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `r:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\h:real^3->real^3. !x. x IN UNIONS l ==> h x = x` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (derived_nbhd t l)`;
                       `derived_nbhd t (l:(real^3->bool)->bool)`; `UNIONS l:real^3->bool`]
    HOMOTOPY_EQUIVALENT_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  EXISTS_TAC `h:real^3->real^3` THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]]);;

let MOI_S3FR_TUBE_COMPLEMENTS = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> connected((:real^3) DIFF derived_nbhd t l) /\
         connected((:real^3) DIFF IMAGE h (derived_nbhd t l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_SEGMENTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_HEQ) THEN
  CONJ_TAC THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:M`] MOI_S3FR_COMPLEMENT_CONNECTED) THEN
  EXISTS_TAC `{c | c IN l /\ ~(c = {})}:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[DIMINDEX_3; LE_REFL] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]);;

(* Bd N is path connected and nonempty: N and its complement are connected, *)
(* so its frontier is (unicoherence, CONNECTED_FRONTIER_SIMPLE), and Bd N   *)
(* is a finite union of simplices, hence locally path connected.            *)

let MOI_S3FR_TUBE_FRONTIER_CONNECTED = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> path_connected (derived_frontier t l) /\ ~(derived_frontier t l = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_HEQ) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_COMPLEMENTS) THEN
  SUBGOAL_THEN `connected (UNIONS l:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_tube]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  (* the graph is path connected *)
  SUBGOAL_THEN `path_connected (UNIONS l:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS l:real^3->bool` PATH_CONNECTED_EQ_CONNECTED_LPC) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ANR_IMP_LOCALLY_PATH_CONNECTED THEN
      MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `polytope (c:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
        ASM SET_TAC[];
        MESON_TAC[POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_CONVEX]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Bd N is locally path connected *)
  SUBGOAL_THEN `locally path_connected (derived_frontier t l:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      MOI_FTD_NBHD_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[complex_boundary] THEN
    MATCH_MP_TAC ANR_IMP_LOCALLY_PATH_CONNECTED THEN
    MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `polytope (c:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN
      EXISTS_TAC `derived_nbhd_complex t (l:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_frontier t l = frontier(derived_nbhd t (l:(real^3->bool)->bool))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `connected(frontier(derived_nbhd t (l:(real^3->bool)->bool)))`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_FRONTIER_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
      MP_TAC(ISPECL [`derived_nbhd t (l:(real^3->bool)->bool)`; `UNIONS l:real^3->bool`]
        HOMOTOPY_EQUIVALENT_PATH_CONNECTEDNESS) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> q ==> p`) THEN
    MATCH_MP_TAC PATH_CONNECTED_EQ_CONNECTED_LPC THEN
    UNDISCH_TAC `locally path_connected (derived_frontier t l:real^3->bool)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!u i (n:real^3->bool). ~(u = {}) /\ u SUBSET i /\ i SUBSET n ==> ~(n = {})`) THEN
      MAP_EVERY EXISTS_TAC
       [`UNIONS l:real^3->bool`; `interior(derived_nbhd t (l:(real^3->bool)->bool))`] THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN ASM_MESON_TAC[MOI_S3FR_TUBE_NONEMPTY];
      ASM_MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]]]);;


(* ------------------------------------------------------------------------- *)
(* The open collar W: a product structure Bd N x [0,1) onto N - |l| with    *)
(* level 0 the identity of Bd N restricts to Bd N x (0,1) onto N - Bd N - |l|; *)
(* composing with the embedding h of N gives W = Int h(N) - h|l|.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3FR_COLLAR_OPEN_PART = prove
 (`!(f0:real^(N,1)finite_sum->real^N) g0 (h:real^N->real^M) k N B L.
     homeomorphism (B PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}, N DIFF L)
                   (f0,g0) /\
     (!y. y IN B ==> f0(pastecart y (vec 0)) = y) /\
     homeomorphism (N,IMAGE h N) (h,k) /\ B SUBSET N /\ L SUBSET N /\ DISJOINT B L
     ==> homeomorphism (B PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},
                        IMAGE h (N DIFF B) DIFF IMAGE h L) (h o f0,g0 o k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `(N DIFF B) DIFF L:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(B:real^N->bool) PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}`;
                          `N DIFF L:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(GEN_REWRITE_RULE I [homeomorphism] (ASSUME
      `homeomorphism (B PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}, N DIFF L)
                     (f0:real^(N,1)finite_sum->real^N,g0)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(B:real^N->bool) PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1} =
      (B:real^N->bool) PCROSS {vec 0} UNION
      B PCROSS {x:real^1 | &0 < drop x /\ drop x < &1} /\
      DISJOINT ((B:real^N->bool) PCROSS {vec 0:real^1})
               (B PCROSS {x:real^1 | &0 < drop x /\ drop x < &1})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM PCROSS_UNION; DISJOINT_PCROSS] THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM] THEN
        GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
        DISJ2_TAC THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        GEN_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f0:real^(N,1)finite_sum->real^N) (B PCROSS {vec 0}) = B`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f0:real^(N,1)finite_sum->real^N) (B PCROSS {vec 0}) = B`;
      `DISJOINT ((B:real^N->bool) PCROSS {vec 0:real^1})
               (B PCROSS {x:real^1 | &0 < drop x /\ drop x < &1})`;
      `(B:real^N->bool) PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1} =
       (B:real^N->bool) PCROSS {vec 0} UNION
       B PCROSS {x:real^1 | &0 < drop x /\ drop x < &1}`;
      `IMAGE (f0:real^(N,1)finite_sum->real^N)
             (B PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}) = N DIFF L`;
      `!x. x IN B PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}
           ==> (g0:real^N->real^(N,1)finite_sum) ((f0:real^(N,1)finite_sum->real^N) x) = x`] THEN
    SPEC_TAC(`(B:real^N->bool) PCROSS {x:real^1 | &0 < drop x /\ drop x < &1}`,
             `PJ:real^(N,1)finite_sum->bool`) THEN
    SPEC_TAC(`(B:real^N->bool) PCROSS {x:real^1 | &0 <= drop x /\ drop x < &1}`,
             `P0:real^(N,1)finite_sum->bool`) THEN
    SPEC_TAC(`(B:real^N->bool) PCROSS {vec 0:real^1}`,
             `Z:real^(N,1)finite_sum->bool`) THEN
    SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `IMAGE (h:real^N->real^M) N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(GEN_REWRITE_RULE I [homeomorphism] (ASSUME
      `homeomorphism (N,IMAGE (h:real^N->real^M) N) (h,k)`)) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `!x:real^N. x IN N ==> (k:real^M->real^N) (h x) = x` THEN
    UNDISCH_TAC `(L:real^N->bool) SUBSET N` THEN SET_TAC[]]);;

let MOI_S3FR_TUBE_WW = prove
 (`!(t:(real^3->bool)->bool) l h.
     moi_s33_tube t l h
     ==> ?(f:real^(3,1)finite_sum->real^3) g.
           homeomorphism
             (derived_frontier t l PCROSS {x:real^1 | &0 < drop x /\ drop x < &1},
              moi_s33_ww t l h) (f,g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_IMAGE_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_TUBE_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g0:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`derived_nbhd t (l:(real^3->bool)->bool)`; `h:real^3->real^3`;
                 `IMAGE (h:real^3->real^3) (derived_nbhd t l)`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
    DISCH_THEN(X_CHOOSE_TAC `k:real^3->real^3`)] THEN
  MAP_EVERY EXISTS_TAC [`(h:real^3->real^3) o (f0:real^(3,1)finite_sum->real^3)`;
                        `(g0:real^3->real^(3,1)finite_sum) o (k:real^3->real^3)`] THEN
  REWRITE_TAC[moi_s33_ww] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3FR_COLLAR_OPEN_PART THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`UNIONS l SUBSET interior (derived_nbhd t (l:(real^3->bool)->bool))`;
    `interior (derived_nbhd t l) =
     derived_nbhd t l DIFF derived_frontier t (l:(real^3->bool)->bool)`] THEN
  SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The theorem TUBE_FACTS.                                                   *)
(* ------------------------------------------------------------------------- *)

let TUBE_FACTS = prove
 (MOI_S33_TUBE_FACTS,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_IMAGE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_COMPLEMENTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_FRONTIER_CONNECTED) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S3FR_DUAL_COMPACT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S3FR_TUBE_WW) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

