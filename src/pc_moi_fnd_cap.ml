(* ========================================================================= *)
(* pc_moi_fnd_cap: capping a combinatorial surface with boundary.  The       *)
(* surface c in real^N is lifted to real^(N,2) by x |-> (x,0) and each      *)
(* boundary component P is capped by the cone with apex (0,(1,ix P)), the   *)
(* index ix injective on the components: moi_fcb_cap c ix.                   *)
(* Main result MOI_FCB_CAP_CM2: the capped complex is a finite closed       *)
(* combinatorial surface; with the cone geometry (moi_fcb_cone, the union,  *)
(* the intersections with the lifted surface, disjointness, compactness,    *)
(* both sides accumulating on each lifted component).  Used for the          *)
(* boundary collars of pc_moi_fnd_bcollar and for the loop theorem.          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_fnd_surfb0.ml";;
needs "src/pc_moi_fnd_gpb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The lift x |-> pastecart x (vec 0) of real^N into real^(N,2) and cones    *)
(* over lifted convex sets whose apexes moi_fcb_apex i lie on different rays *)
(* of the extra plane: the cone meets the lifted space in its base, two      *)
(* cones with one apex meet in the cone over the common part of the bases,   *)
(* two cones with different apexes meet in the common part of the bases;     *)
(* cones over simplices are simplices with the expected faces.               *)
(* ========================================================================= *)

let moi_fcb_lift = new_definition
 `moi_fcb_lift (x:real^N) = pastecart x (vec 0:real^2)`;;

let moi_fcb_apex = new_definition
 `moi_fcb_apex (i:num) = pastecart (vec 0:real^N) (vector[&1; &i]:real^2)`;;

let MOI_FCB_LIFT = prove
 (`linear (moi_fcb_lift:real^N->real^(N,2)finite_sum) /\
   (!x y:real^N. moi_fcb_lift x = moi_fcb_lift y <=> x = y) /\
   (!x:real^N. fstcart(moi_fcb_lift x) = x /\ sndcart(moi_fcb_lift x) = vec 0)`,
  REWRITE_TAC[moi_fcb_lift; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
  REWRITE_TAC[linear; moi_fcb_lift; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID;
              VECTOR_MUL_RZERO]);;

let MOI_FCB_APEX = prove
 (`!i. fstcart(moi_fcb_apex i:real^(N,2)finite_sum) = vec 0 /\
       sndcart(moi_fcb_apex i:real^(N,2)finite_sum) = vector[&1; &i]`,
  REWRITE_TAC[moi_fcb_apex; FSTCART_PASTECART; SNDCART_PASTECART]);;

(* Points of a cone over a lifted convex set.                                 *)

let MOI_FCB_CONE_POINTS = prove
 (`!i (s:real^N->bool) z.
     convex s /\ ~(s = {})
     ==> (z IN convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) <=>
          ?t x. &0 <= t /\ t <= &1 /\ x IN s /\
                z = (&1 - t) % moi_fcb_lift x + t % moi_fcb_apex i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (moi_fcb_lift:real^N->real^(N,2)finite_sum) s`;
                 `moi_fcb_apex i:real^(N,2)finite_sum`] CONVEX_HULL_INSERT) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `convex hull (IMAGE (moi_fcb_lift:real^N->real^(N,2)finite_sum) s) =
                IMAGE moi_fcb_lift s` SUBST1_TAC THENL
   [SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN ASM_SIMP_TAC[HULL_P];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
      (X_CHOOSE_THEN `b:real^(N,2)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))))))) THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `x:real^N`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `&1 - t`; `moi_fcb_lift (x:real^N):real^(N,2)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      VECTOR_ARITH_TAC]]);;

let MOI_FCB_CONE_SND = prove
 (`!i t (x:real^N).
     fstcart((&1 - t) % moi_fcb_lift x + t % moi_fcb_apex i:real^(N,2)finite_sum) =
     (&1 - t) % x /\
     sndcart((&1 - t) % moi_fcb_lift x + t % moi_fcb_apex i:real^(N,2)finite_sum) =
     t % vector[&1; &i]`,
  REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL; MOI_FCB_LIFT;
              MOI_FCB_APEX] THEN
  VECTOR_ARITH_TAC);;

(* A point of two cones with the same apex.                                   *)

let MOI_FCB_CONE_SAME = prove
 (`!i t t' (x:real^N) x'.
     (&1 - t) % moi_fcb_lift x + t % moi_fcb_apex i:real^(N,2)finite_sum =
     (&1 - t') % moi_fcb_lift x' + t' % moi_fcb_apex i
     ==> t = t' /\ (t < &1 ==> x = x')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `t:real = t'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^(N,2)finite_sum. (sndcart z)$1`) THEN
    REWRITE_TAC[MOI_FCB_CONE_SND; VECTOR_MUL_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `fstcart:real^(N,2)finite_sum->real^N`) THEN
  ASM_REWRITE_TAC[MOI_FCB_CONE_SND; VECTOR_MUL_LCANCEL] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [UNDISCH_TAC `t' < &1` THEN REAL_ARITH_TAC; SIMP_TAC[]]);;

(* A point of two cones with different apexes lies in the lifted space.      *)

let MOI_FCB_CONE_DIFF = prove
 (`!i j t t' (x:real^N) x'.
     ~(i = j) /\
     (&1 - t) % moi_fcb_lift x + t % moi_fcb_apex i:real^(N,2)finite_sum =
     (&1 - t') % moi_fcb_lift x' + t' % moi_fcb_apex j
     ==> t = &0 /\ t' = &0 /\ x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t = t' /\ t * &i = t' * &j` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `sndcart:real^(N,2)finite_sum->real^2`) THEN
    REWRITE_TAC[MOI_FCB_CONE_SND; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
                VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `t * &i = t' * &j` THEN ASM_REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ARITH `a * b = a * c <=> a * (b - c) = &0`; REAL_ENTIRE] THEN
    UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t' = &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `fstcart:real^(N,2)finite_sum->real^N`) THEN
  ASM_REWRITE_TAC[MOI_FCB_CONE_SND] THEN VECTOR_ARITH_TAC);;

(* The cone over the hull of a set is the hull of the cone over the set.   *)

let MOI_FCB_CONE_HULL = prove
 (`!i (v:real^N->bool).
     convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift (convex hull v)) =
     convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift v):real^(N,2)finite_sum->bool`,
  REPEAT GEN_TAC THEN SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
  ONCE_REWRITE_TAC[SET_RULE `(a:real^(N,2)finite_sum) INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[GSYM HULL_UNION_RIGHT]);;

let MOI_FCB_APEX_NOT_FLAT = prove
 (`!i (s:real^N->bool).
     ~(moi_fcb_apex i IN affine hull (IMAGE moi_fcb_lift s):real^(N,2)finite_sum->bool)`,
  REPEAT GEN_TAC THEN SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N`
    (MP_TAC o AP_TERM `sndcart:real^(N,2)finite_sum->real^2` o CONJUNCT1)) THEN
  REWRITE_TAC[MOI_FCB_LIFT; MOI_FCB_APEX; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FCB_CONE_SIMPLEX = prove
 (`!i n (s:real^N->bool).
     n simplex s
     ==> (n + &1) simplex
         (convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):real^(N,2)finite_sum->bool)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_fcb_apex i INSERT IMAGE moi_fcb_lift (v:real^N->bool):
              real^(N,2)finite_sum->bool` THEN
  ASM_REWRITE_TAC[MOI_FCB_CONE_HULL] THEN
  MP_TAC(ISPECL [`i:num`; `v:real^N->bool`] MOI_FCB_APEX_NOT_FLAT) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(moi_fcb_apex i IN IMAGE moi_fcb_lift (v:real^N->bool):
                  real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (v:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[AFFINE_DEPENDENT_LINEAR_IMAGE_EQ; MOI_FCB_LIFT];
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE] THEN
    SUBGOAL_THEN `CARD(IMAGE (moi_fcb_lift:real^N->real^(N,2)finite_sum) v) = CARD v`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[MOI_FCB_LIFT] THEN MESON_TAC[];
      REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN ASM_REWRITE_TAC[]]]);;

(* Faces of a cone over a simplex.                                            *)

let MOI_FCB_CONE_FACES = prove
 (`!i (s:real^N->bool) f.
     (?n. n simplex s)
     ==> (f face_of
          convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):real^(N,2)finite_sum->bool <=>
          (?g. g face_of s /\ f = IMAGE moi_fcb_lift g) \/
          (?g. g face_of s /\
               f = convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift g)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  MP_TAC(ISPECL [`i:num`; `n:int`; `s:real^N->bool`] MOI_FCB_CONE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `n simplex (s:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[MOI_FCB_CONE_HULL] THEN
  MP_TAC(ISPECL [`i:num`; `v:real^N->bool`] MOI_FCB_APEX_NOT_FLAT) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~affine_dependent (moi_fcb_apex i INSERT IMAGE moi_fcb_lift (v:real^N->bool):
                  real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[AFFINE_DEPENDENT_LINEAR_IMAGE_EQ; MOI_FCB_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fcb_apex i IN IMAGE moi_fcb_lift (v:real^N->bool):
                  real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `w0 = {x:real^N | x IN v /\ moi_fcb_lift x IN w}` THEN
    SUBGOAL_THEN `w0 SUBSET (v:real^N->bool) /\
                  w DELETE moi_fcb_apex i = IMAGE moi_fcb_lift w0`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w0" THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_DELETE; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^(N,2)finite_sum` THEN EQ_TAC THENL
       [STRIP_TAC THEN
        SUBGOAL_THEN `(z:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift (v:real^N->bool)`
        MP_TAC THENL
         [UNDISCH_TAC `w SUBSET moi_fcb_apex i INSERT IMAGE moi_fcb_lift (v:real^N->bool)` THEN
          UNDISCH_TAC `(z:real^(N,2)finite_sum) IN w` THEN
          UNDISCH_TAC `~(z:real^(N,2)finite_sum = moi_fcb_apex i)` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:real^(N,2)finite_sum) IN w` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN
        UNDISCH_TAC `~(moi_fcb_apex i IN IMAGE moi_fcb_lift (v:real^N->bool):
                       real^(N,2)finite_sum->bool)` THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `moi_fcb_apex i IN (w:real^(N,2)finite_sum->bool)` THENL
     [DISJ2_TAC THEN EXISTS_TAC `convex hull w0:real^N->bool` THEN
      ASM_REWRITE_TAC[MOI_FCB_CONE_HULL] THEN
      CONJ_TAC THENL [EXISTS_TAC `w0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(lhs(concl th)) &&
        can (find_term ((=) `(DELETE):(real^(N,2)finite_sum->bool)->real^(N,2)finite_sum->real^(N,2)finite_sum->bool`)) (lhs(concl th)))) THEN
      UNDISCH_TAC `moi_fcb_apex i IN (w:real^(N,2)finite_sum->bool)` THEN SET_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `convex hull w0:real^N->bool` THEN
      CONJ_TAC THENL [EXISTS_TAC `w0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(lhs(concl th)) &&
        can (find_term ((=) `(DELETE):(real^(N,2)finite_sum->bool)->real^(N,2)finite_sum->real^(N,2)finite_sum->bool`)) (lhs(concl th)))) THEN
      UNDISCH_TAC `~(moi_fcb_apex i IN (w:real^(N,2)finite_sum->bool))` THEN SET_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `g:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w0:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `IMAGE moi_fcb_lift (w0:real^N->bool):real^(N,2)finite_sum->bool` THEN
      SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
      UNDISCH_TAC `w0 SUBSET (v:real^N->bool)` THEN SET_TAC[];
      EXISTS_TAC `moi_fcb_apex i INSERT IMAGE moi_fcb_lift (w0:real^N->bool):
                  real^(N,2)finite_sum->bool` THEN
      REWRITE_TAC[MOI_FCB_CONE_HULL] THEN
      UNDISCH_TAC `w0 SUBSET (v:real^N->bool)` THEN SET_TAC[]]]);;

(* Intersections of cones and lifted sets.                                    *)

let MOI_FCB_CONE_EMPTY = prove
 (`!i. convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift ({}:real^N->bool)) =
       {moi_fcb_apex i:real^(N,2)finite_sum}`,
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]);;

let MOI_FCB_APEX_NOT_LIFT = prove
 (`!i (y:real^N). ~(moi_fcb_lift y = moi_fcb_apex i:real^(N,2)finite_sum) /\
                  ~(moi_fcb_apex i = moi_fcb_lift y:real^(N,2)finite_sum)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `~p /\ (q ==> p) ==> ~p /\ ~q`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\z:real^(N,2)finite_sum. (sndcart z)$1`) THEN
  REWRITE_TAC[MOI_FCB_LIFT; MOI_FCB_APEX; VEC_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_FCB_LIFT_INJ = prove
 (`!x y:real^N. moi_fcb_lift x = moi_fcb_lift y ==> x = y`,
  MESON_TAC[MOI_FCB_LIFT]);;

let MOI_FCB_CONE_INTER_FLAT = prove
 (`!i (s:real^N->bool) t.
     convex s
     ==> convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) INTER
         IMAGE moi_fcb_lift t =
         IMAGE moi_fcb_lift (s INTER t):real^(N,2)finite_sum->bool`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY; INTER_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    ASM_CASES_TAC `z = moi_fcb_apex i:real^(N,2)finite_sum` THEN
    ASM_REWRITE_TAC[MOI_FCB_APEX_NOT_LIFT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
  ASM_SIMP_TAC[IN_INTER; MOI_FCB_CONE_POINTS] THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `t0 = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `z = (&1 - t0) % moi_fcb_lift x + t0 % moi_fcb_apex i:
                   real^(N,2)finite_sum` THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\z:real^(N,2)finite_sum. (sndcart z)$1`) THEN
      REWRITE_TAC[MOI_FCB_CONE_SND; MOI_FCB_LIFT; VEC_COMPONENT; VECTOR_MUL_COMPONENT;
                  VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x:real^N = y` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_FCB_LIFT_INJ THEN
      UNDISCH_TAC `z = (&1 - &0) % moi_fcb_lift x + &0 % moi_fcb_apex i:
                   real^(N,2)finite_sum` THEN
      UNDISCH_TAC `z = moi_fcb_lift (y:real^N):real^(N,2)finite_sum` THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&0`; `x:real^N`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FCB_CONE_INTER_SAME = prove
 (`!i (s:real^N->bool) t.
     convex s /\ convex t
     ==> convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) INTER
         convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift t) =
         convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift (s INTER t)):
         real^(N,2)finite_sum->bool`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N->bool. moi_fcb_apex i IN
                  convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift u):
                  real^(N,2)finite_sum->bool` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[]] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY; INTER_EMPTY] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY; INTER_EMPTY] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
  ASM_SIMP_TAC[MOI_FCB_CONE_POINTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`i:num`; `t1:real`; `t2:real`; `x1:real^N`; `x2:real^N`]
    MOI_FCB_CONE_SAME) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `t1 < &1` THENL
   [SUBGOAL_THEN `(x1:real^N) IN s INTER t` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `~((s:real^N->bool) INTER t = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FCB_CONE_POINTS; CONVEX_INTER] THEN
    MAP_EVERY EXISTS_TAC [`t1:real`; `x1:real^N`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x1:real^N = x2` SUBST1_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    SUBGOAL_THEN `t1 = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z = moi_fcb_apex i:real^(N,2)finite_sum` SUBST1_TAC THENL
     [UNDISCH_TAC `z = (&1 - &1) % moi_fcb_lift x1 + &1 % moi_fcb_apex i:
                   real^(N,2)finite_sum` THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

let MOI_FCB_CONE_INTER_DIFF = prove
 (`!i j (s:real^N->bool) t.
     ~(i = j) /\ convex s /\ convex t
     ==> convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) INTER
         convex hull (moi_fcb_apex j INSERT IMAGE moi_fcb_lift t) =
         IMAGE moi_fcb_lift (s INTER t):real^(N,2)finite_sum->bool`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k (u:real^N->bool). convex u
                  ==> IMAGE moi_fcb_lift u SUBSET
                      convex hull (moi_fcb_apex k INSERT IMAGE moi_fcb_lift u):
                      real^(N,2)finite_sum->bool` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_fcb_apex k INSERT IMAGE moi_fcb_lift (u:real^N->bool):
                real^(N,2)finite_sum->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `IMAGE moi_fcb_lift (s:real^N->bool):real^(N,2)finite_sum->bool`;
      EXISTS_TAC `IMAGE moi_fcb_lift (t:real^N->bool):real^(N,2)finite_sum->bool`] THEN
    ASM_SIMP_TAC[] THEN SET_TAC[]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) INTER
              IMAGE moi_fcb_lift (t:real^N->bool):real^(N,2)finite_sum->bool` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[MOI_FCB_CONE_INTER_FLAT; SUBSET_REFL]] THEN
  MATCH_MP_TAC(SET_RULE `!a b c:A->bool. a INTER b SUBSET c ==> a INTER b SUBSET a INTER c`) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `z = moi_fcb_apex i:real^(N,2)finite_sum`)) THEN
    ASM_CASES_TAC `t:real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY; IN_SING] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\z:real^(N,2)finite_sum. (sndcart z)$2`) THEN
      REWRITE_TAC[MOI_FCB_APEX; VECTOR_2; REAL_OF_NUM_EQ] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_FCB_CONE_POINTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`i:num`; `j:num`; `&1`; `t2:real`; `x2:real^N`; `x2:real^N`]
        MOI_FCB_CONE_DIFF) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `moi_fcb_apex i = (&1 - t2) % moi_fcb_lift x2 + t2 % moi_fcb_apex j:
                     real^(N,2)finite_sum` THEN VECTOR_ARITH_TAC;
        REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FCB_CONE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[MOI_FCB_CONE_POINTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`i:num`; `j:num`; `t1:real`; `&1`; `x1:real^N`; `x1:real^N`]
      MOI_FCB_CONE_DIFF) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `moi_fcb_apex j = (&1 - t1) % moi_fcb_lift x1 + t1 % moi_fcb_apex i:
                   real^(N,2)finite_sum` THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
  ASM_SIMP_TAC[MOI_FCB_CONE_POINTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`i:num`; `j:num`; `t1:real`; `t2:real`; `x1:real^N`; `x2:real^N`]
    MOI_FCB_CONE_DIFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z = (&1 - t1) % moi_fcb_lift x1 + t1 % moi_fcb_apex i:
                 real^(N,2)finite_sum` THEN
    UNDISCH_TAC `z = (&1 - t2) % moi_fcb_lift x2 + t2 % moi_fcb_apex j:
                 real^(N,2)finite_sum` THEN
    DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
      SUBST_ALL_TAC))] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x2:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The capped complex moi_fcb_cap c ix: the lifted simplices of c and the    *)
(* cones over the lifted simplices of each component P of the surface        *)
(* boundary, with apex moi_fcb_apex (ix P).  It is a simplicial complex.     *)
(* ========================================================================= *)

let moi_fcb_cap = new_definition
 `moi_fcb_cap (c:(real^N->bool)->bool) (ix:(real^N->bool)->num) =
    IMAGE (IMAGE moi_fcb_lift) c UNION
    {convex hull (moi_fcb_apex (ix P) INSERT IMAGE moi_fcb_lift s):
       real^(N,2)finite_sum->bool | P,s |
       P IN components (surface_boundary c) /\ s IN c /\ s SUBSET P}`;;

let MOI_FCB_CAP_IN = prove
 (`!(c:(real^N->bool)->bool) ix x.
     x IN moi_fcb_cap c ix <=>
     (?s. s IN c /\ x = IMAGE moi_fcb_lift s) \/
     (?P s. P IN components (surface_boundary c) /\ s IN c /\ s SUBSET P /\
            x = convex hull (moi_fcb_apex (ix P) INSERT IMAGE moi_fcb_lift s))`,
  REWRITE_TAC[moi_fcb_cap; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Faces and intersections of lifted sets.                                    *)

let MOI_FCB_LIFT_FACES = prove
 (`!(s:real^N->bool) f.
     f face_of IMAGE moi_fcb_lift s:real^(N,2)finite_sum->bool
     ==> ?g. g face_of s /\ f = IMAGE moi_fcb_lift g`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{x:real^N | x IN s /\ moi_fcb_lift x IN f}` THEN
  SUBGOAL_THEN `f = IMAGE moi_fcb_lift {x:real^N | x IN s /\ moi_fcb_lift x IN f}:
                real^(N,2)finite_sum->bool` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(ISPECL [`moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `{x:real^N | x IN s /\ moi_fcb_lift x IN f}`; `s:real^N->bool`]
    FACE_OF_LINEAR_IMAGE) THEN
  REWRITE_TAC[MOI_FCB_LIFT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let MOI_FCB_LIFT_FACE_OF = prove
 (`!(g:real^N->bool) s.
     g face_of s ==> IMAGE moi_fcb_lift g face_of IMAGE moi_fcb_lift s:
                     real^(N,2)finite_sum->bool`,
  SIMP_TAC[FACE_OF_LINEAR_IMAGE; MOI_FCB_LIFT]);;

let MOI_FCB_LIFT_INTER = prove
 (`!(s:real^N->bool) t.
     IMAGE moi_fcb_lift s INTER IMAGE moi_fcb_lift t =
     IMAGE moi_fcb_lift (s INTER t):real^(N,2)finite_sum->bool`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_INTER_INJ THEN
  REWRITE_TAC[MOI_FCB_LIFT]);;

let MOI_FCB_CONE_FACE_OF = prove
 (`!i (s:real^N->bool) g.
     (?n. n simplex s) /\ g face_of s
     ==> IMAGE moi_fcb_lift g face_of
           convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):
           real^(N,2)finite_sum->bool /\
         convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift g) face_of
           convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):
           real^(N,2)finite_sum->bool`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `i:num` MOI_FCB_CONE_FACES) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `?n. n simplex (s:real^N->bool)`)]) THEN
  ASM_MESON_TAC[]);;

let MOI_FCB_CONE_FACE_LIFT = prove
 (`!i (s:real^N->bool) g.
     (?n. n simplex s) /\ g face_of s
     ==> IMAGE moi_fcb_lift g face_of
           convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):
           real^(N,2)finite_sum->bool`,
  MESON_TAC[MOI_FCB_CONE_FACE_OF]);;

let MOI_FCB_CONE_FACE_CONE = prove
 (`!i (s:real^N->bool) g.
     (?n. n simplex s) /\ g face_of s
     ==> convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift g) face_of
           convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):
           real^(N,2)finite_sum->bool`,
  MESON_TAC[MOI_FCB_CONE_FACE_OF]);;

(* The capped complex is a simplicial complex.                                *)

let MOI_FCB_CAP_SC = prove
 (`!(c:(real^N->bool)->bool) ix.
     simplicial_complex c /\ FINITE (components (surface_boundary c))
     ==> simplicial_complex (moi_fcb_cap c ix)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> convex s /\ (?n. n simplex s)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!s t:real^N->bool. s IN c /\ t IN c ==> (s INTER t) face_of s`
  ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `!s g:real^N->bool. s IN c /\ g face_of s ==> g IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN moi_fcb_cap (c:(real^N->bool)->bool) ix /\ y IN moi_fcb_cap c ix
          ==> (x INTER y) face_of x`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^(N,2)finite_sum->bool`; `y:real^(N,2)finite_sum->bool`] THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC)))
      (DISJ_CASES_THEN2 (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `Q:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
          STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[MOI_FCB_LIFT_INTER] THEN MATCH_MP_TAC MOI_FCB_LIFT_FACE_OF THEN
      ASM_SIMP_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[MOI_FCB_CONE_INTER_FLAT] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MOI_FCB_LIFT_FACE_OF THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[MOI_FCB_CONE_INTER_FLAT] THEN MATCH_MP_TAC MOI_FCB_CONE_FACE_LIFT THEN ASM_SIMP_TAC[];
      ASM_CASES_TAC `(ix:(real^N->bool)->num) P = ix Q` THENL
       [ASM_SIMP_TAC[MOI_FCB_CONE_INTER_SAME] THEN
        MATCH_MP_TAC MOI_FCB_CONE_FACE_CONE THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[MOI_FCB_CONE_INTER_DIFF] THEN
        MATCH_MP_TAC MOI_FCB_CONE_FACE_LIFT THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcb_cap; FINITE_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[simplicial_complex];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\(P,s). convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P)
                    INSERT IMAGE moi_fcb_lift s):real^(N,2)finite_sum->bool)
                  (components (surface_boundary c) CROSS c)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CROSS THEN
        ASM_MESON_TAC[simplicial_complex];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
        MESON_TAC[]]];
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool`
        STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N->bool` o check (fun th ->
      can (term_match [] `!s:real^N->bool. s IN c ==> convex s /\ (?n. n simplex s)`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int` o CONJUNCT2) THENL
     [EXISTS_TAC `n:int` THEN ASM_SIMP_TAC[SIMPLEX_LINEAR_IMAGE_EQ; MOI_FCB_LIFT];
      EXISTS_TAC `n + &1:int` THEN ASM_SIMP_TAC[MOI_FCB_CONE_SIMPLEX]];
    MAP_EVERY X_GEN_TAC [`f:real^(N,2)finite_sum->bool`; `x:real^(N,2)finite_sum->bool`] THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `a:real^N->bool` STRIP_ASSUME_TAC)))
      ASSUME_TAC) THEN
    UNDISCH_TAC `(f:real^(N,2)finite_sum->bool) face_of x` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP MOI_FCB_LIFT_FACES) THEN
      DISJ1_TAC THEN EXISTS_TAC `g:real^N->bool` THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`(ix:(real^N->bool)->num) P`; `a:real^N->bool`;
                     `f:real^(N,2)finite_sum->bool`] MOI_FCB_CONE_FACES) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)) THENL
       [DISJ1_TAC THEN EXISTS_TAC `g:real^N->bool` THEN ASM_MESON_TAC[];
        DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `g:real^N->bool`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
          ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]]];
    MAP_EVERY X_GEN_TAC [`x:real^(N,2)finite_sum->bool`; `y:real^(N,2)finite_sum->bool`] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_MESON_TAC[]]]);;

(* ========================================================================= *)
(* The capped complex is a closed combinatorial surface.  Simplices of c     *)
(* inside the surface boundary lie in boundary edges; the vertices of the    *)
(* capped complex; its links at lifted interior vertices, at apexes and at   *)
(* lifted boundary vertices (all vertices of the link of degree 2, by        *)
(* MOI_S8TB_LINK_DEGREE and MOI_S4L_CM1_CIRCLES).  The two facts on the      *)
(* surface boundary (BD_DEGREE, BD_CIRCLES of surfb) enter as hypotheses.    *)
(* ========================================================================= *)

(* Simplices of c inside the surface boundary lie in boundary edges.         *)

let MOI_FCB_SB_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) s.
     simplicial_complex c /\ s IN c /\ ~(s = {}) /\ s SUBSET surface_boundary c
     ==> ?e. e IN c /\ aff_dim e = &1 /\
             CARD {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = 1 /\ s SUBSET e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e INTER s:real^N->bool) face_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `e INTER s:real^N->bool = s` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e INTER s:real^N->bool`; `s:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior s` THEN
    UNDISCH_TAC `(x:real^N) IN e` THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    SET_TAC[]]);;

let MOI_FCB_EDGE_SB = prove
 (`!(c:(real^N->bool)->bool) e.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> (e SUBSET surface_boundary c <=>
          CARD {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = 1)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SB_SIMPLEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `e:real^N->bool = e'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(e INTER e':real^N->bool) face_of e'` MP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `e INTER e':real^N->bool = e` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `e':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    DISCH_TAC THEN REWRITE_TAC[surface_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* Vertices of the capped complex.                                            *)

let MOI_FCB_LIFT_SING = prove
 (`!(s:real^N->bool) w.
     IMAGE moi_fcb_lift s = {w:real^(N,2)finite_sum} <=>
     ?v. s = {v} /\ w = moi_fcb_lift v`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?v:real^N. v IN s` (X_CHOOSE_TAC `v:real^N`) THENL
     [MATCH_MP_TAC(SET_RULE `!s:real^N->bool. ~(s = {}) ==> ?x. x IN s`) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `IMAGE moi_fcb_lift ({}:real^N->bool) = {w:real^(N,2)finite_sum}` THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^N` THEN
    SUBGOAL_THEN `!x:real^N. x IN s ==> moi_fcb_lift x = w:real^(N,2)finite_sum`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_SING] THEN
      EQ_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC MOI_FCB_LIFT_INJ THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]]);;

let MOI_FCB_EMPTY_IN = prove
 (`!(c:(real^N->bool)->bool) P.
     simplicial_complex c /\ P IN components (surface_boundary c) ==> {} IN c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE `~(s:A->bool = {}) ==> ?x. x IN s`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
   [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[EMPTY_FACE_OF]);;

let MOI_FCB_CAP_VERTEX = prove
 (`!(c:(real^N->bool)->bool) ix w.
     simplicial_complex c
     ==> ({w} IN moi_fcb_cap c ix <=>
          (?v. {v} IN c /\ w = moi_fcb_lift v) \/
          (?P. P IN components (surface_boundary c) /\ w = moi_fcb_apex (ix P)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FCB_CAP_IN] THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
        STRIP_ASSUME_TAC))) THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `{w} = IMAGE moi_fcb_lift (s:real^N->bool)` THEN
      DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[MOI_FCB_LIFT_SING] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `v:real^N` THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `P:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                    {w:real^(N,2)finite_sum}` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        REWRITE_TAC[IN_SING] THEN MESON_TAC[]]];
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `{}:real^N->bool`] THEN
      ASM_REWRITE_TAC[EMPTY_SUBSET; MOI_FCB_CONE_EMPTY] THEN
      ASM_MESON_TAC[MOI_FCB_EMPTY_IN]]]);;

(* A lifted point lies in a cone exactly when it lies in the lifted base.    *)

let MOI_FCB_LIFT_IN_CONE = prove
 (`!i (s:real^N->bool) v.
     convex s
     ==> (moi_fcb_lift v IN convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) <=>
          v IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `s:real^N->bool`; `{v:real^N}`] MOI_FCB_CONE_INTER_FLAT) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_fcb_lift (v:real^N):real^(N,2)finite_sum`) THEN
  REWRITE_TAC[MOI_FCB_LIFT] THEN MESON_TAC[]);;

let MOI_FCB_APEX_NOT_IN_LIFT = prove
 (`!i (s:real^N->bool). ~(moi_fcb_apex i IN IMAGE moi_fcb_lift s:real^(N,2)finite_sum->bool)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[MOI_FCB_APEX_NOT_LIFT]);;

(* Small facts on simplicial complexes and lifts.                             *)

let MOI_FCB_SC_FACES = prove
 (`!(c:(real^N->bool)->bool) s g.
     simplicial_complex c /\ s IN c /\ g face_of s ==> g IN c`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_FCB_SC_CONVEX = prove
 (`!(c:(real^N->bool)->bool) s.
     simplicial_complex c /\ s IN c ==> convex s /\ (?n. n simplex s)`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_FCB_LIFT_IN = prove
 (`!(v:real^N) s. moi_fcb_lift v IN IMAGE moi_fcb_lift s:real^(N,2)finite_sum->bool <=>
                  v IN s`,
  REWRITE_TAC[IN_IMAGE; MOI_FCB_LIFT] THEN MESON_TAC[]);;

(* The link at a lifted vertex off the surface boundary is the lifted link. *)

let MOI_FCB_CAP_LINK_INT = prove
 (`!(c:(real^N->bool)->bool) ix v.
     simplicial_complex c /\ ~(v IN surface_boundary c)
     ==> simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v) =
         IMAGE (IMAGE moi_fcb_lift) (simplicial_link c v)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC))) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(y:real^(N,2)finite_sum->bool) IN moi_fcb_cap c ix` THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `t:real^N->bool`
        STRIP_ASSUME_TAC))) THENL
     [UNDISCH_TAC `(x:real^(N,2)finite_sum->bool) face_of y` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
        MATCH_MP MOI_FCB_LIFT_FACES) THEN
      EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FCB_SC_FACES THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(moi_fcb_lift (v:real^N) IN (x:real^(N,2)finite_sum->bool))` THEN
        ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (y:real^(N,2)finite_sum->bool)` THEN
        ASM_REWRITE_TAC[MOI_FCB_LIFT_IN]];
      UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (y:real^(N,2)finite_sum->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((v:real^N) IN surface_boundary c)` THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2 SUBST1_TAC
      STRIP_ASSUME_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
      EXISTS_TAC `IMAGE moi_fcb_lift (t:real^N->bool):real^(N,2)finite_sum->bool` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
        MATCH_MP_TAC MOI_FCB_LIFT_FACE_OF THEN ASM_REWRITE_TAC[]]]]);;

(* An apex lies in a cone exactly when it is the apex of that cone.         *)

let MOI_FCB_APEX_IN_CONE = prove
 (`!i j (s:real^N->bool).
     convex s
     ==> (moi_fcb_apex j IN
          convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):real^(N,2)finite_sum->bool
          <=> i = j)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^(N,2)finite_sum. (sndcart z)$2`) THEN
    REWRITE_TAC[MOI_FCB_APEX; VECTOR_2; REAL_OF_NUM_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FCB_CONE_POINTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `sndcart:real^(N,2)finite_sum->real^2`) THEN
  REWRITE_TAC[MOI_FCB_CONE_SND; MOI_FCB_APEX; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN SUBST_ALL_TAC(SYM(CONJUNCT1 th))) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_EQ] THEN MESON_TAC[]);;

(* A point of a boundary component lies in a boundary edge inside it.       *)

let MOI_FCB_BD_COVER = prove
 (`!(c:(real^N->bool)->bool) P x.
     simplicial_complex c /\ P IN components (surface_boundary c) /\ x IN P
     ==> ?e. e IN c /\ aff_dim e = &1 /\
             CARD {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = 1 /\
             e SUBSET P /\ x IN e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
   [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `surface_boundary (c:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN
    ASM_MESON_TAC[MOI_FCB_SC_CONVEX];
    REWRITE_TAC[surface_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ASM SET_TAC[]]);;

(* The link at an apex: the lifted boundary component.                      *)

let MOI_FCB_CAP_LINK_APEX = prove
 (`!(c:(real^N->bool)->bool) ix P.
     simplicial_complex c /\ P IN components (surface_boundary c) /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_apex (ix P))) =
         IMAGE moi_fcb_lift P`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(y:real^(N,2)finite_sum->bool) IN moi_fcb_cap c ix` THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `Q:real^N->bool` (X_CHOOSE_THEN `t:real^N->bool`
        STRIP_ASSUME_TAC))) THENL
     [UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                   (y:real^(N,2)finite_sum->bool)` THEN
      ASM_REWRITE_TAC[MOI_FCB_APEX_NOT_IN_LIFT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `Q:real^N->bool = P` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                   (y:real^(N,2)finite_sum->bool)` THEN
      ASM_SIMP_TAC[MOI_FCB_APEX_IN_CONE] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^(N,2)finite_sum->bool) face_of y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(ix:(real^N->bool)->num) P`; `t:real^N->bool`;
                   `x:real^(N,2)finite_sum->bool`] MOI_FCB_CONE_FACES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)) THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g:real^N->bool) SUBSET t` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `(t:real^N->bool) SUBSET P` THEN SET_TAC[];
      UNDISCH_TAC `~(moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                     (x:real^(N,2)finite_sum->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
      MOI_FCB_BD_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (e:real^N->bool):real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[MOI_FCB_LIFT_IN] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM; MOI_FCB_APEX_NOT_IN_LIFT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                             IMAGE moi_fcb_lift (e:real^N->bool)):
                real^(N,2)finite_sum->bool` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `e:real^N->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      MATCH_MP_TAC MOI_FCB_CONE_FACE_LIFT THEN ASM_SIMP_TAC[FACE_OF_REFL]]]);;

(* Dimensions of cones, injectivity of the cone map.                        *)

let MOI_FCB_CONE_AFF_DIM = prove
 (`!i (s:real^N->bool).
     (?n. n simplex s)
     ==> aff_dim (convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s):
                  real^(N,2)finite_sum->bool) = aff_dim s + &1`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  MP_TAC(ISPECL [`i:num`; `n:int`; `s:real^N->bool`] MOI_FCB_CONE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_MESON_TAC[AFF_DIM_SIMPLEX]);;

let MOI_FCB_CONE_INJ = prove
 (`!i (s:real^N->bool) t.
     convex s /\ convex t /\
     convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift s) =
     convex hull (moi_fcb_apex i INSERT IMAGE moi_fcb_lift t):real^(N,2)finite_sum->bool
     ==> s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `s:real^N->bool`; `(:real^N)`] MOI_FCB_CONE_INTER_FLAT) THEN
  MP_TAC(ISPECL [`i:num`; `t:real^N->bool`; `(:real^N)`] MOI_FCB_CONE_INTER_FLAT) THEN
  ASM_REWRITE_TAC[INTER_UNIV] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE moi_fcb_lift s = IMAGE moi_fcb_lift (t:real^N->bool):
                real^(N,2)finite_sum->bool` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `moi_fcb_lift (x:real^N):real^(N,2)finite_sum`) THEN
  REWRITE_TAC[MOI_FCB_LIFT] THEN MESON_TAC[]);;

(* Simplices of the capped complex have dimension at most 2.               *)

let MOI_FCB_CAP_DIM = prove
 (`!(c:(real^N->bool)->bool) ix t.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     t IN moi_fcb_cap c ix
     ==> aff_dim t <= &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[MOI_FCB_CAP_IN] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `P:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE; MOI_FCB_LIFT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[MOI_FCB_CONE_AFF_DIM] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SB_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e:real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FCB_SC_INTER = prove
 (`!(c:(real^N->bool)->bool) s t.
     simplicial_complex c /\ s IN c /\ t IN c
     ==> (s INTER t) face_of s /\ (s INTER t) face_of t`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_FCB_IMAGE_LIFT_INJ = prove
 (`!(s:real^N->bool) t.
     IMAGE moi_fcb_lift s = IMAGE moi_fcb_lift t:real^(N,2)finite_sum->bool <=> s = t`,
  MP_TAC(ISPEC `moi_fcb_lift:real^N->real^(N,2)finite_sum` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  REWRITE_TAC[MOI_FCB_LIFT] THEN SIMP_TAC[]);;

let MOI_FCB_IMAGE_LIFT_SUBSET = prove
 (`!(s:real^N->bool) t.
     IMAGE moi_fcb_lift s SUBSET IMAGE moi_fcb_lift t:real^(N,2)finite_sum->bool <=>
     s SUBSET t`,
  MP_TAC(ISPEC `moi_fcb_lift:real^N->real^(N,2)finite_sum` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  REWRITE_TAC[MOI_FCB_LIFT] THEN SIMP_TAC[]);;

(* The triangles of the capped complex at a lifted edge.                     *)

let MOI_FCB_CAP_TRI_SET = prove
 (`!(c:(real^N->bool)->bool) ix e.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> {t | t IN moi_fcb_cap c ix /\ aff_dim t = &2 /\
              IMAGE moi_fcb_lift e SUBSET t} =
         IMAGE (IMAGE moi_fcb_lift) {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} UNION
         {convex hull (moi_fcb_apex (ix Q) INSERT IMAGE moi_fcb_lift e):
          real^(N,2)finite_sum->bool | Q |
          Q IN components (surface_boundary c) /\ e SUBSET Q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_IMAGE; MOI_FCB_CAP_IN] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `Q:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
          STRIP_ASSUME_TAC)))
      STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aff_dim(x:real^(N,2)finite_sum->bool) = &2` THEN
      UNDISCH_TAC `IMAGE moi_fcb_lift (e:real^N->bool) SUBSET x` THEN
      ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FCB_LIFT_IN] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `Q:real^N->bool` THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE moi_fcb_lift (e:real^N->bool) SUBSET x` THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `!a b u:A->bool. a SUBSET b ==> a INTER u SUBSET b INTER u`)) THEN
      DISCH_THEN(MP_TAC o SPEC
        `IMAGE moi_fcb_lift (:real^N):real^(N,2)finite_sum->bool`) THEN
      ASM_SIMP_TAC[MOI_FCB_CONE_INTER_FLAT; INTER_UNIV] THEN
      REWRITE_TAC[MOI_FCB_LIFT_INTER; INTER_UNIV; MOI_FCB_IMAGE_LIFT_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `s:real^N->bool = e` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(e INTER s:real^N->bool) face_of s` MP_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `s:real^N->bool`]
          MOI_FCB_SC_INTER) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `e INTER s:real^N->bool = e` SUBST1_TAC THENL
       [UNDISCH_TAC `(e:real^N->bool) SUBSET s` THEN SET_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^N->bool`; `s:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aff_dim(x:real^(N,2)finite_sum->bool) = &2` THEN
      ASM_SIMP_TAC[MOI_FCB_CONE_AFF_DIM] THEN
      UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THENL
     [REPEAT CONJ_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE; MOI_FCB_LIFT];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FCB_LIFT_IN] THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET s` THEN REWRITE_TAC[SUBSET]];
      REPEAT CONJ_TAC THENL
       [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`Q:real^N->bool`; `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MOI_FCB_CONE_AFF_DIM] THEN INT_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) Q) INSERT
                    IMAGE moi_fcb_lift (e:real^N->bool):real^(N,2)finite_sum->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[]]]]);;


(* The capped complex has two triangles at every lifted edge.               *)

let MOI_FCB_CAP_TRI_LIFT2 = prove
 (`!(c:(real^N->bool)->bool) ix e.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ e IN c /\ aff_dim e = &1
     ==> CARD {t | t IN moi_fcb_cap c ix /\ aff_dim t = &2 /\
                   IMAGE moi_fcb_lift e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FCB_CAP_TRI_SET] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FGB_CMB2_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (IMAGE (IMAGE moi_fcb_lift)
           {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}) =
    CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[MOI_FCB_IMAGE_LIFT_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (IMAGE moi_fcb_lift)
      {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} INTER
    {convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) Q) INSERT
                  IMAGE moi_fcb_lift e):real^(N,2)finite_sum->bool | Q |
     Q IN components (surface_boundary c) /\ e SUBSET Q} = {}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
    REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`(ix:(real^N->bool)->num) Q`; `s:real^N->bool`]
      MOI_FCB_APEX_NOT_IN_LIFT) THEN
    UNDISCH_TAC `x = IMAGE moi_fcb_lift (s:real^N->bool):real^(N,2)finite_sum->bool` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ASM_CASES_TAC `(e:real^N->bool) SUBSET surface_boundary c` THENL
   [SUBGOAL_THEN `?x:real^N. x IN e` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s:real^N->bool. ~(s = {}) ==> ?x. x IN s`) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `connected_component (surface_boundary c) (x:real^N) IN
        components (surface_boundary c) /\
      (e:real^N->bool) SUBSET connected_component (surface_boundary c) x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET surface_boundary c` THEN
        UNDISCH_TAC `(x:real^N) IN e` THEN SET_TAC[];
        MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[CONVEX_CONNECTED]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) Q) INSERT
                    IMAGE moi_fcb_lift e):real^(N,2)finite_sum->bool | Q |
       Q IN components (surface_boundary c) /\ e SUBSET Q} =
      {convex hull (moi_fcb_apex (ix (connected_component (surface_boundary c) x))
                    INSERT IMAGE moi_fcb_lift e)}`
    (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `y:real^(N,2)finite_sum->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `Q:real^N->bool`;
          `connected_component (surface_boundary c) (x:real^N)`] COMPONENTS_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET Q` THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET connected_component (surface_boundary c) x` THEN
        UNDISCH_TAC `(x:real^N) IN e` THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN
        EXISTS_TAC `connected_component (surface_boundary c) (x:real^N)` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (IMAGE moi_fcb_lift)
        {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`;
      `{convex hull (moi_fcb_apex ((ix:(real^N->bool)->num)
                     (connected_component (surface_boundary c) (x:real^N))) INSERT
                     IMAGE moi_fcb_lift (e:real^N->bool)):real^(N,2)finite_sum->bool}`]
     CARD_UNION) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_SING]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_EDGE_SB) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CARD_SING] THEN ARITH_TAC;
    SUBGOAL_THEN
     `{convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) Q) INSERT
                    IMAGE moi_fcb_lift e):real^(N,2)finite_sum->bool | Q |
       Q IN components (surface_boundary c) /\ e SUBSET Q} = {}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^(N,2)finite_sum->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~((e:real^N->bool) SUBSET surface_boundary c)` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `Q:real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:real^N->bool) SUBSET Q` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_EDGE_SB) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1 \/
                   CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_EMPTY]]);;

(* The capped complex has two triangles at the edge from a lifted boundary *)
(* vertex to the apex of its component.                                     *)

let MOI_FCB_CAP_TRI_APEX2 = prove
 (`!(c:(real^N->bool)->bool) ix P v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     P IN components (surface_boundary c) /\ {v} IN c /\ v IN P /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> CARD {t | t IN moi_fcb_cap c ix /\ aff_dim t = &2 /\
                   convex hull {moi_fcb_lift v, moi_fcb_apex (ix P)} SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN surface_boundary c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^N) IN P` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN moi_fcb_cap c ix /\ aff_dim t = &2 /\
         convex hull {moi_fcb_lift v, moi_fcb_apex ((ix:(real^N->bool)->num) P)}
         SUBSET t} =
    IMAGE (\e. convex hull (moi_fcb_apex (ix P) INSERT IMAGE moi_fcb_lift e):
               real^(N,2)finite_sum->bool)
          {e:real^N->bool | e IN c /\ aff_dim e = &1 /\ v IN e /\
                            CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `moi_fcb_lift (v:real^N) IN (x:real^(N,2)finite_sum->bool) /\
        moi_fcb_apex ((ix:(real^N->bool)->num) P) IN x`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check
          (fun th -> is_binary "SUBSET" (concl th))) THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        ALL_TAC] THEN
      REWRITE_TAC[MOI_FCB_CAP_IN] THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `Q:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
          STRIP_ASSUME_TAC))) THENL
       [UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                     (x:real^(N,2)finite_sum->bool)` THEN
        ASM_REWRITE_TAC[MOI_FCB_APEX_NOT_IN_LIFT];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN `Q:real^N->bool = P` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `ix:(real^N->bool)->num`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                     (x:real^(N,2)finite_sum->bool)` THEN
        ASM_SIMP_TAC[MOI_FCB_APEX_IN_CONE] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (x:real^(N,2)finite_sum->bool)` THEN
        ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1` ASSUME_TAC THENL
       [UNDISCH_TAC `aff_dim(x:real^(N,2)finite_sum->bool) = &2` THEN
        ASM_SIMP_TAC[MOI_FCB_CONE_AFF_DIM] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_EDGE_SB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `P:real^N->bool`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^N->bool) SUBSET P` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      SUBGOAL_THEN `(e:real^N->bool) SUBSET P` ASSUME_TAC THENL
       [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `surface_boundary (c:(real^N->bool)->bool)` THEN
        ASM_SIMP_TAC[CONVEX_CONNECTED] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_EDGE_SB) THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `(v:real^N) IN e` THEN UNDISCH_TAC `(v:real^N) IN P` THEN SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `e:real^N->bool`] THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MOI_FCB_CONE_AFF_DIM] THEN INT_ARITH_TAC;
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE];
          MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {e:real^N->bool | e IN c /\ aff_dim e = &1 /\ v IN e /\
                    CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FSB_BD_DEGREE) THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCB_CONE_INJ THEN
    EXISTS_TAC `(ix:(real^N->bool)->num) P` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FCB_SC_CONVEX];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The capped complex is a closed combinatorial surface (links at lifted     *)
(* boundary vertices: degree 2 everywhere and connected).                    *)
(* ========================================================================= *)

let MOI_FCB_PL_BALL_CONNECTED = prove
 (`!n (s:real^N->bool). pl_ball n s ==> connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `s = IMAGE (f:real^N->real^N) k` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_FCB_LINK_C_CONNECTED = prove
 (`!(c:(real^N->bool)->bool) v.
     combinatorial_manifold_with_boundary 2 c /\ {v} IN c
     ==> connected (UNIONS (simplicial_link c v))`,
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[MOI_S4O_SPHERE1_CONNECTED; MOI_FCB_PL_BALL_CONNECTED]);;

(* Context facts for the capped complex.                                      *)

let MOI_FCB_CAP_CONTEXT = prove
 (`!(c:(real^N->bool)->bool) ix.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> simplicial_complex c /\ FINITE (components (surface_boundary c)) /\
         simplicial_complex (moi_fcb_cap c ix) /\
         lf_simplicial_complex (moi_fcb_cap c ix) /\
         (!t. t IN moi_fcb_cap c ix ==> aff_dim t <= &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (components (surface_boundary (c:(real^N->bool)->bool)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FSB_BD_CIRCLES]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (moi_fcb_cap (c:(real^N->bool)->bool) ix)`
  ASSUME_TAC THENL [MATCH_MP_TAC MOI_FCB_CAP_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FCB_CAP_DIM THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_DIM THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* Every vertex of the link at a lifted boundary vertex has degree 2.        *)

let MOI_FCB_CAP_LINK_DEG = prove
 (`!(c:(real^N->bool)->bool) ix v a.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q) /\
     {a} IN simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)
     ==> CARD {e | e IN simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v) /\
                   aff_dim e = &1 /\ a IN e} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{moi_fcb_lift (v:real^N)} IN moi_fcb_cap c ix` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FCB_CAP_VERTEX] THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`; `moi_fcb_lift (v:real^N)`;
                 `a:real^(N,2)finite_sum`] MOI_S8TB_LINK_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`; `moi_fcb_lift (v:real^N)`;
                 `a:real^(N,2)finite_sum`] MOI_S8TB_LINK_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `{a:real^(N,2)finite_sum} IN moi_fcb_cap c ix` THEN
  ASM_SIMP_TAC[MOI_FCB_CAP_VERTEX] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `convex hull {moi_fcb_lift v, a} =
                  IMAGE moi_fcb_lift (convex hull {v:real^N,u}):real^(N,2)finite_sum->bool`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; MOI_FCB_LIFT] THEN
      REWRITE_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull {v:real^N,u} IN c /\ aff_dim(convex hull {v:real^N,u}) = &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `convex hull {moi_fcb_lift (v:real^N),a} IN moi_fcb_cap c ix` THEN
        ASM_REWRITE_TAC[MOI_FCB_CAP_IN; MOI_FCB_IMAGE_LIFT_INJ] THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
          (X_CHOOSE_THEN `R:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
            STRIP_ASSUME_TAC))) THENL
         [ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`(ix:(real^N->bool)->num) R`; `convex hull {v:real^N,u}`]
            MOI_FCB_APEX_NOT_IN_LIFT) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
          MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
        UNDISCH_TAC `aff_dim(convex hull {moi_fcb_lift (v:real^N),a}) = &1` THEN
        ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE; MOI_FCB_LIFT]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FCB_CAP_TRI_LIFT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN Q` ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {moi_fcb_lift (v:real^N),a} IN moi_fcb_cap c ix` THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `R:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
        STRIP_ASSUME_TAC))) THENL
     [MP_TAC(ISPECL [`(ix:(real^N->bool)->num) Q`; `s:real^N->bool`]
        MOI_FCB_APEX_NOT_IN_LIFT) THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {moi_fcb_lift (v:real^N),a} =
                   IMAGE moi_fcb_lift s:real^(N,2)finite_sum->bool` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `R:real^N->bool = Q` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ix:(real^N->bool)->num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(ix:(real^N->bool)->num) R`; `(ix:(real^N->bool)->num) Q`;
                     `s:real^N->bool`] MOI_FCB_APEX_IN_CONE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `convex hull {moi_fcb_lift (v:real^N),a} =
                   convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) R) INSERT
                                IMAGE moi_fcb_lift s)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) IN s` MP_TAC THENL
     [MP_TAC(ISPECL [`(ix:(real^N->bool)->num) Q`; `s:real^N->bool`; `v:real^N`]
        MOI_FCB_LIFT_IN_CONE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `convex hull {moi_fcb_lift (v:real^N),a} =
                   convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) Q) INSERT
                                IMAGE moi_fcb_lift s)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      UNDISCH_TAC `(s:real^N->bool) SUBSET Q` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FCB_CAP_TRI_APEX2 THEN ASM_REWRITE_TAC[]);;

(* Edges as segments, and the other end of an edge at a vertex.             *)

let MOI_FCB_EDGE_FRAME = prove
 (`!(c:(real^N->bool)->bool) e.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> ?p q. ~(p = q) /\ e = segment[p,q]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int` o CONJUNCT2) THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
      UNDISCH_TAC `&(CARD(w:real^N->bool)):int = &1 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]);;

let MOI_FCB_EDGE_OTHER = prove
 (`!(c:(real^N->bool)->bool) e v.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1 /\ {v} IN c /\ v IN e
     ==> ?u. ~(u = v) /\ {u} IN c /\ e = segment[v,u]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} face_of e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`; `e:real^N->bool`]
      MOI_FCB_SC_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{v:real^N} INTER e = {v}` SUBST1_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN e` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_EDGE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{p:real^N} IN c /\ {q:real^N} IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FCB_SC_FACES THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  UNDISCH_TAC `{v:real^N} face_of e` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT] THEN STRIP_TAC THENL
   [EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[SEGMENT_SYM] THEN ASM_MESON_TAC[]]);;

(* Members of the link at a lifted vertex: lifted links of c, or cones      *)
(* through the apex of the component of the vertex.                         *)

let MOI_FCB_CAP_LINK_MEMBER = prove
 (`!(c:(real^N->bool)->bool) ix v x.
     simplicial_complex c /\ {v} IN c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q) /\
     x IN simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)
     ==> (?g. g IN simplicial_link c v /\ x = IMAGE moi_fcb_lift g) \/
         (?P. P IN components (surface_boundary c) /\ v IN P /\
              moi_fcb_apex (ix P) IN x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INJ") MP_TAC))) THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[MOI_FCB_CAP_IN] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `Q:real^N->bool` (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC))) THENL
   [DISJ1_TAC THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(moi_fcb_lift (v:real^N) IN (x:real^(N,2)finite_sum->bool))` THEN
      ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^(N,2)finite_sum->bool) IN moi_fcb_cap c ix` THEN
    REWRITE_TAC[MOI_FCB_CAP_IN] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `R:real^N->bool` (X_CHOOSE_THEN `t:real^N->bool`
        STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (y:real^(N,2)finite_sum->bool)` THEN
        ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
        UNDISCH_TAC `(x:real^(N,2)finite_sum->bool) face_of y` THEN
        ASM_SIMP_TAC[FACE_OF_LINEAR_IMAGE; MOI_FCB_LIFT]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (y:real^(N,2)finite_sum->bool)` THEN
        ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE];
        ALL_TAC] THEN
      UNDISCH_TAC `(x:real^(N,2)finite_sum->bool) face_of y` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(ix:(real^N->bool)->num) R`; `t:real^N->bool`;
                     `IMAGE moi_fcb_lift (g:real^N->bool):real^(N,2)finite_sum->bool`]
        MOI_FCB_CONE_FACES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MOI_FCB_IMAGE_LIFT_INJ] THEN
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `h:real^N->bool` STRIP_ASSUME_TAC)) THENL
       [ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`(ix:(real^N->bool)->num) R`; `g:real^N->bool`]
          MOI_FCB_APEX_NOT_IN_LIFT) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `moi_fcb_apex ((ix:(real^N->bool)->num) Q) IN
                (y:real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b z:A. a SUBSET b /\ z IN a ==> z IN b`) THEN
    EXISTS_TAC `x:real^(N,2)finite_sum->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^(N,2)finite_sum->bool) IN moi_fcb_cap c ix` THEN
  REWRITE_TAC[MOI_FCB_CAP_IN] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `R:real^N->bool` (X_CHOOSE_THEN `t:real^N->bool`
      STRIP_ASSUME_TAC))) THENL
   [UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) Q) IN
                 (y:real^(N,2)finite_sum->bool)` THEN
    ASM_REWRITE_TAC[MOI_FCB_APEX_NOT_IN_LIFT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `R:real^N->bool = Q` SUBST_ALL_TAC THENL
   [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) Q) IN
                 (y:real^(N,2)finite_sum->bool)` THEN
    ASM_SIMP_TAC[MOI_FCB_APEX_IN_CONE];
    ALL_TAC] THEN
  EXISTS_TAC `Q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `moi_fcb_lift (v:real^N) IN (y:real^(N,2)finite_sum->bool)` THEN
    ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE] THEN UNDISCH_TAC `(t:real^N->bool) SUBSET Q` THEN
    SET_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]);;


(* A union of connected sets each empty or meeting a connected subset B of *)
(* the union is connected.                                                    *)

let MOI_FCB_CONNECTED_STAR = prove
 (`!(f:(real^M->bool)->bool) b.
     connected b /\ ~(b = {}) /\ b SUBSET UNIONS f /\
     (!s. s IN f ==> connected s /\ (s = {} \/ ~(s INTER b = {})))
     ==> connected (UNIONS f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS f = UNIONS ((b:real^M->bool) INSERT {b UNION s | s IN f})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `b UNION s:real^M->bool` THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^M->bool` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [ASM_REWRITE_TAC[UNION_EMPTY];
      MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((s:real^M->bool) INTER b = {})` THEN SET_TAC[]];
    MATCH_MP_TAC(SET_RULE `!a:A->bool u. ~(a = {}) /\ a SUBSET u ==> ~(u = {})`) THEN
    EXISTS_TAC `b:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERS; FORALL_IN_INSERT; FORALL_IN_GSPEC; SUBSET_REFL] THEN
    SET_TAC[]]);;


(* The link at a lifted boundary vertex is connected.                        *)

let MOI_FCB_CAP_LINK_CONN = prove
 (`!(c:(real^N->bool)->bool) ix v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     v IN surface_boundary c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> connected (UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v))) /\
         ~(UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `(v:real^N) IN surface_boundary c`) THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e0:real^N->bool`; `v:real^N`]
    MOI_FCB_EDGE_OTHER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN `(u0:real^N) IN e0 /\ {u0} face_of e0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[th; ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC]) THEN
  SUBGOAL_THEN `e0 SUBSET surface_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component (surface_boundary c) (v:real^N) IN
      components (surface_boundary c) /\
    v IN connected_component (surface_boundary c) v /\
    e0 SUBSET connected_component (surface_boundary c) v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
      ONCE_REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e0:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `P = connected_component (surface_boundary c) (v:real^N)` THEN
  ABBREV_TAC `sig0 = convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                                  IMAGE moi_fcb_lift {u0:real^N}):
                     real^(N,2)finite_sum->bool` THEN
  SUBGOAL_THEN
   `sig0 IN simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift (v:real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "sig0" THEN REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `{u0:real^N}`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e0:real^N->bool) SUBSET P` THEN UNDISCH_TAC `(u0:real^N) IN e0` THEN
      SET_TAC[];
      EXPAND_TAC "sig0" THEN SIMP_TAC[MOI_FCB_LIFT_IN_CONE; CONVEX_SING; IN_SING] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                               IMAGE moi_fcb_lift (e0:real^N->bool)):
                  real^(N,2)finite_sum->bool` THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e0:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ2_TAC THEN
        MAP_EVERY EXISTS_TAC [`P:real^N->bool`; `e0:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE];
        EXPAND_TAC "sig0" THEN MATCH_MP_TAC MOI_FCB_CONE_FACE_CONE THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `A = IMAGE moi_fcb_lift (UNIONS (simplicial_link c (v:real^N))):
                  real^(N,2)finite_sum->bool` THEN
  SUBGOAL_THEN `A SUBSET UNIONS (simplicial_link (moi_fcb_cap c ix)
                                   (moi_fcb_lift (v:real^N)))` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (g:real^N->bool):real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[MOI_FCB_LIFT_IN] THEN
    UNDISCH_TAC `(g:real^N->bool) IN simplicial_link c v` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN EXISTS_TAC `g:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
      EXISTS_TAC `IMAGE moi_fcb_lift (t:real^N->bool):real^(N,2)finite_sum->bool` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_FCB_CAP_IN] THEN DISJ1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[MOI_FCB_LIFT_IN];
        MATCH_MP_TAC MOI_FCB_LIFT_FACE_OF THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (A:real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_FCB_LIFT] THEN
    MATCH_MP_TAC MOI_FCB_LINK_C_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcb_lift (u0:real^N) IN (A:real^(N,2)finite_sum->bool) /\
                moi_fcb_lift u0 IN sig0 /\
                moi_fcb_apex ((ix:(real^N->bool)->num) P) IN (sig0:real^(N,2)finite_sum->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[MOI_FCB_LIFT_IN; IN_UNIONS] THEN
      EXISTS_TAC `{u0:real^N}` THEN REWRITE_TAC[IN_SING] THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
      EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "sig0" THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_INSERT; IMAGE_CLAUSES];
      EXPAND_TAC "sig0" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE `!a:A s t. a IN s /\ s SUBSET t ==> ~(t = {})`) THEN
    EXISTS_TAC `moi_fcb_lift (u0:real^N)` THEN
    EXISTS_TAC `A:real^(N,2)finite_sum->bool` THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC MOI_FCB_CONNECTED_STAR THEN
  EXISTS_TAC `A UNION sig0:real^(N,2)finite_sum->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "sig0" THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
      REWRITE_TAC[CONVEX_CONVEX_HULL];
      ASM SET_TAC[]];
    ASM SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^(N,2)finite_sum->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                     `x:real^(N,2)finite_sum->bool`] MOI_FCB_SC_CONVEX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC
         `(x:real^(N,2)finite_sum->bool) IN
          simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)` THEN
        SIMP_TAC[simplicial_link; IN_ELIM_THM];
        SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^(N,2)finite_sum->bool = {}` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `v:real^N`;
                   `x:real^(N,2)finite_sum->bool`] MOI_FCB_CAP_LINK_MEMBER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)) THENL
     [SUBGOAL_THEN `(x:real^(N,2)finite_sum->bool) SUBSET A` MP_TAC THENL
       [UNDISCH_TAC `x = IMAGE moi_fcb_lift (g:real^N->bool):real^(N,2)finite_sum->bool` THEN
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "A" THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(x:real^(N,2)finite_sum->bool = {})` THEN SET_TAC[]];
      SUBGOAL_THEN `Q:real^N->bool = P` SUBST_ALL_TAC THENL
       [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `Q:real^N->bool`;
                       `P:real^N->bool`] COMPONENTS_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(v:real^N) IN Q` THEN UNDISCH_TAC `(v:real^N) IN P` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN
                   (x:real^(N,2)finite_sum->bool)` THEN
      UNDISCH_TAC `moi_fcb_apex ((ix:(real^N->bool)->num) P) IN (sig0:real^(N,2)finite_sum->bool)` THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* The capped complex is a closed combinatorial surface: links at interior   *)
(* lifted vertices are lifted links, at lifted boundary vertices connected   *)
(* degree-2 graphs (circles), at apexes the lifted component.                *)
(* ========================================================================= *)

let MOI_FCB_CAP_SPHERE_INT = prove
 (`!(c:(real^N->bool)->bool) ix v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     ~(v IN surface_boundary c)
     ==> pl_sphere 1 (UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\ simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
        MOI_FCB_CAP_CONTEXT) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FCB_CAP_LINK_INT] THEN
  REWRITE_TAC[GSYM IMAGE_UNIONS] THEN
  MP_TAC(ISPECL [`moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `UNIONS (simplicial_link c (v:real^N))`; `1`]
    MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_FCB_LIFT] THEN MATCH_MP_TAC MOI_FM3_LINK_POLYHEDRON THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MATCH_MP_TAC MOI_FGB_CMB2_VERTEX_INT THEN ASM_REWRITE_TAC[]);;

let MOI_FCB_CAP_SPHERE_APEX = prove
 (`!(c:(real^N->bool)->bool) ix P.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     P IN components (surface_boundary c) /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> pl_sphere 1 (UNIONS (simplicial_link (moi_fcb_cap c ix)
                                (moi_fcb_apex (ix P))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
      MOI_FCB_CAP_CONTEXT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FCB_CAP_LINK_APEX] THEN
  MP_TAC(ISPECL [`moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `P:real^N->bool`; `1`] MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_FCB_LIFT] THEN REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{s | s IN c /\ s SUBSET (P:real^N->bool)}` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_SIMP_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
          MOI_FCB_BD_COVER) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        MESON_TAC[SUBSET]]];
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_BD_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FCB_CAP_SPHERE_BD = prove
 (`!(c:(real^N->bool)->bool) ix v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     v IN surface_boundary c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> pl_sphere 1 (UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift v)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{moi_fcb_lift (v:real^N)} IN moi_fcb_cap c ix` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FCB_CAP_VERTEX] THEN DISJ1_TAC THEN EXISTS_TAC `v:real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `v:real^N`]
    MOI_FCB_CAP_LINK_CONN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift (v:real^N))`
    MOI_S4L_CM1_CIRCLES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2] THEN
      MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
      MATCH_MP_TAC MOI_FM3_LINK_SC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real^(N,2)finite_sum->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S8TB_LINK_DIM THEN
      EXISTS_TAC `moi_fcb_cap (c:(real^N->bool)->bool) ix` THEN
      EXISTS_TAC `moi_fcb_lift (v:real^N)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `a:real^(N,2)finite_sum` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_FCB_CAP_LINK_DEG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPEC `UNIONS (simplicial_link (moi_fcb_cap c ix) (moi_fcb_lift (v:real^N)))`
    COMPONENTS_EQ_SING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_SING] THEN
  MESON_TAC[]);;

let MOI_FCB_CAP_CM2 = prove
 (`!(c:(real^N->bool)->bool) ix.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> FINITE (moi_fcb_cap c ix) /\ combinatorial_manifold 2 (moi_fcb_cap c ix)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (moi_fcb_cap (c:(real^N->bool)->bool) ix)` THEN
    SIMP_TAC[simplicial_complex];
    ALL_TAC] THEN
  REWRITE_TAC[combinatorial_manifold] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  X_GEN_TAC `w:real^(N,2)finite_sum` THEN ASM_SIMP_TAC[MOI_FCB_CAP_VERTEX] THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))
    (X_CHOOSE_THEN `P:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THENL
   [ASM_CASES_TAC `(v:real^N) IN surface_boundary c` THENL
     [MATCH_MP_TAC MOI_FCB_CAP_SPHERE_BD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FCB_CAP_SPHERE_INT THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FCB_CAP_SPHERE_APEX THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The geometry of the cap: the cone of a boundary component, the union of   *)
(* the cap, intersections of the cones with the lifted surface and with each *)
(* other, compactness, both sides accumulating on each lifted component, the *)
(* lifted surface as a subcomplex, components as polyhedra with lifted PL    *)
(* circles, injective indices, and open sets of the cap around one lifted    *)
(* component that miss the other cones.                                      *)
(* ========================================================================= *)

(* The cone of the cap over a boundary component P.                           *)

let moi_fcb_cone = new_definition
 `moi_fcb_cone (c:(real^N->bool)->bool) (ix:(real^N->bool)->num) P =
    UNIONS {convex hull (moi_fcb_apex (ix P) INSERT IMAGE moi_fcb_lift s):
              real^(N,2)finite_sum->bool | s | s IN c /\ s SUBSET P}`;;

let MOI_FCB_CAP_UNIONS = prove
 (`!(c:(real^N->bool)->bool) ix.
     UNIONS (moi_fcb_cap c ix) =
     IMAGE moi_fcb_lift (UNIONS c) UNION
     UNIONS {moi_fcb_cone c ix P | P | P IN components (surface_boundary c)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcb_cap; UNIONS_UNION; GSYM IMAGE_UNIONS] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `z:real^(N,2)finite_sum` THEN
  REWRITE_TAC[moi_fcb_cone; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`moi_fcb_cone (c:(real^N->bool)->bool) ix P`; `P:real^N->bool`] THEN
    ASM_REWRITE_TAC[moi_fcb_cone] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `t:real^(N,2)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `t:real^(N,2)finite_sum->bool`)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_UNIONS; IN_ELIM_THM] o check (fun th ->
      is_binary "IN" (concl th) && lhand(concl th) = `z:real^(N,2)finite_sum`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^(N,2)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`t':real^(N,2)finite_sum->bool`; `P:real^N->bool`;
                          `s:real^N->bool`] THEN
    ASM_MESON_TAC[]]);;




let MOI_FCB_CONE_COMPACT = prove
 (`!(c:(real^N->bool)->bool) ix P.
     simplicial_complex c ==> compact (moi_fcb_cone c ix P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fcb_cone] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC COMPACT_INSERT THEN
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN REWRITE_TAC[MOI_FCB_LIFT] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]]);;

let MOI_FCB_CONE_LIFT = prove
 (`!(c:(real^N->bool)->bool) ix P.
     simplicial_complex c /\ P IN components (surface_boundary c)
     ==> moi_fcb_cone c ix P INTER IMAGE moi_fcb_lift (UNIONS c) = IMAGE moi_fcb_lift P /\
         IMAGE moi_fcb_lift P SUBSET moi_fcb_cone c ix P /\
         IMAGE moi_fcb_lift P SUBSET IMAGE moi_fcb_lift (UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `surface_boundary c:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[surface_boundary] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE moi_fcb_lift P SUBSET moi_fcb_cone c ix (P:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
      MOI_FCB_BD_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[moi_fcb_cone; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                             IMAGE moi_fcb_lift (e:real^N->bool)):
                real^(N,2)finite_sum->bool` THEN
    CONJ_TAC THENL [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_SIMP_TAC[MOI_FCB_LIFT_IN_CONE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fcb_cone; INTER_UNIONS; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MOI_FCB_CONE_INTER_FLAT] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_FCB_CONES_DISJOINT = prove
 (`!(c:(real^N->bool)->bool) ix P Q.
     simplicial_complex c /\ P IN components (surface_boundary c) /\
     Q IN components (surface_boundary c) /\ ~(P = Q) /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q)
     ==> moi_fcb_cone c ix P INTER moi_fcb_cone c ix Q = {} /\
         moi_fcb_cone c ix Q INTER IMAGE moi_fcb_lift P = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P INTER Q:real^N->bool = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `~((ix:(real^N->bool)->num) P = ix Q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_fcb_cone; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^(N,2)finite_sum->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (X_CHOOSE_THEN `y:real^(N,2)finite_sum->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`(ix:(real^N->bool)->num) P`; `(ix:(real^N->bool)->num) Q`;
                   `s:real^N->bool`; `t:real^N->bool`] MOI_FCB_CONE_INTER_DIFF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FCB_SC_CONVEX]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift (s INTER t:real^N->bool)`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      MAP_EVERY UNDISCH_TAC
       [`(s:real^N->bool) SUBSET P`; `(t:real^N->bool) SUBSET Q`;
        `P INTER Q:real^N->bool = {}`] THEN
      SET_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `Q:real^N->bool`]
      MOI_FCB_CONE_LIFT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `P:real^N->bool`]
      MOI_FCB_CONE_LIFT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!a b c d:A->bool. a INTER c = d /\ b SUBSET c /\ d INTER b = {}
                        ==> a INTER b = {}`) THEN
    MAP_EVERY EXISTS_TAC [`IMAGE moi_fcb_lift (UNIONS c):real^(N,2)finite_sum->bool`;
                          `IMAGE moi_fcb_lift Q:real^(N,2)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P INTER Q:real^N->bool = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[MOI_FCB_LIFT]]);;

(* Both sides of the cap accumulate on each lifted boundary component.       *)

let MOI_FCB_CONE_CLOSURE = prove
 (`!(c:(real^N->bool)->bool) ix P.
     simplicial_complex c /\ P IN components (surface_boundary c)
     ==> IMAGE moi_fcb_lift P SUBSET
         closure (moi_fcb_cone c ix P DIFF IMAGE moi_fcb_lift P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
    MOI_FCB_BD_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `segment(moi_fcb_lift (x:real^N),moi_fcb_apex ((ix:(real^N->bool)->num) P)) SUBSET
    moi_fcb_cone c ix P DIFF IMAGE moi_fcb_lift P`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fcb_cone; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull (moi_fcb_apex ((ix:(real^N->bool)->num) P) INSERT
                               IMAGE moi_fcb_lift (e:real^N->bool)):
                  real^(N,2)finite_sum->bool` THEN
      CONJ_TAC THENL [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^(N,2)finite_sum) IN
                   segment(moi_fcb_lift (x:real^N),moi_fcb_apex ((ix:(real^N->bool)->num) P))` THEN
      MATCH_MP_TAC(SET_RULE `!s t z:A. s SUBSET t ==> z IN s ==> z IN t`) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `segment[moi_fcb_lift (x:real^N),
                          moi_fcb_apex ((ix:(real^N->bool)->num) P)]` THEN
      REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(z:real^(N,2)finite_sum) IN
                   segment(moi_fcb_lift (x:real^N),moi_fcb_apex ((ix:(real^N->bool)->num) P))` THEN
      REWRITE_TAC[IN_SEGMENT; IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `sndcart(moi_fcb_lift (y:real^N)) =
        sndcart((&1 - u) % moi_fcb_lift (x:real^N) +
                u % moi_fcb_apex ((ix:(real^N->bool)->num) P):real^(N,2)finite_sum)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FCB_CONE_SND; MOI_FCB_LIFT] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_MUL_COMPONENT;
                  VECTOR_2] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `closure(segment(moi_fcb_lift (x:real^N),
                              moi_fcb_apex ((ix:(real^N->bool)->num) P)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CLOSURE_SEGMENT; MOI_FCB_APEX_NOT_LIFT; ENDS_IN_SEGMENT];
    MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]]);;

let MOI_FCB_LIFT_CLOSURE = prove
 (`!(c:(real^N->bool)->bool) P.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     P IN components (surface_boundary c)
     ==> IMAGE moi_fcb_lift P SUBSET
         closure (IMAGE moi_fcb_lift (UNIONS c) DIFF IMAGE moi_fcb_lift P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(\P. 0):(real^N->bool)->num`]
      MOI_FCB_CAP_CONTEXT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
    MOI_FCB_BD_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `n:int`)) THEN
  SUBGOAL_THEN `relative_interior t INTER (P:real^N->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^N` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `y:real^N`]
      MOI_FCB_BD_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `t INTER e':real^N->bool`; `t:real^N->bool`]
      SUBSET_OF_FACE_OF) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FCB_SC_INTER];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `e':real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN closure (relative_interior t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
    SUBGOAL_THEN `closure t = t:real^N->bool` SUBST1_TAC THENL
     [ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `IMAGE moi_fcb_lift (closure (relative_interior t:real^N->bool)):
              real^(N,2)finite_sum->bool` THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure (IMAGE moi_fcb_lift (relative_interior t:real^N->bool)):
              real^(N,2)finite_sum->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_LINEAR_IMAGE_SUBSET THEN REWRITE_TAC[MOI_FCB_LIFT];
    MATCH_MP_TAC SUBSET_CLOSURE THEN
    SUBGOAL_THEN `relative_interior t SUBSET UNIONS (c:(real^N->bool)->bool)` MP_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      UNDISCH_TAC `relative_interior t INTER (P:real^N->bool) = {}` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; FORALL_IN_IMAGE; IN_IMAGE; EXTENSION; IN_INTER;
                  NOT_IN_EMPTY] THEN
      MESON_TAC[MOI_FCB_LIFT]]]);;



(* The lifted surface is a subcomplex of the cap.                             *)

let MOI_FCB_LIFT_SUBCOMPLEX = prove
 (`!(c:(real^N->bool)->bool) ix.
     simplicial_complex c
     ==> simplicial_subcomplex (IMAGE (IMAGE moi_fcb_lift) c) (moi_fcb_cap c ix) /\
         UNIONS (IMAGE (IMAGE moi_fcb_lift) c) = IMAGE moi_fcb_lift (UNIONS c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_UNIONS; simplicial_subcomplex] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FCB_CAP_IN] THEN MESON_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `f:real^(N,2)finite_sum->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
      MATCH_MP MOI_FCB_LIFT_FACES) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[MOI_FCB_SC_FACES]]);;

(* Boundary components are polyhedra and their lifts are PL circles.         *)

let MOI_FCB_COMP_POLY = prove
 (`!(c:(real^N->bool)->bool) P.
     simplicial_complex c /\ P IN components (surface_boundary c)
     ==> pl_polyhedron P /\ P = UNIONS {s | s IN c /\ s SUBSET P}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `P = UNIONS {s | s IN c /\ s SUBSET (P:real^N->bool)}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
        MOI_FCB_BD_COVER) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{s | s IN c /\ s SUBSET (P:real^N->bool)}` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCB_SC_CONVEX) THEN
    ASM_SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_FCB_LIFT_SPHERE = prove
 (`!(c:(real^N->bool)->bool) P.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     P IN components (surface_boundary c)
     ==> pl_sphere 1 (IMAGE moi_fcb_lift P:real^(N,2)finite_sum->bool) /\
         pl_polyhedron P /\ compact P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(\P. 0):(real^N->bool)->num`]
      MOI_FCB_CAP_CONTEXT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`] MOI_FCB_COMP_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT] THEN
  MP_TAC(ISPECL [`moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `P:real^N->bool`; `1`] MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_FCB_LIFT]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_BD_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* An index injective on the boundary components.                            *)

let MOI_FCB_INDEX_EXISTS = prove
 (`!s:(real^N->bool)->bool.
     FINITE s ==> ?ix:(real^N->bool)->num. !P Q. P IN s /\ Q IN s /\ ix P = ix Q ==> P = Q`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_COUNTABLE) THEN
  REWRITE_TAC[COUNTABLE; ge_c; le_c; IN_UNIV] THEN MESON_TAC[]);;

(* Open sets of the cap around one lifted component missing the other cones *)

let MOI_FCB_UPRIME = prove
 (`!(c:(real^N->bool)->bool) ix P u.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q) /\
     P IN components (surface_boundary c) /\
     open_in (subtopology euclidean (UNIONS c)) u /\ P SUBSET u
     ==> ?U. open_in (subtopology euclidean (UNIONS (moi_fcb_cap c ix))) U /\
             IMAGE moi_fcb_lift P SUBSET U /\
             U SUBSET IMAGE moi_fcb_lift (UNIONS c) UNION moi_fcb_cone c ix P /\
             U INTER IMAGE moi_fcb_lift (UNIONS c) SUBSET IMAGE moi_fcb_lift u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Tz = IMAGE moi_fcb_lift (UNIONS c DIFF u) UNION
                  UNIONS {moi_fcb_cone c ix Q | Q | Q IN components (surface_boundary c) /\
                                                   ~(Q = P)}:real^(N,2)finite_sum->bool` THEN
  SUBGOAL_THEN `closed (Tz:real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tz" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
      REWRITE_TAC[MOI_FCB_LIFT] THEN
      UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[SET_RULE `s DIFF (s INTER t) = s INTER ((:real^N) DIFF t)`] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[MOI_FCB_SC_CONVEX; SIMPLEX_IMP_COMPACT];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_SIMP_TAC[MOI_FCB_CONE_COMPACT]]];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (moi_fcb_cap c ix) DIFF Tz:real^(N,2)finite_sum->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_UNIONS) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `P:real^N->bool`]
    MOI_FCB_CONE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^(N,2)finite_sum) DIFF Tz` THEN
    ASM_REWRITE_TAC[GSYM closed] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN ASM SET_TAC[];
      EXPAND_TAC "Tz" THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^(N,2)finite_sum) IN IMAGE moi_fcb_lift P` THEN
        UNDISCH_TAC `(P:real^N->bool) SUBSET u` THEN
        REWRITE_TAC[IN_IMAGE; IN_DIFF; SUBSET] THEN MESON_TAC[MOI_FCB_LIFT];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `t:real^(N,2)finite_sum->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Q:real^N->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`;
                       `P:real^N->bool`; `Q:real^N->bool`] MOI_FCB_CONES_DISJOINT) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    UNDISCH_TAC `UNIONS (moi_fcb_cap (c:(real^N->bool)->bool) ix) =
                 IMAGE moi_fcb_lift (UNIONS c) UNION
                 UNIONS {moi_fcb_cone c ix P | P | P IN components (surface_boundary c)}` THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "Tz" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    MESON_TAC[];
    EXPAND_TAC "Tz" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNION; IN_IMAGE] THEN
    MESON_TAC[]]);;

