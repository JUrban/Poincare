(* ========================================================================= *)
(* pc_moi_s33_z2b: main theorem Z2_CHAR : |- MOI_S33_Z2_CHAR                *)
(* (pc_moi_s33_stmt.ml).  For a finite connected lf complex c the           *)
(* simplicial classes moi_s33_h1z2 c and the loop characters of UNIONS c    *)
(* have the same number: the parity of a cocycle along Lebesgue chains of a *)
(* loop (open vertex stars) is a character, and every character arises from *)
(* exactly one class.                                                       *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s30_z2c.ml";;
needs "src/pc_moi_star.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: parity of a cochain along a vertex sequence; the triangle and    *)
(* square relations of a cocycle; ladders; refinement; reversal.            *)
(* ========================================================================= *)

let moi_s3zb_ez = new_definition
 `moi_s3zb_ez (z:(real^N->bool)->bool) (u:real^N) v <=> ~(u = v) /\ segment[u,v] IN z`;;

let moi_s3zb_par = define
 `(moi_s3zb_par (z:(real^N->bool)->bool) (v:num->real^N) 0 <=> F) /\
  (moi_s3zb_par z v (SUC m) <=>
     ~(moi_s3zb_par z v m <=> moi_s3zb_ez z (v m) (v (SUC m))))`;;

let MOI_S3ZB_EZ_SYM = prove
 (`!(z:(real^N->bool)->bool) u v. moi_s3zb_ez z u v <=> moi_s3zb_ez z v u`,
  REWRITE_TAC[moi_s3zb_ez; SEGMENT_SYM] THEN MESON_TAC[]);;

let MOI_S3ZB_EZ_REFL = prove
 (`!(z:(real^N->bool)->bool) u. ~moi_s3zb_ez z u u`,
  REWRITE_TAC[moi_s3zb_ez]);;

let MOI_S3ZB_PAR_ADD = prove
 (`!(z:(real^N->bool)->bool) x a b.
     moi_s3zb_par z x (a + b) <=>
     ~(moi_s3zb_par z x a <=> moi_s3zb_par z (\i. x(a + i)) b)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[moi_s3zb_par; ADD_CLAUSES] THEN CONV_TAC TAUT);;

let MOI_S3ZB_PAR_EQ = prove
 (`!(z:(real^N->bool)->bool) x y m.
     (!i. i <= m ==> x i = y i)
     ==> (moi_s3zb_par z x m <=> moi_s3zb_par z y m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[moi_s3zb_par] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(x:num->real^N) m = y m /\ x (SUC m) = y (SUC m)`
    (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let MOI_S3ZB_PAR_BLOCK = prove
 (`!(z:(real^N->bool)->bool) x k.
     1 <= k /\ (!i. i < k ==> x i = x 0)
     ==> (moi_s3zb_par z x k <=> moi_s3zb_ez z (x 0) (x k))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[moi_s3zb_par] THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[moi_s3zb_par; ARITH; MOI_S3ZB_EZ_REFL] THEN
    REWRITE_TAC[ONE] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(x:num->real^N) k = x 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOI_S3ZB_EZ_REFL]);;

let MOI_S3ZB_PAR_REFINE = prove
 (`!(z:(real^N->bool)->bool) v k.
     1 <= k
     ==> !m. moi_s3zb_par z (\i. v (i DIV k)) (m * k) <=> moi_s3zb_par z v m`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; moi_s3zb_par] THEN
  REWRITE_TAC[MOI_S3ZB_PAR_ADD] THEN FIRST_X_ASSUM(SUBST1_TAC o check (is_iff o concl)) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`;
                 `\i. (\i. (v:num->real^N) (i DIV k)) (m * k + i)`; `k:num`]
    MOI_S3ZB_PAR_BLOCK) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 0 < k`; DIV_LT; ADD_CLAUSES];
    DISCH_THEN SUBST1_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; DIV_REFL; ARITH_RULE `~(k = 0) ==> 0 < k`; DIV_LT;
               ADD_CLAUSES] THEN
  REWRITE_TAC[ADD1]);;

let MOI_S3ZB_PAR_FIRST = prove
 (`!(z:(real^N->bool)->bool) x m.
     moi_s3zb_par z x (SUC m) <=>
     ~(moi_s3zb_ez z (x 0) (x 1) <=> moi_s3zb_par z (\i. x(SUC i)) m)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `x:num->real^N`; `1`; `m:num`]
    MOI_S3ZB_PAR_ADD) THEN
  REWRITE_TAC[ARITH_RULE `1 + i = SUC i`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ONE; moi_s3zb_par] THEN CONV_TAC TAUT);;

let MOI_S3ZB_PAR_REV = prove
 (`!(z:(real^N->bool)->bool) m w.
     moi_s3zb_par z (\i. w(m - i)) m <=> moi_s3zb_par z w m`,
  GEN_TAC THEN INDUCT_TAC THENL [REWRITE_TAC[moi_s3zb_par]; ALL_TAC] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MOI_S3ZB_PAR_FIRST] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 moi_s3zb_par] THEN
  REWRITE_TAC[ARITH_RULE `SUC m - SUC i = m - i`; SUB_0; ARITH_RULE `SUC m - 1 = m`] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MOI_S3ZB_EZ_SYM] THEN CONV_TAC TAUT);;

let MOI_S3ZB_PAR_SYMDIFF = prove
 (`!(z:(real^N->bool)->bool) z' v m.
     moi_s3zb_par ((z DIFF z') UNION (z' DIFF z)) v m <=>
     ~(moi_s3zb_par z v m <=> moi_s3zb_par z' v m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[moi_s3zb_par; moi_s3zb_ez; IN_UNION; IN_DIFF] THEN
  CONV_TAC TAUT);;

let MOI_S3ZB_SIMPLEX_VERTS = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ t IN c
     ==> ?V. ~affine_dependent V /\ t = convex hull V /\
             !x. {x} IN c /\ x IN t ==> x IN V`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[simplex; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:int`; `V:real^N->bool`] THEN STRIP_TAC THEN
  EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `x:real^N`]
    MOI_FN1_VERTEX_EXTREME) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_S3ZB_FACE_VERTS = prove
 (`!c t (S:real^N->bool).
     lf_simplicial_complex c /\ t IN c /\ (!x. x IN S ==> {x} IN c /\ x IN t)
     ==> convex hull S IN c /\ ~affine_dependent S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S3ZB_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(S:real^N->bool) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `convex hull (S:real^N->bool) face_of t` MP_TAC THENL
     [UNDISCH_TAC `t = convex hull (V:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[lf_simplicial_complex]];
    ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]]);;

let MOI_S3ZB_ADJ = prove
 (`!c t (u:real^N) v.
     lf_simplicial_complex c /\ t IN c /\ {u} IN c /\ {v} IN c /\ u IN t /\ v IN t
     ==> u = v \/ (segment[u,v] IN c /\ aff_dim(segment[u,v]) = &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u:real^N = v` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_CONVEX_HULL] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `{u:real^N,v}`]
    MOI_S3ZB_FACE_VERTS) THEN
  ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; SIMP_TAC[]]);;

let MOI_S3ZB_CARD3 = prove
 (`!(s1:A) s2 s3 P.
     ~(s1 = s2) /\ ~(s1 = s3) /\ ~(s2 = s3)
     ==> (EVEN (CARD {e | e IN {s1,s2,s3} /\ P e}) <=> (P s1 <=> ~(P s2 <=> P s3)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{e | e IN {s1,s2,s3} /\ (P:A->bool) e} =
    (if P s1 then {s1} else {}) UNION (if P s2 then {s2} else {}) UNION
    (if P s3 then {s3} else {})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`(P:A->bool) s1`; `(P:A->bool) s2`; `(P:A->bool) s3`] THEN
  ASM_REWRITE_TAC[UNION_EMPTY; SET_RULE `{a:A} UNION s = a INSERT s`] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; CARD_SING] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;


let MOI_S3ZB_TRI = prove
 (`!c z (a:real^N) b d t.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     {a} IN c /\ {b} IN c /\ {d} IN c /\ t IN c /\ a IN t /\ b IN t /\ d IN t
     ==> (moi_s3zb_ez z a b <=> ~(moi_s3zb_ez z b d <=> moi_s3zb_ez z d a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a:real^N = b` THENL
   [ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN REWRITE_TAC[MOI_S3ZB_EZ_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `b:real^N = d` THENL
   [ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN REWRITE_TAC[MOI_S3ZB_EZ_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `d:real^N = a` THENL
   [ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN REWRITE_TAC[MOI_S3ZB_EZ_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s3zb_ez] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `{a:real^N,b,d}`]
    MOI_S3ZB_FACE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(convex hull {a:real^N,b,d}) = &2` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `convex hull {a:real^N,b,d}` o CONJUNCT2 o
    GEN_REWRITE_RULE I [z2_cocycle]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{e | e IN z /\ e SUBSET convex hull {a:real^N,b,d}} =
    {e | e IN {segment[a,b], segment[b,d], segment[d,a]} /\ e IN z}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[z2_cocycle]; ALL_TAC] THEN
      SUBGOAL_THEN `(e:real^N->bool) face_of convex hull {a,b,d}` MP_TAC THENL
       [SUBGOAL_THEN `e INTER convex hull {a:real^N,b,d} = e` (SUBST1_TAC o SYM) THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~affine_dependent(S:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(S:real^N->bool) HAS_SIZE 2` MP_TAC THENL
       [UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
        ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
        REWRITE_TAC[INT_ARITH `x - &1:int = &1 <=> x = &2`; INT_OF_NUM_EQ];
        ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `(S:real^N->bool) SUBSET {a,b,d}` THEN
      UNDISCH_TAC `e = convex hull (S:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_EQ] THEN
      UNDISCH_TAC `{x:real^N,y} SUBSET {a,b,d}` THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(x:real^N = y)` THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`segment[a:real^N,b]`; `segment[b:real^N,d]`;
                            `segment[d:real^N,a]`; `\e:real^N->bool. e IN z`]
    MOI_S3ZB_CARD3)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let MOI_S3ZB_SQUARE = prove
 (`!c z (a:real^N) b d e t.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     {a} IN c /\ {b} IN c /\ {d} IN c /\ {e} IN c /\
     t IN c /\ a IN t /\ b IN t /\ d IN t /\ e IN t
     ==> (~(moi_s3zb_ez z a b <=> moi_s3zb_ez z b d) <=>
          ~(moi_s3zb_ez z d e <=> moi_s3zb_ez z e a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `t:real^N->bool`] MOI_S3ZB_TRI) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `a:real^N`; `d:real^N`; `e:real^N`; `t:real^N->bool`] MOI_S3ZB_TRI) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_S3ZB_EZ_SYM] THEN CONV_TAC TAUT);;

let MOI_S3ZB_LADDER = prove
 (`!c z (v:num->real^N) w m.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     (!i. i <= m ==> {v i} IN c /\ {w i} IN c) /\
     (!i. i < m ==> ?t. t IN c /\ v i IN t /\ v (SUC i) IN t /\
                         w i IN t /\ w (SUC i) IN t)
     ==> (~(moi_s3zb_par z v m <=> moi_s3zb_par z w m) <=>
          ~(moi_s3zb_ez z (v 0) (w 0) <=> moi_s3zb_ez z (v m) (w m)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[moi_s3zb_par]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE `i <= m ==> i <= SUC m`; ARITH_RULE `i < m ==> i < SUC m`];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3zb_par] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term is_exists) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `m < SUC m`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `(v:num->real^N) m`; `(v:num->real^N) (SUC m)`;
                 `(w:num->real^N) (SUC m)`; `(w:num->real^N) m`; `t:real^N->bool`]
    MOI_S3ZB_SQUARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
      not (can (find_term is_exists) (concl th)))) THEN
    MESON_TAC[ARITH_RULE `m <= SUC m /\ SUC m <= SUC m`];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3ZB_EZ_SYM] THEN CONV_TAC TAUT);;

let MOI_S3ZB_COB_EDGE = prove
 (`!c y (w:real^N->bool) u v.
     lf_simplicial_complex c /\
     (!e. e IN c /\ aff_dim e = &1
          ==> (e IN y <=> ODD (CARD {x | x IN w /\ x IN e /\ {x} IN c}))) /\
     {u} IN c /\ {v} IN c /\ (u = v \/ segment[u,v] IN c)
     ==> (moi_s3zb_ez y u v <=> ~(u IN w <=> v IN w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL [ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s3zb_ez] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `segment[u:real^N,v]`) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `{x | x IN w /\ x IN segment[u,v] /\ {x} IN c} = {x | x IN {u:real^N,v} /\ x IN w}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[u:real^N,v]`; `x:real^N`]
        MOI_FN1_VERTEX_EXTREME) THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
      STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`(u:real^N) IN w`; `(v:real^N) IN w`] THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {u,v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {u}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC]] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; CARD_SING] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_S3ZB_PAR_COB = prove
 (`!c y (w:real^N->bool) v m.
     lf_simplicial_complex c /\
     (!e. e IN c /\ aff_dim e = &1
          ==> (e IN y <=> ODD (CARD {x | x IN w /\ x IN e /\ {x} IN c}))) /\
     (!i. i <= m ==> {v i} IN c) /\
     (!i. i < m ==> v i = v (SUC i) \/ segment[v i,v (SUC i)] IN c)
     ==> (moi_s3zb_par y v m <=> ~(v 0 IN w <=> v m IN w))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[moi_s3zb_par]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[moi_s3zb_par] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`; `w:real^N->bool`;
                 `(v:num->real^N) m`; `(v:num->real^N) (SUC m)`] MOI_S3ZB_COB_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && not(can (find_term is_disj) (concl th)) &&
        not(can (find_term ((=) `y:(real^N->bool)->bool`)) (concl th)))) THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && not(can (find_term is_disj) (concl th)) &&
        not(can (find_term ((=) `y:(real^N->bool)->bool`)) (concl th)))) THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term is_disj) (concl th))) THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT]);;

(* ========================================================================= *)
(* Part 2: open vertex stars (moi_sta_open_star of pc_moi_star): common     *)
(* simplices, vertices in stars, star-shapedness at the vertex, open edges, *)
(* and a Lebesgue number for the star cover pulled back by a map.           *)
(* ========================================================================= *)

let MOI_S3ZB_STAR_IN = prove
 (`!c (w:real^N) x t.
     x IN moi_sta_open_star c w /\ t IN c /\ x IN t ==> w IN t`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3ZB_STAR_UNIONS = prove
 (`!c (w:real^N) x. x IN moi_sta_open_star c w ==> x IN UNIONS c`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3ZB_STAR_COMMON = prove
 (`!c (x:real^N). x IN UNIONS c ==> ?t. t IN c /\ x IN t /\
        !w. x IN moi_sta_open_star c w ==> w IN t`,
  REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[MOI_S3ZB_STAR_IN]);;

let MOI_S3ZB_STAR_VERTEX = prove
 (`!c (x:real^N) w. {x} IN c /\ x IN moi_sta_open_star c w ==> x = w`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N}`) THEN ASM_REWRITE_TAC[IN_SING] THEN
  MESON_TAC[]);;

let MOI_S3ZB_STAR_SELF = prove
 (`!c (v:real^N). {v} IN c ==> v IN moi_sta_open_star c v`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN
  MESON_TAC[IN_SING]);;

let MOI_S3ZB_STAR_SEGMENT = prove
 (`!c (w:real^N) x.
     lf_simplicial_complex c /\ x IN moi_sta_open_star c w
     ==> segment[w,x] SUBSET moi_sta_open_star c w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FM3_CARRIER_VERTEX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `v0:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN s /\ x IN s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ZB_STAR_IN THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    UNDISCH_TAC `(x:real^N) IN moi_sta_open_star c w` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN relative_interior s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:real`; `w:real^N`; `x:real^N`]
      IN_RELATIVE_INTERIOR_CONVEX_SHRINK) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `t:real^N->bool`;
                   `y:real^N`] MOI_FM3_LF_RELINT_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_S3ZB_OPEN_EDGE_STAR = prove
 (`!c (u:real^N) v y.
     lf_simplicial_complex c /\ segment[u,v] IN c /\ ~(u = v) /\ y IN segment(u,v)
     ==> y IN moi_sta_open_star c u /\ y IN moi_sta_open_star c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN relative_interior(segment[u,v])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[u:real^N,v]` THEN
    ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[u:real^N,v]`; `t:real^N->bool`;
                 `y:real^N`] MOI_FM3_LF_RELINT_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET]);;

let MOI_S3ZB_STAR_LEBESGUE = prove
 (`!c (f:real^M->real^N) s.
     lf_simplicial_complex c /\ compact s /\ f continuous_on s /\
     IMAGE f s SUBSET UNIONS c
     ==> ?e. &0 < e /\
             !x. x IN s ==> ?w. {w} IN c /\
                               !y. y IN s /\ y IN ball(x,e)
                                   ==> f y IN moi_sta_open_star c w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^M->bool` HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `{u:real^M->bool | open u /\
                      ?w:real^N. {w} IN c /\
                                 !y. y IN s /\ y IN u ==> f y IN moi_sta_open_star c w}`) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(f:real^M->real^N) x`]
      MOI_STA_OPEN_STAR_COVER) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `UNIONS c:real^N->bool`;
                   `moi_sta_open_star c (w:real^N)`] CONTINUOUS_OPEN_IN_PREIMAGE_GEN) THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `w:real^N` THEN ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N` THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Part 3: interval chains of a loop (the intervals [i/m,(i+1)/m] mapped    *)
(* into the open stars of v i), the loop parity lpar of a cocycle, its      *)
(* independence of the chain, free homotopy invariance, additivity.         *)
(* ========================================================================= *)

let moi_s3zb_ichain = new_definition
 `moi_s3zb_ichain (c:(real^N->bool)->bool) (p:real^1->real^N) m (v:num->real^N) <=>
    1 <= m /\ v m = v 0 /\
    !i. i < m ==> {v i} IN c /\
                  !t. &i <= &m * drop t /\ &m * drop t <= &(SUC i)
                      ==> p t IN moi_sta_open_star c (v i)`;;

let moi_s3zb_lpar = new_definition
 `moi_s3zb_lpar (c:(real^N->bool)->bool) z (p:real^1->real^N) <=>
    ?m v. moi_s3zb_ichain c p m v /\ moi_s3zb_par z v m`;;

let MOI_S3ZB_ICHAIN_UNIT = prove
 (`!m i t. i < m /\ &i <= &m * drop t /\ &m * drop t <= &(SUC i)
           ==> t IN interval[vec 0,vec 1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(SUC i) <= &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < &m`))] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
  MP_TAC(SPEC `i:num` REAL_POS) THEN ASM_REAL_ARITH_TAC);;

let MOI_S3ZB_ICHAIN_CONG = prove
 (`!c (p:real^1->real^N) q m v.
     (!t. t IN interval[vec 0,vec 1] ==> p t = q t)
     ==> (moi_s3zb_ichain c p m v <=> moi_s3zb_ichain c q m v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN
  SUBGOAL_THEN
   `!i t. i < m /\ &i <= &m * drop t /\ &m * drop t <= &(SUC i)
          ==> (p:real^1->real^N) t = q t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S3ZB_ICHAIN_UNIT THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `i:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S3ZB_ICHAIN_EXISTS = prove
 (`!c (p:real^1->real^N).
     lf_simplicial_complex c /\ path p /\ path_image p SUBSET UNIONS c
     ==> ?m v. moi_s3zb_ichain c p m v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `interval[vec 0:real^1,vec 1]`] MOI_S3ZB_STAR_LEBESGUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[path; path_image];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i < m ==> ?w:real^N. {w} IN c /\
          !t. &i <= &m * drop t /\ &m * drop t <= &(SUC i)
              ==> p t IN moi_sta_open_star c w`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(&i / &m)`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `~(m = 0) ==> 0 < m`; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ZB_ICHAIN_UNIT THEN
      MAP_EVERY EXISTS_TAC [`m:num`; `i:num`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&m)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&i / &m - drop t = (&i - &m * drop t) / &m` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&i <= &m * drop t` THEN UNDISCH_TAC `&m * drop t <= &(SUC i)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num->real^N`) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `\i. if i = m then (w:num->real^N) 0 else w i`] THEN
  REWRITE_TAC[moi_s3zb_ichain] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[COND_ID]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(i:num = m)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[]]);;

let MOI_S3ZB_ICHAIN_REFINE = prove
 (`!c (p:real^1->real^N) m v k.
     moi_s3zb_ichain c p m v /\ 1 <= k
     ==> moi_s3zb_ichain c p (m * k) (\i. v (i DIV k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0) /\ ~(m = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT; DIV_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i DIV k < m` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i DIV k`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`i:num`; `k:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = i DIV k` THEN ABBREV_TAC `r = i MOD k` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&i = &j * &k + &r /\ &r + &1 <= &k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < &k`))] THEN
  UNDISCH_TAC `&i <= &(m * k) * drop t` THEN UNDISCH_TAC `&(m * k) * drop t <= &(SUC i)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `r:num` REAL_POS) THEN
  UNDISCH_TAC `&r + &1 <= &k` THEN UNDISCH_TAC `&i = &j * &k + &r` THEN
  REAL_ARITH_TAC);;

let MOI_S3ZB_ICHAIN_POINT = prove
 (`!c (p:real^1->real^N) m v i.
     moi_s3zb_ichain c p m v /\ pathfinish p = pathstart p /\ i < m
     ==> p(lift(&(SUC i) / &m)) IN moi_sta_open_star c (v i) /\
         p(lift(&(SUC i) / &m)) IN moi_sta_open_star c (v (SUC i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&m = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&m * drop(lift(&(SUC i) / &m)) = &(SUC i)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `SUC i < m` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC i = m` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; LIFT_NUM] THEN
  UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart p` THEN
  REWRITE_TAC[pathfinish; pathstart] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC);;

let MOI_S3ZB_ICHAIN_SAME = prove
 (`!c z (p:real^1->real^N) m v w.
     lf_simplicial_complex c /\ z2_cocycle c z /\ pathfinish p = pathstart p /\
     moi_s3zb_ichain c p m v /\ moi_s3zb_ichain c p m w
     ==> (moi_s3zb_par z v m <=> moi_s3zb_par z w m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `v:num->real^N`; `w:num->real^N`; `m:num`] MOI_S3ZB_LADDER) THEN
  SUBGOAL_THEN `(v:num->real^N) m = v 0 /\ (w:num->real^N) m = w 0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_ichain]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; CONV_TAC TAUT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!u:num->real^N. moi_s3zb_ichain c p m u ==> {u i} IN c` MP_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
      ASM_CASES_TAC `i:num = m` THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`;
                 `v:num->real^N`; `i:num`] MOI_S3ZB_ICHAIN_POINT) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`;
                 `w:num->real^N`; `i:num`] MOI_S3ZB_ICHAIN_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(p:real^1->real^N)(lift(&(SUC i) / &m))`]
    MOI_S3ZB_STAR_COMMON) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3ZB_ICHAIN_UNIQUE = prove
 (`!c z (p:real^1->real^N) m v m' w.
     lf_simplicial_complex c /\ z2_cocycle c z /\ pathfinish p = pathstart p /\
     moi_s3zb_ichain c p m v /\ moi_s3zb_ichain c p m' w
     ==> (moi_s3zb_par z v m <=> moi_s3zb_par z w m')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m /\ 1 <= m'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_ichain]; ALL_TAC] THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `v:num->real^N`; `m':num`]
    MOI_S3ZB_PAR_REFINE) THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `w:num->real^N`; `m:num`]
    MOI_S3ZB_PAR_REFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(SPEC `m':num` th)]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(SPEC `m:num` th)]) THEN
  SUBST1_TAC(SPECL [`m':num`; `m:num`] MULT_SYM) THEN
  MATCH_MP_TAC MOI_S3ZB_ICHAIN_SAME THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `p:real^1->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_ICHAIN_REFINE THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOI_S3ZB_ICHAIN_REFINE THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_LPAR_EQ = prove
 (`!c z (p:real^1->real^N) m v.
     lf_simplicial_complex c /\ z2_cocycle c z /\ pathfinish p = pathstart p /\
     moi_s3zb_ichain c p m v
     ==> (moi_s3zb_lpar c z p <=> moi_s3zb_par z v m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3zb_lpar] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `m':num` (X_CHOOSE_THEN `w:num->real^N` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `p:real^1->real^N`;
                   `m:num`; `v:num->real^N`; `m':num`; `w:num->real^N`]
      MOI_S3ZB_ICHAIN_UNIQUE) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`m:num`; `v:num->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_GRID_1 = prove
 (`!M i t. ~(M = 0) /\ &i <= &M * drop t /\ &M * drop t <= &(SUC i)
           ==> abs(&i / &M - drop t) <= inv(&M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&i / &M - drop t = (&i - &M * drop t) / &M` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&i <= &M * drop t` THEN UNDISCH_TAC `&M * drop t <= &(SUC i)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let MOI_S3ZB_GRID_BALL = prove
 (`!M i j t x e.
     ~(M = 0) /\ inv(&M) < e / &2 /\
     &i <= &M * drop t /\ &M * drop t <= &(SUC i) /\
     &j <= &M * drop x /\ &M * drop x <= &(SUC j)
     ==> pastecart t x IN ball(pastecart (lift(&i / &M)) (lift(&j / &M)), e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL; dist; PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(lift(&i / &M) - t) + norm(lift(&j / &M) - x)` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  REWRITE_TAC[NORM_REAL; VECTOR_SUB_COMPONENT; GSYM drop; LIFT_DROP] THEN
  MP_TAC(SPECL [`M:num`; `i:num`; `t:real^1`] MOI_S3ZB_GRID_1) THEN
  MP_TAC(SPECL [`M:num`; `j:num`; `x:real^1`] MOI_S3ZB_GRID_1) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3ZB_LPAR_HOMOTOPIC = prove
 (`!c z (p:real^1->real^N) q.
     lf_simplicial_complex c /\ z2_cocycle c z /\ homotopic_loops (UNIONS c) p q
     ==> (moi_s3zb_lpar c z p <=> moi_s3zb_lpar c z q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMOTOPIC_LOOPS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^(1,1)finite_sum->real^N`;
                 `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]`]
    MOI_S3ZB_STAR_LEBESGUE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i j. i < M /\ j < M
          ==> ?w:real^N. {w} IN c /\
                !t x. &i <= &M * drop t /\ &M * drop t <= &(SUC i) /\
                      &j <= &M * drop x /\ &M * drop x <= &(SUC j)
                      ==> h(pastecart t x) IN moi_sta_open_star c w`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `pastecart (lift(&i / &M)) (lift(&j / &M)):real^(1,1)finite_sum`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `~(m = 0) ==> 0 < m`; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS] THEN CONJ_TAC THEN
      MATCH_MP_TAC MOI_S3ZB_ICHAIN_UNIT THENL
       [MAP_EVERY EXISTS_TAC [`M:num`; `i:num`]; MAP_EVERY EXISTS_TAC [`M:num`; `j:num`]] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3ZB_GRID_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `u:num->num->real^N`) THEN
  SUBGOAL_THEN
   `!i t. i < M /\ &i <= &M * drop t /\ &M * drop t <= &(SUC i)
          ==> moi_s3zb_ichain c (\x. (h:real^(1,1)finite_sum->real^N)(pastecart t x)) M
                                (\j. u i (j MOD M))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[MOD_REFL; MOD_0];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[MOD_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0:real^1,vec 1]
        ==> pathfinish(\x. (h:real^(1,1)finite_sum->real^N)(pastecart t x)) =
            pathstart(\x. h(pastecart t x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `pathfinish:(real^1->real^N)->real^N`))
                                   (concl th))) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < M ==> (moi_s3zb_par z (\j. (u:num->num->real^N) i (j MOD M)) M <=>
                   moi_s3zb_par z (\j. u 0 (j MOD M)) M)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S3ZB_ICHAIN_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`c:(real^N->bool)->bool`;
      `\x. (h:real^(1,1)finite_sum->real^N)(pastecart (lift(&(SUC i) / &M)) x)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&M * drop(lift(&(SUC i) / &M)) = &(SUC i)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_OF_NUM_EQ]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `~(m = 0) ==> 0 < m`; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3zb_ichain c p M (\j. (u:num->num->real^N) 0 (j MOD M)) /\
    moi_s3zb_ichain c q M (\j. u (M - 1) (j MOD M))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`;
                     `\x. (h:real^(1,1)finite_sum->real^N)(pastecart (vec 0) x)`;
                     `M:num`; `\j. (u:num->num->real^N) 0 (j MOD M)`]
        MOI_S3ZB_ICHAIN_CONG) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^1->real^N`;
                     `\x. (h:real^(1,1)finite_sum->real^N)(pastecart (vec 1) x)`;
                     `M:num`; `\j. (u:num->num->real^N) (M - 1) (j MOD M)`]
        MOI_S3ZB_ICHAIN_CONG) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[DROP_VEC; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(M = 0) ==> SUC(M - 1) = M`; REAL_LE_REFL;
                   REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `M:num`; `\j. (u:num->num->real^N) 0 (j MOD M)`] MOI_S3ZB_LPAR_EQ) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `q:real^1->real^N`;
                 `M:num`; `\j. (u:num->num->real^N) (M - 1) (j MOD M)`] MOI_S3ZB_LPAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MOI_S3ZB_ICHAIN_JOIN = prove
 (`!c (p:real^1->real^N) q M v w.
     moi_s3zb_ichain c p M v /\ moi_s3zb_ichain c q M w /\ pathfinish p = pathstart q
     ==> moi_s3zb_ichain c (p ++ q) (M + M)
           (\i. if i < M then v i else if i < M + M then w (i - M) else v 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[LT_REFL; ARITH_RULE `~(M + M < M:num)`] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= M ==> 0 < M`];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < M:num` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `i < M:num`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `p:real^1->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop t <= &1 / &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&M * (&2 * drop t) <= &M * &1` MP_TAC THENL
       [SUBGOAL_THEN `&(SUC i) <= &M` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&(M + M) * drop t <= &(SUC i)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[joinpaths] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[DROP_CMUL] THEN
    UNDISCH_TAC `&i <= &(M + M) * drop t` THEN UNDISCH_TAC `&(M + M) * drop t <= &(SUC i)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i - M < M /\ M <= i:num` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MP (ASSUME `i - M < M:num`) o SPEC `i - M:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q:real^1->real^N`)) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN REWRITE_TAC[joinpaths] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `i:num = M /\ &2 % (t:real^1) = vec 1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&M <= &i` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * &M * drop t = &M` ASSUME_TAC THENL
       [SUBGOAL_THEN `&M * (&2 * drop t) <= &M * &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          UNDISCH_TAC `drop t <= &1 / &2` THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `&i <= &(M + M) * drop t` THEN UNDISCH_TAC `&M <= &i` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
        UNDISCH_TAC `&i <= &(M + M) * drop t` THEN UNDISCH_TAC `&M <= &i` THEN
        UNDISCH_TAC `&2 * &M * drop t = &M` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
        MATCH_MP_TAC(REAL_FIELD `!m x. ~(m = &0) /\ m * x = m * &1 ==> x = &1`) THEN
        EXISTS_TAC `&M` THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < &M` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `&2 * &M * drop t = &M` THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL] THEN
    UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart q` THEN
    REWRITE_TAC[pathfinish; pathstart] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q:real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - M:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `q:real^1->real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[DROP_SUB; DROP_CMUL; DROP_VEC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `M <= i ==> SUC(i - M) = SUC i - M`;
               ARITH_RULE `M <= i ==> M <= SUC i`] THEN
  UNDISCH_TAC `&i <= &(M + M) * drop t` THEN UNDISCH_TAC `&(M + M) * drop t <= &(SUC i)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let MOI_S3ZB_ICHAIN_ENDS = prove
 (`!c (p:real^1->real^N) M v.
     moi_s3zb_ichain c p M v
     ==> pathstart p IN moi_sta_open_star c (v 0) /\
         pathfinish p IN moi_sta_open_star c (v (M - 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
  REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_OF_NUM_LE] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `M - 1`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= M ==> SUC(M - 1) = M`; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
    ARITH_TAC]);;

let MOI_S3ZB_LPAR_JOIN_SAME = prove
 (`!c z (p:real^1->real^N) q M v w.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     pathfinish p = pathstart p /\ pathstart q = pathstart p /\ pathfinish q = pathstart p /\
     moi_s3zb_ichain c p M v /\ moi_s3zb_ichain c q M w
     ==> (moi_s3zb_lpar c z (p ++ q) <=>
          ~(moi_s3zb_par z v M <=> moi_s3zb_par z w M))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= M /\ (v:num->real^N) M = v 0 /\ (w:num->real^N) M = w 0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_s3zb_ichain]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `q:real^1->real^N`;
                 `M:num`; `v:num->real^N`; `w:num->real^N`] MOI_S3ZB_ICHAIN_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = \i. if i < M then (v:num->real^N) i
                      else if i < M + M then w (i - M) else v 0` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `(p:real^1->real^N) ++ q`; `M + M:num`; `x:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOI_S3ZB_PAR_ADD] THEN
  MP_TAC(SPEC `M:num` num_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= M ==> ~(M = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[moi_s3zb_par] THEN
  SUBGOAL_THEN
   `(moi_s3zb_par z x N <=> moi_s3zb_par z (v:num->real^N) N) /\
    (moi_s3zb_par z (\i. (x:num->real^N)(SUC N + i)) N <=> moi_s3zb_par z (w:num->real^N) N)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3ZB_PAR_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXPAND_TAC "x" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= N ==> i < SUC N`; ARITH_RULE `~(SUC N + i < SUC N)`;
                 ARITH_RULE `i <= N ==> SUC N + i < SUC N + SUC N`; ADD_SUB2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:num->real^N) N = v N /\ x (SUC N) = w 0 /\ x(SUC N + N) = w N /\
    x(SUC N + SUC N) = v 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `N < SUC N`; LT_REFL; ARITH_RULE `SUC N < SUC N + SUC N`;
                ARITH_RULE `~(SUC N + N < SUC N)`; ARITH_RULE `SUC N + N < SUC N + SUC N`;
                ARITH_RULE `~(SUC N + SUC N < SUC N)`; ARITH_RULE `~(n + n < n + n:num)`;
                SUB_REFL; ADD_SUB2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `SUC N`; `v:num->real^N`]
    MOI_S3ZB_ICHAIN_ENDS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^1->real^N`; `SUC N`; `w:num->real^N`]
    MOI_S3ZB_ICHAIN_ENDS) THEN
  ASM_REWRITE_TAC[SUC_SUB1] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `pathstart(p:real^1->real^N)`]
    MOI_S3ZB_STAR_COMMON) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `(v:num->real^N) N`; `(w:num->real^N) 0`; `(w:num->real^N) N`;
                 `(v:num->real^N) 0`; `t:real^N->bool`] MOI_S3ZB_SQUARE) THEN
  SUBGOAL_THEN
   `{(v:num->real^N) N} IN c /\ {v 0} IN c /\ {(w:num->real^N) N} IN c /\ {w 0} IN c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3zb_ichain c (p:real^1->real^N) (SUC N) v` THEN
    UNDISCH_TAC `moi_s3zb_ichain c (q:real^1->real^N) (SUC N) w` THEN
    REWRITE_TAC[moi_s3zb_ichain] THEN MESON_TAC[ARITH_RULE `N < SUC N /\ 0 < SUC N`];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3ZB_EZ_SYM] THEN CONV_TAC TAUT);;

let MOI_S3ZB_LPAR_JOIN = prove
 (`!c z (p:real^1->real^N) q.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p /\
     path q /\ path_image q SUBSET UNIONS c /\
     pathstart q = pathstart p /\ pathfinish q = pathstart p
     ==> (moi_s3zb_lpar c z (p ++ q) <=>
          ~(moi_s3zb_lpar c z p <=> moi_s3zb_lpar c z q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_ICHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `v:num->real^N`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^1->real^N`] MOI_S3ZB_ICHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':num` (X_CHOOSE_TAC `w:num->real^N`)) THEN
  SUBGOAL_THEN `1 <= m /\ 1 <= m'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_ichain]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3zb_ichain c p (m * m') (\i. (v:num->real^N) (i DIV m')) /\
    moi_s3zb_ichain c q (m * m') (\i. (w:num->real^N) (i DIV m))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ZB_ICHAIN_REFINE THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOI_S3ZB_ICHAIN_REFINE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `q:real^1->real^N`; `m * m':num`; `\i. (v:num->real^N) (i DIV m')`;
                 `\i. (w:num->real^N) (i DIV m)`] MOI_S3ZB_LPAR_JOIN_SAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `m * m':num`; `\i. (v:num->real^N) (i DIV m')`] MOI_S3ZB_LPAR_EQ) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `q:real^1->real^N`;
                 `m * m':num`; `\i. (w:num->real^N) (i DIV m)`] MOI_S3ZB_LPAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

(* ========================================================================= *)
(* Part 4: point chains of paths (each interval [k/m,(k+1)/m] mapped into   *)
(* the stars of both w k and w (k+1)): existence, ends, refinement,         *)
(* uniqueness of the parity for vertex ends, joins, reversal, linepaths.    *)
(* ========================================================================= *)

let moi_s3zb_pchain = new_definition
 `moi_s3zb_pchain (c:(real^N->bool)->bool) (p:real^1->real^N) m (w:num->real^N) <=>
    1 <= m /\ (!k. k <= m ==> {w k} IN c) /\
    !k t. k < m /\ &k <= &m * drop t /\ &m * drop t <= &(SUC k)
          ==> p t IN moi_sta_open_star c (w k) /\
              p t IN moi_sta_open_star c (w (SUC k))`;;

let MOI_S3ZB_GRID_2 = prove
 (`!M i t. ~(M = 0) /\ &i <= &M * drop t /\ &M * drop t <= &(SUC i)
           ==> abs(&(SUC i) / &M - drop t) <= inv(&M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(SUC i) / &M - drop t = (&(SUC i) - &M * drop t) / &M` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM; real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&i <= &M * drop t` THEN UNDISCH_TAC `&M * drop t <= &(SUC i)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let MOI_S3ZB_PCHAIN_EXISTS = prove
 (`!c (p:real^1->real^N).
     lf_simplicial_complex c /\ path p /\ path_image p SUBSET UNIONS c
     ==> ?m w. moi_s3zb_pchain c p m w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `interval[vec 0:real^1,vec 1]`] MOI_S3ZB_STAR_LEBESGUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN ASM_MESON_TAC[path; path_image];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. k <= m ==> ?w:real^N. {w} IN c /\
          !t. t IN interval[vec 0,vec 1] /\ abs(&k / &m - drop t) <= inv(&m)
              ==> p t IN moi_sta_open_star c w`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(&k / &m)`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                   ARITH_RULE `~(m = 0) ==> 0 < m`; REAL_MUL_LID; REAL_OF_NUM_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num->real^N`) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `w:num->real^N`] THEN
  REWRITE_TAC[moi_s3zb_pchain] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `w:num->real^N`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_ICHAIN_UNIT THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `k:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `w:num->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3ZB_GRID_1 THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o SPEC `SUC k` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `w:num->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3ZB_GRID_2 THEN ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_PCHAIN_ENDS = prove
 (`!c (p:real^1->real^N) m w.
     moi_s3zb_pchain c p m w
     ==> pathstart p IN moi_sta_open_star c (w 0) /\
         pathfinish p IN moi_sta_open_star c (w m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain] THEN STRIP_TAC THEN
  REWRITE_TAC[pathstart; pathfinish] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `vec 0:real^1`]) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`m - 1`; `vec 1:real^1`]) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> SUC(m - 1) = m`; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]]);;

let MOI_S3ZB_PCHAIN_VERTEX_ENDS = prove
 (`!c (p:real^1->real^N) m w.
     moi_s3zb_pchain c p m w
     ==> ({pathstart p} IN c ==> w 0 = pathstart p) /\
         ({pathfinish p} IN c ==> w m = pathfinish p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3ZB_PCHAIN_ENDS) THEN
  MESON_TAC[MOI_S3ZB_STAR_VERTEX]);;

let MOI_S3ZB_PCHAIN_ICHAIN = prove
 (`!c (p:real^1->real^N) m w.
     moi_s3zb_pchain c p m w /\ w m = w 0 ==> moi_s3zb_ichain c p m w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain; moi_s3zb_ichain] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let MOI_S3ZB_PCHAIN_REFINE = prove
 (`!c (p:real^1->real^N) m w k.
     moi_s3zb_pchain c p m w /\ 1 <= k
     ==> moi_s3zb_pchain c p (m * k) (\i. w (i DIV k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0) /\ ~(m = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    TRANS_TAC LE_TRANS `(m * k) DIV k` THEN ASM_SIMP_TAC[DIV_MONO] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT; LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `t:real^1`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `k:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `j = i DIV k` THEN ABBREV_TAC `r = i MOD k` THEN STRIP_TAC THEN
  SUBGOAL_THEN `j < m:num` ASSUME_TAC THENL
   [UNDISCH_TAC `i < m * k:num` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(m <= j) ==> j < m:num`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `m * k <= j * k:num` MP_TAC THENL
     [ASM_SIMP_TAC[LE_MULT_RCANCEL]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&j <= &m * drop t /\ &m * drop t <= &(SUC j)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&i = &j * &k + &r /\ &r + &1 <= &k` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < &k`))] THEN
    UNDISCH_TAC `&i <= &(m * k) * drop t` THEN
    UNDISCH_TAC `&(m * k) * drop t <= &(SUC i)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
    MP_TAC(SPEC `r:num` REAL_POS) THEN
    UNDISCH_TAC `&r + &1 <= &k` THEN UNDISCH_TAC `&i = &j * &k + &r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `t:real^1`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `p:real^1->real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUC (j * k + r) DIV k = j \/ SUC (j * k + r) DIV k = SUC j`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `SUC r < k` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `SUC r` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISJ2_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      try lhs(concl th) = `SUC (j * k + r) DIV k` with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      try lhs(concl th) = `SUC (j * k + r) DIV k` with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_PCHAIN_SAME = prove
 (`!c z (p:real^1->real^N) m w w'.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     moi_s3zb_pchain c p m w /\ moi_s3zb_pchain c p m w' /\
     w 0 = w' 0 /\ w m = w' m
     ==> (moi_s3zb_par z w m <=> moi_s3zb_par z w' m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `w:num->real^N`; `w':num->real^N`; `m:num`] MOI_S3ZB_LADDER) THEN
  ASM_REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN ANTS_TAC THENL [ALL_TAC; CONV_TAC TAUT] THEN
  UNDISCH_TAC `moi_s3zb_pchain c (p:real^1->real^N) m w` THEN
  UNDISCH_TAC `moi_s3zb_pchain c (p:real^1->real^N) m w'` THEN
  REWRITE_TAC[moi_s3zb_pchain] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `&i <= &m * drop(lift(&i / &m)) /\ &m * drop(lift(&i / &m)) <= &(SUC i)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_OF_NUM_EQ;
                 ARITH_RULE `1 <= m ==> ~(m = 0)`; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(p:real^1->real^N)(lift(&i / &m))`]
    MOI_S3ZB_STAR_COMMON) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3ZB_PCHAIN_UNIQUE = prove
 (`!c z (p:real^1->real^N) m w m' w'.
     lf_simplicial_complex c /\ z2_cocycle c z /\
     moi_s3zb_pchain c p m w /\ moi_s3zb_pchain c p m' w' /\
     w 0 = w' 0 /\ w m = w' m'
     ==> (moi_s3zb_par z w m <=> moi_s3zb_par z w' m')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m /\ 1 <= m'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_pchain]; ALL_TAC] THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `w:num->real^N`; `m':num`]
    MOI_S3ZB_PAR_REFINE) THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `w':num->real^N`; `m:num`]
    MOI_S3ZB_PAR_REFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(SPEC `m':num` th)]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(SPEC `m:num` th)]) THEN
  SUBST1_TAC(SPECL [`m':num`; `m:num`] MULT_SYM) THEN
  MATCH_MP_TAC MOI_S3ZB_PCHAIN_SAME THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `p:real^1->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(m = 0) /\ ~(m' = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(m * m') DIV m' = m /\ (m * m') DIV m = m'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIV_0] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_PCHAIN_REFINE THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOI_S3ZB_PCHAIN_REFINE THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_PCHAIN_JOIN = prove
 (`!c (p:real^1->real^N) q M w1 w2.
     moi_s3zb_pchain c p M w1 /\ moi_s3zb_pchain c q M w2 /\
     pathfinish p = pathstart q /\ w1 M = w2 0
     ==> moi_s3zb_pchain c (p ++ q) (M + M)
           (\i. if i <= M then w1 i else w2 (i - M))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `w1:num->real^N`)) (concl th) &&
        not(can (find_term ((=) `p:real^1->real^N`)) (concl th)))) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `w2:num->real^N`)) (concl th) &&
        not(can (find_term ((=) `q:real^1->real^N`)) (concl th)))) THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real^1`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `k < M:num` THENL
   [SUBGOAL_THEN `k <= M /\ SUC k <= M` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `drop t <= &1 / &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&M * (&2 * drop t) <= &M * &1` MP_TAC THENL
       [SUBGOAL_THEN `&(SUC k) <= &M` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `&(M + M) * drop t <= &(SUC k)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[joinpaths] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `p:real^1->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[DROP_CMUL] THEN
    UNDISCH_TAC `&k <= &(M + M) * drop t` THEN
    UNDISCH_TAC `&(M + M) * drop t <= &(SUC k)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M <= k /\ k - M < M /\ ~(SUC k <= M) /\ SUC k - M = SUC(k - M)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(if k <= M then (w1:num->real^N) k else w2 (k - M)) = w2 (k - M)`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `k:num = M` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[joinpaths] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `k:num = M /\ &2 % (t:real^1) = vec 1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&M <= &k` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `&2 * &M * drop t = &M` ASSUME_TAC THENL
       [SUBGOAL_THEN `&M * (&2 * drop t) <= &M * &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          UNDISCH_TAC `drop t <= &1 / &2` THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `&k <= &(M + M) * drop t` THEN UNDISCH_TAC `&M <= &k` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
        UNDISCH_TAC `&k <= &(M + M) * drop t` THEN UNDISCH_TAC `&M <= &k` THEN
        UNDISCH_TAC `&2 * &M * drop t = &M` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
        MATCH_MP_TAC(REAL_FIELD `!m x. ~(m = &0) /\ m * x = m * &1 ==> x = &1`) THEN
        EXISTS_TAC `&M` THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < &M` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `&2 * &M * drop t = &M` THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL] THEN
    UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart q` THEN
    REWRITE_TAC[pathfinish; pathstart] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `vec 0:real^1`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `q:real^1->real^N`)) (concl th))) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_OF_NUM_LE] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ONE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `q:real^1->real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[DROP_SUB; DROP_CMUL; DROP_VEC; GSYM REAL_OF_NUM_SUC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  UNDISCH_TAC `&k <= &(M + M) * drop t` THEN UNDISCH_TAC `&(M + M) * drop t <= &(SUC k)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let MOI_S3ZB_PAR_JOIN = prove
 (`!(z:(real^N->bool)->bool) M w1 w2.
     w1 M = w2 0
     ==> (moi_s3zb_par z (\i. if i <= M then w1 i else w2 (i - M)) (M + M) <=>
          ~(moi_s3zb_par z w1 M <=> moi_s3zb_par z w2 M))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_S3ZB_PAR_ADD] THEN
  AP_TERM_TAC THEN BINOP_TAC THEN MATCH_MP_TAC MOI_S3ZB_PAR_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[];
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL; ADD_SUB2] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> ~(M + i <= M)`]]);;

let MOI_S3ZB_PCHAIN_REV = prove
 (`!c (p:real^1->real^N) m w.
     moi_s3zb_pchain c p m w
     ==> moi_s3zb_pchain c (reversepath p) m (\k. w(m - k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[reversepath] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m - SUC k`; `vec 1 - t:real^1`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `p:real^1->real^N`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DROP_SUB; DROP_VEC] THEN
    ASM_SIMP_TAC[ARITH_RULE `k < m ==> SUC(m - SUC k) = m - k`] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `k < m ==> SUC k <= m`; LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&k <= &m * drop t` THEN UNDISCH_TAC `&m * drop t <= &(SUC k)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `k < m ==> SUC(m - SUC k) = m - k`;
                 ARITH_RULE `m - SUC k = m - k - 1`] THEN
    SIMP_TAC[CONJ_SYM]]);;

let MOI_S3ZB_PCHAIN_LINEPATH = prove
 (`!c (u:real^N) v.
     lf_simplicial_complex c /\ {u} IN c /\ {v} IN c /\ (u = v \/ segment[u,v] IN c)
     ==> moi_s3zb_pchain c (linepath(u,v)) 3 (\k. if k <= 1 then u else v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[moi_s3zb_pchain] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `t:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`3`; `k:num`; `t:real^1`] MOI_S3ZB_ICHAIN_UNIT) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[LINEPATH_REFL; COND_ID] THEN ASM_SIMP_TAC[MOI_S3ZB_STAR_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^N,v] IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < drop t /\ drop t < &1
    ==> linepath(u:real^N,v) t IN moi_sta_open_star c u /\
        linepath(u,v) t IN moi_sta_open_star c v`
  ASSUME_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_S3ZB_OPEN_EDGE_STAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_SEGMENT; linepath] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `drop t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0 < drop t /\ drop t < &1) \/ drop t = &0 \/ drop t = &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&k <= &3 * drop t` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `linepath(u:real^N,v) t = u` SUBST1_TAC THENL
     [REWRITE_TAC[linepath] THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOI_S3ZB_STAR_SELF]];
    SUBGOAL_THEN `k = 2` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&3 * drop t <= &(SUC k)` THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `k < 3` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `linepath(u:real^N,v) t = v` SUBST1_TAC THENL
     [REWRITE_TAC[linepath] THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOI_S3ZB_STAR_SELF]]]);;

let MOI_S3ZB_PAR_LINEPATH = prove
 (`!(z:(real^N->bool)->bool) u v.
     moi_s3zb_par z (\k. if k <= 1 then u else v) 3 <=> moi_s3zb_ez z u v`,
  REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; moi_s3zb_par] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Part 5: a cocycle whose loop parity vanishes on all loops is a           *)
(* coboundary (vertex parities of point chains of paths from a base         *)
(* vertex), hence the parity map on classes is injective.                   *)
(* ========================================================================= *)

let MOI_S3ZB_EDGE_VERTS = prove
 (`!c e:real^N->bool.
     lf_simplicial_complex c /\ e IN c /\ aff_dim e = &1
     ==> ?u v. ~(u = v) /\ {u} IN c /\ {v} IN c /\ e = segment[u,v]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[simplex; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:int`; `V:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    SUBGOAL_THEN `aff_dim(V:real^N->bool) = &(CARD V) - &1` MP_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(V:real^N->bool) = &1` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `!x:real^N. x IN {u,v} ==> {x} IN c`
    (fun th -> MESON_TAC[th; IN_INSERT]) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:real^N} face_of e` MP_TAC THENL
   [REWRITE_TAC[FACE_OF_SING] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ASM_MESON_TAC[lf_simplicial_complex]]);;

let MOI_S3ZB_EDGE_ODD = prove
 (`!c (w:real^N->bool) u v.
     lf_simplicial_complex c /\ {u} IN c /\ {v} IN c /\ ~(u = v) /\ segment[u,v] IN c
     ==> (ODD (CARD {x | x IN w /\ x IN segment[u,v] /\ {x} IN c}) <=>
          ~(u IN w <=> v IN w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN w /\ x IN segment[u,v] /\ {x} IN c} = {x | x IN {u:real^N,v} /\ x IN w}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `segment[u:real^N,v]`; `x:real^N`]
        MOI_FN1_VERTEX_EXTREME) THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
      STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MAP_EVERY ASM_CASES_TAC [`(u:real^N) IN w`; `(v:real^N) IN w`] THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {u,v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {u}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {v}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC];
    SUBGOAL_THEN `{x | x IN {u:real^N,v} /\ x IN w} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC]] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; CARD_SING] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_S3ZB_PCHAIN_JOIN_ANY = prove
 (`!c z (p:real^1->real^N) q m w1 n w2.
     moi_s3zb_pchain c p m w1 /\ moi_s3zb_pchain c q n w2 /\
     pathfinish p = pathstart q /\ w1 m = w2 0
     ==> ?M x. moi_s3zb_pchain c (p ++ q) M x /\ x 0 = w1 0 /\ x M = w2 n /\
               (moi_s3zb_par z x M <=> ~(moi_s3zb_par z w1 m <=> moi_s3zb_par z w2 n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_pchain]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0) /\ ~(n = 0)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s3zb_pchain c p (m * n) (\i. (w1:num->real^N) (i DIV n)) /\
    moi_s3zb_pchain c q (m * n) (\i. (w2:num->real^N) (i DIV m))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3ZB_PCHAIN_REFINE THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC MOI_S3ZB_PCHAIN_REFINE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m * n) DIV n = m /\ (m * n) DIV m = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ONCE_REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `q:real^1->real^N`;
                 `m * n:num`; `\i. (w1:num->real^N) (i DIV n)`;
                 `\i. (w2:num->real^N) (i DIV m)`] MOI_S3ZB_PCHAIN_JOIN) THEN
  ASM_REWRITE_TAC[DIV_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(moi_s3zb_par z (\i. (w1:num->real^N) (i DIV n)) (m * n) <=> moi_s3zb_par z w1 m) /\
    (moi_s3zb_par z (\i. (w2:num->real^N) (i DIV m)) (m * n) <=> moi_s3zb_par z w2 n)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `w1:num->real^N`; `n:num`]
        MOI_S3ZB_PAR_REFINE) THEN ASM_SIMP_TAC[];
      SUBST1_TAC(SPECL [`m:num`; `n:num`] MULT_SYM) THEN
      MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `w2:num->real^N`; `m:num`]
        MOI_S3ZB_PAR_REFINE) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m * n + m * n <= m * n:num)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(x:num) + x <= x <=> x = 0`; MULT_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`m * n + m * n:num`;
    `\i. if i <= m * n then (w1:num->real^N) (i DIV n) else w2 ((i - m * n) DIV m)`] THEN
  ASM_REWRITE_TAC[LE_0; DIV_0; ADD_SUB] THEN
  MP_TAC(ISPECL [`z:(real^N->bool)->bool`; `m * n:num`; `\i. (w1:num->real^N) (i DIV n)`;
                 `\i. (w2:num->real^N) (i DIV m)`] MOI_S3ZB_PAR_JOIN) THEN
  ASM_REWRITE_TAC[DIV_0]);;

let MOI_S3ZB_BASE_VERTEX = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c /\ ~(UNIONS c = {}) ==> ?v. {v} IN c`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]]);;

let MOI_S3ZB_EDGE_LOOP = prove
 (`!c (y:(real^N->bool)->bool) v0 gu mu wu gv mv wv u v.
     lf_simplicial_complex c /\ z2_cocycle c y /\
     {u} IN c /\ {v} IN c /\ ~(u = v) /\ segment[u,v] IN c /\
     path gu /\ path_image gu SUBSET UNIONS c /\ pathstart gu = v0 /\ pathfinish gu = u /\
     path gv /\ path_image gv SUBSET UNIONS c /\ pathstart gv = v0 /\ pathfinish gv = v /\
     moi_s3zb_pchain c gu mu wu /\ moi_s3zb_pchain c gv mv wv /\
     wu 0 = v0 /\ wu mu = u /\ wv 0 = v0 /\ wv mv = v
     ==> path (gu ++ linepath(u,v) ++ reversepath gv) /\
         path_image (gu ++ linepath(u,v) ++ reversepath gv) SUBSET UNIONS c /\
         pathfinish (gu ++ linepath(u,v) ++ reversepath gv) =
         pathstart (gu ++ linepath(u,v) ++ reversepath gv) /\
         (moi_s3zb_lpar c y (gu ++ linepath(u,v) ++ reversepath gv) <=>
          ~(moi_s3zb_par y wu mu <=>
            ~(segment[u,v] IN y <=> moi_s3zb_par y wv mv)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image(linepath(u:real^N,v)) SUBSET UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; PATH_REVERSEPATH;
               PATH_IMAGE_REVERSEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; UNION_SUBSET] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`; `v:real^N`]
    MOI_S3ZB_PCHAIN_LINEPATH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `gv:real^1->real^N`; `mv:num`; `wv:num->real^N`]
    MOI_S3ZB_PCHAIN_REV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`;
                 `linepath(u:real^N,v)`; `reversepath(gv:real^1->real^N)`; `3`;
                 `\k. if k <= 1 then u else (v:real^N)`; `mv:num`;
                 `\k. (wv:num->real^N)(mv - k)`] MOI_S3ZB_PCHAIN_JOIN_ANY) THEN
  ASM_REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_REVERSEPATH; SUB_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:num` (X_CHOOSE_THEN `x1:num->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`;
                 `gu:real^1->real^N`; `linepath(u:real^N,v) ++ reversepath gv`; `mu:num`;
                 `wu:num->real^N`; `M1:num`; `x1:num->real^N`]
    MOI_S3ZB_PCHAIN_JOIN_ANY) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:num` (X_CHOOSE_THEN `x2:num->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`;
                 `gu ++ linepath(u:real^N,v) ++ reversepath gv`; `M2:num`; `x2:num->real^N`]
    MOI_S3ZB_LPAR_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                 PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
    MATCH_MP_TAC MOI_S3ZB_PCHAIN_ICHAIN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUB_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_S3ZB_PAR_LINEPATH; MOI_S3ZB_PAR_REV] THEN
  ASM_REWRITE_TAC[moi_s3zb_ez]);;

let MOI_S3ZB_INJ = prove
 (`!c (y:(real^N->bool)->bool).
     FINITE c /\ lf_simplicial_complex c /\ connected(UNIONS c) /\ ~(UNIONS c = {}) /\
     z2_cocycle c y /\
     (!p. path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p
          ==> ~moi_s3zb_lpar c y p)
     ==> z2_coboundary c y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZB_BASE_VERTEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^N`) THEN
  SUBGOAL_THEN `path_connected(UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3Z2_COMPLEX_PC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. ?g m w. {v} IN c
       ==> path g /\ path_image g SUBSET UNIONS c /\ pathstart g = v0 /\ pathfinish g = v /\
           moi_s3zb_pchain c g m w /\ w 0 = v0 /\ w m = v`
  MP_TAC THENL
   [X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `{v:real^N} IN c` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_connected(UNIONS c:real^N->bool)` THEN
    REWRITE_TAC[path_connected] THEN
    DISCH_THEN(MP_TAC o SPECL [`v0:real^N`; `v:real^N`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^1->real^N`] MOI_S3ZB_PCHAIN_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `w:num->real^N`)) THEN
    MAP_EVERY EXISTS_TAC [`g:real^1->real^N`; `m:num`; `w:num->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^1->real^N`; `m:num`; `w:num->real^N`]
      MOI_S3ZB_PCHAIN_VERTEX_ENDS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^1->real^N` (X_CHOOSE_THEN `MM:real^N->num`
    (X_CHOOSE_TAC `WW:real^N->num->real^N`))) THEN
  REWRITE_TAC[z2_coboundary] THEN
  EXISTS_TAC `{v:real^N | {v} IN c /\ moi_s3zb_par (y:(real^N->bool)->bool) ((WW:real^N->num->real^N) v) ((MM:real^N->num) v)}` THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S3ZB_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `{v:real^N | {v} IN c /\ moi_s3zb_par (y:(real^N->bool)->bool) ((WW:real^N->num->real^N) v) ((MM:real^N->num) v)}`;
                 `u:real^N`; `v:real^N`] MOI_S3ZB_EDGE_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `{u:real^N} IN c`) o SPEC `u:real^N` o
    check (fun th -> can (find_term ((=) `G:real^N->real^1->real^N`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MP (ASSUME `{v:real^N} IN c`) o SPEC `v:real^N` o
    check (fun th -> can (find_term ((=) `G:real^N->real^1->real^N`)) (concl th) &&
                     is_forall(concl th))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`; `v0:real^N`;
                 `(G:real^N->real^1->real^N) u`; `(MM:real^N->num) u`;
                 `(WW:real^N->num->real^N) u`;
                 `(G:real^N->real^1->real^N) v`; `(MM:real^N->num) v`;
                 `(WW:real^N->num->real^N) v`; `u:real^N`; `v:real^N`]
    MOI_S3ZB_EDGE_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(G:real^N->real^1->real^N) u ++ linepath(u,v) ++ reversepath (G v)` o check (fun th ->
      can (find_term ((=) `moi_s3zb_lpar:((real^N->bool)->bool)->
                              ((real^N->bool)->bool)->(real^1->real^N)->bool`)) (concl th) &&
      is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Part 6: path values of a character phi (closing a path by fixed paths    *)
(* gam x from a base point): invariance, additivity, reversal, loops.       *)
(* ========================================================================= *)

let moi_s3zb_gam = new_definition
 `moi_s3zb_gam (s:real^N->bool) (v0:real^N) (gam:real^N->real^1->real^N) <=>
    !x. x IN s ==> path(gam x) /\ path_image(gam x) SUBSET s /\
                   pathstart(gam x) = v0 /\ pathfinish(gam x) = x`;;

let moi_s3zb_pv = new_definition
 `moi_s3zb_pv (phi:(real^1->real^N)->bool) (gam:real^N->real^1->real^N) p <=>
    phi(gam(pathstart p) ++ p ++ reversepath(gam(pathfinish p)))`;;

let MOI_S3ZB_GAM_LOOP = prove
 (`!(s:real^N->bool) v0 gam p.
     moi_s3zb_gam s v0 gam /\ path p /\ path_image p SUBSET s
     ==> path(gam(pathstart p) ++ p ++ reversepath(gam(pathfinish p))) /\
         path_image(gam(pathstart p) ++ p ++ reversepath(gam(pathfinish p))) SUBSET s /\
         pathstart(gam(pathstart p) ++ p ++ reversepath(gam(pathfinish p))) = v0 /\
         pathfinish(gam(pathstart p) ++ p ++ reversepath(gam(pathfinish p))) = v0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_gam] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN s /\ pathfinish p IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; UNION_SUBSET]);;

let MOI_S3ZB_PV_LOOP = prove
 (`!(s:real^N->bool) phi v0 gam p.
     moi_s33_char s phi /\ moi_s3zb_gam s v0 gam /\
     path p /\ path_image p SUBSET s /\ pathfinish p = pathstart p
     ==> (moi_s3zb_pv phi gam p <=> phi p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3zb_pv] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s3zb_gam s (v0:real^N) gam` THEN REWRITE_TAC[moi_s3zb_gam] THEN
  DISCH_THEN(MP_TAC o SPEC `pathstart(p:real^1->real^N)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; SIMP_TAC[]]);;

let MOI_S3ZB_PV_HOM = prove
 (`!(s:real^N->bool) phi v0 gam p q.
     moi_s33_char s phi /\ moi_s3zb_gam s v0 gam /\
     path p /\ path_image p SUBSET s /\ homotopic_paths s p q
     ==> (moi_s3zb_pv phi gam p <=> moi_s3zb_pv phi gam q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3zb_pv] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHSTART) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP HOMOTOPIC_PATHS_IMP_PATHFINISH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN s /\ pathfinish p IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `path((gam:real^N->real^1->real^N) (pathstart p)) /\
    path_image(gam(pathstart p)) SUBSET s /\
    pathstart(gam(pathstart p)) = v0 /\ pathfinish(gam(pathstart p)) = pathstart p /\
    path(gam(pathfinish p)) /\ path_image(gam(pathfinish p)) SUBSET s /\
    pathstart(gam(pathfinish p)) = v0 /\ pathfinish(gam(pathfinish p)) = pathfinish p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s3zb_gam]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
  ASM_SIMP_TAC[HOMOTOPIC_PATHS_REFL; PATHSTART_JOIN] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN
  ASM_SIMP_TAC[HOMOTOPIC_PATHS_REFL; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_REVERSEPATH]);;

let MOI_S3ZB_PATH_TAC =
  ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_REVERSEPATH; PATH_IMAGE_REVERSEPATH;
               PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; UNION_SUBSET; PATH_LINEPATH; PATH_IMAGE_LINEPATH;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH; SEGMENT_REFL; SING_SUBSET;
               HOMOTOPIC_PATHS_REFL];;

let MOI_S3ZB_CANCEL = prove
 (`!(s:real^N->bool) A p B q D.
     path A /\ path_image A SUBSET s /\ path p /\ path_image p SUBSET s /\
     path B /\ path_image B SUBSET s /\ path q /\ path_image q SUBSET s /\
     path D /\ path_image D SUBSET s /\
     pathfinish A = pathstart p /\ pathfinish p = pathfinish B /\
     pathfinish B = pathstart q /\ pathfinish q = pathfinish D /\
     pathstart A = pathstart B /\ pathstart B = pathstart D
     ==> homotopic_paths s ((A ++ p ++ reversepath B) ++ (B ++ q ++ reversepath D))
                           (A ++ (p ++ q) ++ reversepath D)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `A ++ ((p ++ reversepath B) ++ (B ++ q ++ reversepath D)):real^1->real^N` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    MOI_S3ZB_PATH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_S3ZB_PATH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (reversepath B ++ (B ++ q ++ reversepath D)):real^1->real^N` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
    MOI_S3ZB_PATH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
  EXISTS_TAC `p ++ (q ++ reversepath D):real^1->real^N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN MOI_S3ZB_PATH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `(reversepath B ++ B) ++ (q ++ reversepath D):real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_S3ZB_PATH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_TRANS THEN
    EXISTS_TAC `linepath(pathfinish B,pathfinish B) ++ (q ++ reversepath D):real^1->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_PATHS_JOIN THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_PATHS_LINV THEN ASM_REWRITE_TAC[];
        MOI_S3ZB_PATH_TAC;
        MOI_S3ZB_PATH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `q ++ reversepath D:real^1->real^N`]
      HOMOTOPIC_PATHS_LID) THEN
    MOI_S3ZB_PATH_TAC;
    MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_S3ZB_PATH_TAC]);;

let MOI_S3ZB_PV_JOIN = prove
 (`!(s:real^N->bool) phi v0 gam p q.
     moi_s33_char s phi /\ moi_s3zb_gam s v0 gam /\
     path p /\ path_image p SUBSET s /\ path q /\ path_image q SUBSET s /\
     pathfinish p = pathstart q
     ==> (moi_s3zb_pv phi gam (p ++ q) <=>
          ~(moi_s3zb_pv phi gam p <=> moi_s3zb_pv phi gam q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s3zb_pv; PATHSTART_JOIN] THEN ASM_SIMP_TAC[PATHFINISH_JOIN] THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN s /\ pathstart q IN s /\ pathfinish q IN s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> path((gam:real^N->real^1->real^N) x) /\ path_image(gam x) SUBSET s /\
                   pathstart(gam x) = v0 /\ pathfinish(gam x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s3zb_gam]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`(gam:real^N->real^1->real^N) (pathstart p) ++ p ++ reversepath(gam(pathstart q))`;
    `(gam:real^N->real^1->real^N) (pathstart q) ++ q ++ reversepath(gam(pathfinish q))`] o
    CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN MOI_S3ZB_PATH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  ASM_SIMP_TAC[] THEN MOI_S3ZB_PATH_TAC THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_PATHS_SYM] THEN MATCH_MP_TAC MOI_S3ZB_CANCEL THEN
  ASM_SIMP_TAC[]);;

let MOI_S3ZB_PV_REV = prove
 (`!(s:real^N->bool) phi v0 gam p.
     moi_s33_char s phi /\ moi_s3zb_gam s v0 gam /\ path p /\ path_image p SUBSET s
     ==> (moi_s3zb_pv phi gam (reversepath p) <=> moi_s3zb_pv phi gam p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s3zb_pv; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN s /\ pathfinish p IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> path((gam:real^N->real^1->real^N) x) /\ path_image(gam x) SUBSET s /\
                   pathstart(gam x) = v0 /\ pathfinish(gam x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_s3zb_gam]; ALL_TAC] THEN
  ABBREV_TAC `A = (gam:real^N->real^1->real^N) (pathstart p)` THEN
  ABBREV_TAC `B = (gam:real^N->real^1->real^N) (pathfinish p)` THEN
  SUBGOAL_THEN `path (A:real^1->real^N) /\ path_image A SUBSET s /\ pathstart A = v0 /\
                pathfinish A = pathstart p /\ path (B:real^1->real^N) /\
                path_image B SUBSET s /\ pathstart B = v0 /\ pathfinish B = pathfinish p`
  STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`;
                 `A ++ p ++ reversepath B:real^1->real^N`] MOI_S3Z2_CHAR_REV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MOI_S3ZB_PATH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN MOI_S3ZB_PATH_TAC THEN
  ASM_SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_REVERSEPATH;
               PATHFINISH_REVERSEPATH; REVERSEPATH_REVERSEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN MOI_S3ZB_PATH_TAC);;

let MOI_S3ZB_PV_CONST = prove
 (`!(s:real^N->bool) phi v0 gam a.
     moi_s33_char s phi /\ moi_s3zb_gam s v0 gam /\ a IN s
     ==> ~moi_s3zb_pv phi gam (linepath(a,a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s3zb_pv phi gam (linepath(a:real^N,a)) <=> phi(linepath(a,a))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_PV_LOOP THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `v0:real^N`] THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET;
                    PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    MP_TAC(ISPECL [`s:real^N->bool`; `phi:(real^1->real^N)->bool`; `a:real^N`]
      MOI_S3Z2_CHAR_CONST) THEN ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_GRID_PTS = prove
 (`!m k. k < m
         ==> lift(&k / &m) IN interval[vec 0,vec 1] /\
             lift(&(SUC k) / &m) IN interval[vec 0,vec 1] /\
             drop(lift(&k / &m)) <= drop(lift(&(SUC k) / &m)) /\
             (!t. t IN interval[lift(&k / &m),lift(&(SUC k) / &m)]
                  ==> &k <= &m * drop t /\ &m * drop t <= &(SUC k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LID;
               REAL_OF_NUM_LE; REAL_LE_DIV2_EQ] THEN
  REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3ZB_PV_PIECE = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam p m w k.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam /\
     path p /\ path_image p SUBSET UNIONS c /\ moi_s3zb_pchain c p m w /\ k < m
     ==> (moi_s3zb_pv phi gam (subpath (lift(&k / &m)) (lift(&(SUC k) / &m)) p) <=>
          ~(moi_s3zb_pv phi gam (linepath(w k,p(lift(&k / &m)))) <=>
            ~(moi_s3zb_pv phi gam (linepath(w(SUC k),p(lift(&(SUC k) / &m)))) <=>
              moi_s3zb_pv phi gam (linepath(w k,w(SUC k))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `k:num`] MOI_S3ZB_GRID_PTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = lift(&k / &m)` THEN ABBREV_TAC `b = lift(&(SUC k) / &m)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `u = (w:num->real^N) k` THEN ABBREV_TAC `u' = (w:num->real^N) (SUC k)` THEN
  SUBGOAL_THEN
   `!t. t IN interval[a,b]
        ==> (p:real^1->real^N) t IN moi_sta_open_star c u /\
            p t IN moi_sta_open_star c u'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_s3zb_pchain c (p:real^1->real^N) m w` THEN
    REWRITE_TAC[moi_s3zb_pchain] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `t:real^1`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (?t. t IN interval[a,b] /\ x = (p:real^1->real^N) t) \/
        x IN segment[u,p a] \/ x IN segment[p b,u']
        ==> ?r. r IN c /\ x IN r /\ u IN r /\ u' IN r`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    SUBGOAL_THEN
     `!t. t IN interval[a,b]
          ==> ?r. r IN c /\ (p:real^1->real^N) t IN r /\ u IN r /\ u' IN r`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(p:real^1->real^N) t`]
        MOI_S3ZB_STAR_COMMON) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^1) IN interval[a,b] /\ (b:real^1) IN interval[a,b]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^1`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[u:real^N,(p:real^1->real^N) a] SUBSET r` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `b:real^1`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[(p:real^1->real^N) b,u'] SUBSET r` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. ((?t. t IN interval[a,b] /\ x = (p:real^1->real^N) t) \/
           x IN segment[u,p a] \/ x IN segment[p b,u']) /\ y IN segment[u,u']
          ==> segment[x,y] SUBSET UNIONS c`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th o SPEC `x:real^N`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `convex(r:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `u:real^N`; `u':real^N`] SEGMENT_SUBSET_CONVEX) THEN
      ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^N,(p:real^1->real^N) a] SUBSET UNIONS c /\
                segment[p b,u'] SUBSET UNIONS c /\
                path(subpath a b (p:real^1->real^N)) /\
                path_image(subpath a b p) SUBSET UNIONS c`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `u:real^N`] o check (fun th ->
        can (find_term ((=) `segment:(real^N#real^N)list->real^N->bool`)) (concl th) &&
        is_forall(concl th) &&
        can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `u':real^N`] o check (fun th ->
        can (find_term ((=) `segment:(real^N#real^N)list->real^N->bool`)) (concl th) &&
        is_forall(concl th) &&
        can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
      MATCH_MP_TAC PATH_SUBPATH THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[PATH_IMAGE_SUBPATH] THEN
      UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET UNIONS c` THEN
      REWRITE_TAC[path_image] THEN
      MATCH_MP_TAC(SET_RULE `(t:real^1->bool) SUBSET s ==> IMAGE (f:real^1->real^N) s SUBSET u ==> IMAGE f t SUBSET u`) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN UNDISCH_TAC `a IN interval[vec 0:real^1,vec 1]` THEN
      UNDISCH_TAC `b IN interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `J = linepath(u,(p:real^1->real^N) a) ++ subpath a b p ++ linepath(p b,u')` THEN
  SUBGOAL_THEN
   `path (J:real^1->real^N) /\ pathstart J = u /\ pathfinish J = u' /\
    path_image J = segment[u:real^N,p a] UNION IMAGE (p:real^1->real^N) (interval[a,b]) UNION
                   segment[p b,u']`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_JOIN;
                 PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                 PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATH_IMAGE_LINEPATH;
                 PATH_IMAGE_SUBPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (J:real^1->real^N) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN
    UNDISCH_TAC `path_image(subpath a b (p:real^1->real^N)) SUBSET UNIONS c` THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_paths (UNIONS c) J (linepath(u:real^N,u'))` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    X_GEN_TAC `t:real^1` THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `segment:(real^N#real^N)list->real^N->bool`)) (concl th) &&
      is_forall(concl th) &&
      can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(J:real^1->real^N) t IN path_image J` MP_TAC THENL
       [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN MESON_TAC[];
      REWRITE_TAC[linepath; IN_SEGMENT] THEN EXISTS_TAC `drop t` THEN
      UNDISCH_TAC `t IN interval[vec 0:real^1,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `J:real^1->real^N`;
                 `linepath(u:real^N,u')`] MOI_S3ZB_PV_HOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "J" THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `linepath(u:real^N,(p:real^1->real^N) a)`;
                 `subpath a b (p:real^1->real^N) ++ linepath(p b,u')`] MOI_S3ZB_PV_JOIN) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `subpath a b (p:real^1->real^N)`;
                 `linepath((p:real^1->real^N) b,u')`] MOI_S3ZB_PV_JOIN) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `linepath(u':real^N,(p:real^1->real^N) b)`] MOI_S3ZB_PV_REV) THEN
  REWRITE_TAC[REVERSEPATH_LINEPATH] THEN
  ASM_SIMP_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATH_JOIN; PATH_IMAGE_JOIN;
               PATHSTART_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH; PATHSTART_SUBPATH;
               PATHFINISH_SUBPATH; UNION_SUBSET] THEN
  ANTS_TAC THENL [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC TAUT);;

let MOI_S3ZB_SUBPATH_REFL = prove
 (`!(p:real^1->real^N) a. subpath a a p = linepath(p a,p a)`,
  REWRITE_TAC[subpath; linepath; FUN_EQ_THM; VECTOR_SUB_REFL; DROP_VEC;
              VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  VECTOR_ARITH_TAC);;

let MOI_S3ZB_PV_SUBDIV = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam p m w y.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam /\
     path p /\ path_image p SUBSET UNIONS c /\ moi_s3zb_pchain c p m w /\
     (!k. k < m
          ==> (moi_s3zb_ez y (w k) (w (SUC k)) <=>
               moi_s3zb_pv phi gam (linepath(w k,w(SUC k)))))
     ==> !j. j <= m
             ==> (moi_s3zb_pv phi gam (subpath (vec 0) (lift(&j / &m)) p) <=>
                  ~(moi_s3zb_pv phi gam (linepath(w 0,p(lift(&0 / &m)))) <=>
                    ~(moi_s3zb_pv phi gam (linepath(w j,p(lift(&j / &m)))) <=>
                      moi_s3zb_par y w j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_s3zb_pchain]) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= m ==> lift(&j / &m) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `~(m = 0) ==> 0 < m`; REAL_MUL_LID; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM; MOI_S3ZB_SUBPATH_REFL] THEN
    REWRITE_TAC[moi_s3zb_par] THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                   `gam:real^N->real^1->real^N`; `(p:real^1->real^N)(vec 0)`]
      MOI_S3ZB_PV_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; pathstart; SUBSET];
      CONV_TAC TAUT];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [(UNDISCH_TAC `SUC j <= m` THEN ARITH_TAC); DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `p:real^1->real^N`; `m:num`;
                 `w:num->real^N`; `j:num`] MOI_S3ZB_PV_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [(UNDISCH_TAC `SUC j <= m` THEN ARITH_TAC); DISCH_TAC] THEN
  SUBGOAL_THEN
   `lift(&j / &m) IN interval[vec 0,vec 1] /\
    lift(&(SUC j) / &m) IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN (UNDISCH_TAC `SUC j <= m` THEN ARITH_TAC); ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`;
                 `subpath (vec 0) (lift(&j / &m)) (p:real^1->real^N) ++
                  subpath (lift(&j / &m)) (lift(&(SUC j) / &m)) p`;
                 `subpath (vec 0) (lift(&(SUC j) / &m)) (p:real^1->real^N)`]
    MOI_S3ZB_PV_HOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_SUBPATH; PATHSTART_SUBPATH; PATHFINISH_SUBPATH;
                 PATH_IMAGE_JOIN; UNION_SUBSET; HOMOTOPIC_JOIN_SUBPATHS] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image(p:real^1->real^N)` THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`;
                 `subpath (vec 0) (lift(&j / &m)) (p:real^1->real^N)`;
                 `subpath (lift(&j / &m)) (lift(&(SUC j) / &m)) (p:real^1->real^N)`]
    MOI_S3ZB_PV_JOIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_SUBPATH] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image(p:real^1->real^N)` THEN
    ASM_SIMP_TAC[PATH_IMAGE_SUBPATH_SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[moi_s3zb_par] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `moi_s3zb_ez:((real^N->bool)->bool)->real^N->real^N->bool`))
        (concl th))) THEN
  ANTS_TAC THENL [(UNDISCH_TAC `SUC j <= m` THEN ARITH_TAC); DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC TAUT);;

(* ========================================================================= *)
(* Part 7: every character is the loop parity of a cocycle (the cocycle of  *)
(* the path values of the edges; even on triangles by the null-homotopic    *)
(* triangle loop; equal on loops at the base vertex by subdivision).        *)
(* ========================================================================= *)

let MOI_S3ZB_TRI_VERTS = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ t IN c /\ aff_dim t = &2
     ==> ?a b d. ~(a = b) /\ ~(a = d) /\ ~(b = d) /\
                 {a} IN c /\ {b} IN c /\ {d} IN c /\
                 ~affine_dependent {a,b,d} /\ t = convex hull {a,b,d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[simplex; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:int`; `V:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    SUBGOAL_THEN `aff_dim(V:real^N->bool) = &(CARD V) - &1` MP_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(V:real^N->bool) = &2` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^N. x IN {a,b,d} ==> {x} IN c`
    (fun th -> MESON_TAC[th; IN_INSERT]) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x:real^N} face_of t` MP_TAC THENL
   [REWRITE_TAC[FACE_OF_SING] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ASM_MESON_TAC[lf_simplicial_complex]]);;

let MOI_S3ZB_TRI_EDGES = prove
 (`!c z (a:real^N) b d.
     lf_simplicial_complex c /\ (!e. e IN z ==> e IN c /\ aff_dim e = &1) /\
     convex hull {a,b,d} IN c /\ ~affine_dependent {a,b,d}
     ==> {e | e IN z /\ e SUBSET convex hull {a,b,d}} =
         {e | e IN {segment[a,b], segment[b,d], segment[d,a]} /\ e IN z}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) face_of convex hull {a,b,d}` MP_TAC THENL
     [SUBGOAL_THEN `e INTER convex hull {a:real^N,b,d} = e` (SUBST1_TAC o SYM) THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~affine_dependent(S:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(S:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
      ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC[INT_ARITH `x - &1:int = &1 <=> x = &2`; INT_OF_NUM_EQ];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(S:real^N->bool) SUBSET {a,b,d}` THEN
    UNDISCH_TAC `e = convex hull (S:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_EQ] THEN
    UNDISCH_TAC `{x:real^N,y} SUBSET {a,b,d}` THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~(x:real^N = y)` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

let moi_s3zb_ycoc = new_definition
 `moi_s3zb_ycoc (c:(real^N->bool)->bool) (phi:(real^1->real^N)->bool) gam =
    {e | e IN c /\ aff_dim e = &1 /\
         ?a b. ~(a = b) /\ {a} IN c /\ {b} IN c /\ e = segment[a,b] /\
               moi_s3zb_pv phi gam (linepath(a,b))}`;;

let MOI_S3ZB_SURJ_EZ = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam u v.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam /\
     {u} IN c /\ {v} IN c /\ (u = v \/ segment[u,v] IN c)
     ==> (moi_s3zb_ez (moi_s3zb_ycoc c phi gam) u v <=>
          moi_s3zb_pv phi gam (linepath(u,v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS c /\ v IN UNIONS c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[MOI_S3ZB_EZ_REFL] THEN
    ASM_MESON_TAC[MOI_S3ZB_PV_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^N,v] IN c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s3zb_ez; moi_s3zb_ycoc; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `segment[u:real^N,v] = segment[a,b]` THEN
    REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N = u /\ b = v) \/ (a = v /\ b = u)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `a:real^N`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `b:real^N`)) THEN
    UNDISCH_TAC `moi_s3zb_pv phi gam (linepath(v:real^N,u))` THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                   `gam:real^N->real^1->real^N`; `linepath(u:real^N,v)`] MOI_S3ZB_PV_REV) THEN
    REWRITE_TAC[REVERSEPATH_LINEPATH] THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; MESON_TAC[]];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_SURJ_EDGE = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam t a b.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam /\ t IN c /\
     {a} IN c /\ {b} IN c /\ a IN t /\ b IN t /\ ~(a = b)
     ==> segment[a,b] IN c /\
         (segment[a,b] IN moi_s3zb_ycoc c phi gam <=>
          moi_s3zb_pv phi gam (linepath(a,b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `a:real^N`; `b:real^N`]
    MOI_S3ZB_ADJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `a:real^N`; `b:real^N`] MOI_S3ZB_SURJ_EZ) THEN
  ASM_REWRITE_TAC[moi_s3zb_ez]);;

let MOI_S3ZB_SURJ_COCYCLE = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam
     ==> z2_cocycle c (moi_s3zb_ycoc c phi gam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[z2_cocycle] THEN CONJ_TAC THENL
   [SIMP_TAC[moi_s3zb_ycoc; IN_ELIM_THM]; ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S3ZB_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam`;
                 `a:real^N`; `b:real^N`; `d:real^N`] MOI_S3ZB_TRI_EDGES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[moi_s3zb_ycoc; IN_ELIM_THM]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`segment[a:real^N,b]`; `segment[b:real^N,d]`;
                            `segment[d:real^N,a]`;
                            `\e:real^N->bool. e IN moi_s3zb_ycoc c phi gam`]
    MOI_S3ZB_CARD3)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN convex hull {a,b,d} /\ b IN convex hull {a,b,d} /\
                d IN convex hull {a,b,d}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(segment[a:real^N,b] IN moi_s3zb_ycoc c phi gam <=> moi_s3zb_pv phi gam (linepath(a,b))) /\
    (segment[b:real^N,d] IN moi_s3zb_ycoc c phi gam <=> moi_s3zb_pv phi gam (linepath(b,d))) /\
    (segment[d:real^N,a] IN moi_s3zb_ycoc c phi gam <=> moi_s3zb_pv phi gam (linepath(d,a)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                     `gam:real^N->real^1->real^N`; `convex hull {a:real^N,b,d}`;
                     `a:real^N`; `b:real^N`] MOI_S3ZB_SURJ_EDGE);
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                     `gam:real^N->real^1->real^N`; `convex hull {a:real^N,b,d}`;
                     `b:real^N`; `d:real^N`] MOI_S3ZB_SURJ_EDGE);
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                     `gam:real^N->real^1->real^N`; `convex hull {a:real^N,b,d}`;
                     `d:real^N`; `a:real^N`] MOI_S3ZB_SURJ_EDGE)] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image(linepath(a:real^N,b)) SUBSET convex hull {a,b,d} /\
    path_image(linepath(b:real^N,d)) SUBSET convex hull {a,b,d} /\
    path_image(linepath(d:real^N,a)) SUBSET convex hull {a,b,d}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^N,b,d} SUBSET UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image(linepath(a:real^N,b)) SUBSET UNIONS c /\
                path_image(linepath(b:real^N,d)) SUBSET UNIONS c /\
                path_image(linepath(d:real^N,a)) SUBSET UNIONS c` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = linepath(a:real^N,b) ++ linepath(b,d) ++ linepath(d,a)` THEN
  SUBGOAL_THEN `path (L:real^1->real^N) /\ path_image L SUBSET convex hull {a,b,d} /\
                pathstart L = a /\ pathfinish L = a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; UNION_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3zb_pv phi gam (L:real^1->real^N) <=>
                ~(moi_s3zb_pv phi gam (linepath(a:real^N,b)) <=>
                  ~(moi_s3zb_pv phi gam (linepath(b,d)) <=>
                    moi_s3zb_pv phi gam (linepath(d,a))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                   `gam:real^N->real^1->real^N`; `linepath(b:real^N,d)`;
                   `linepath(d:real^N,a)`] MOI_S3ZB_PV_JOIN) THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                   `gam:real^N->real^1->real^N`; `linepath(a:real^N,b)`;
                   `linepath(b:real^N,d) ++ linepath(d,a)`] MOI_S3ZB_PV_JOIN) THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH; UNION_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(phi:(real^1->real^N)->bool) L` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3Z2_CHAR_NULL THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `convex hull {a:real^N,b,d}` CONVEX_IMP_SIMPLY_CONNECTED) THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `L:real^1->real^N`] MOI_S3ZB_PV_LOOP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MOI_S3ZB_PCHAIN_ADJ = prove
 (`!c (p:real^1->real^N) m w k.
     lf_simplicial_complex c /\ moi_s3zb_pchain c p m w /\ k < m
     ==> {w k} IN c /\ {w (SUC k)} IN c /\
         (w k = w (SUC k) \/ segment[w k,w (SUC k)] IN c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_pchain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{(w:num->real^N) k} IN c /\ {w (SUC k)} IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `k < m:num` THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `lift(&k / &m)`]) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `&m * &k / &m = &k` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_OF_NUM_LE] THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(p:real^1->real^N)(lift(&k / &m))`]
    MOI_S3ZB_STAR_COMMON) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s0:real^N->bool`; `(w:num->real^N) k`;
                 `(w:num->real^N) (SUC k)`] MOI_S3ZB_ADJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

let MOI_S3ZB_SURJ_LOOPV = prove
 (`!c (phi:(real^1->real^N)->bool) v0 gam p.
     lf_simplicial_complex c /\ moi_s33_char (UNIONS c) phi /\
     moi_s3zb_gam (UNIONS c) v0 gam /\
     path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p /\
     {pathstart p} IN c
     ==> (phi p <=> moi_s3zb_lpar c (moi_s3zb_ycoc c phi gam) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_PCHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `w:num->real^N`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`; `w:num->real^N`]
    MOI_S3ZB_PCHAIN_VERTEX_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_MESON_TAC[moi_s3zb_pchain]; ALL_TAC] THEN
  SUBGOAL_THEN `z2_cocycle c (moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam)`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_SURJ_COCYCLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam`;
                 `p:real^1->real^N`; `m:num`; `w:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3ZB_PCHAIN_ICHAIN THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!k. k < m
        ==> (moi_s3zb_ez (moi_s3zb_ycoc c phi gam) ((w:num->real^N) k) (w (SUC k)) <=>
             moi_s3zb_pv phi gam (linepath(w k,w(SUC k))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3ZB_SURJ_EZ THEN
    EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3ZB_PCHAIN_ADJ THEN
    MAP_EVERY EXISTS_TAC [`p:real^1->real^N`; `m:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `p:real^1->real^N`; `m:num`; `w:num->real^N`;
                 `moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam`] MOI_S3ZB_PV_SUBDIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LE_REFL] THEN
  SUBGOAL_THEN `&m / &m = &1 /\ &0 / &m = &0` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_NUM; SUBPATH_TRIVIAL] THEN
  SUBGOAL_THEN `(p:real^1->real^N)(vec 0) = pathstart p /\ p(vec 1) = pathfinish p`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `pathstart(p:real^1->real^N)`]
    MOI_S3ZB_PV_CONST) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `phi:(real^1->real^N)->bool`; `v0:real^N`;
                 `gam:real^N->real^1->real^N`; `p:real^1->real^N`] MOI_S3ZB_PV_LOOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

let MOI_S3ZB_SURJ = prove
 (`!c (phi:(real^1->real^N)->bool).
     FINITE c /\ lf_simplicial_complex c /\ connected(UNIONS c) /\ ~(UNIONS c = {}) /\
     moi_s33_char (UNIONS c) phi
     ==> ?y. z2_cocycle c y /\
             !p. path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p
                 ==> (phi p <=> moi_s3zb_lpar c y p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S3ZB_BASE_VERTEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^N`) THEN
  SUBGOAL_THEN `(v0:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `path_connected(UNIONS c:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_S3Z2_COMPLEX_PC]; ALL_TAC] THEN
  REWRITE_TAC[path_connected] THEN DISCH_THEN(MP_TAC o SPEC `v0:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `gam:real^N->real^1->real^N` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN `moi_s3zb_gam (UNIONS c) (v0:real^N) gam` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3zb_gam] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_SURJ_COCYCLE]; ALL_TAC] THEN
  X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathstart(p:real^1->real^N) IN UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `g = (gam:real^N->real^1->real^N) (pathstart p)` THEN
  SUBGOAL_THEN `path (g:real^1->real^N) /\ path_image g SUBSET UNIONS c /\
                pathstart g = v0 /\ pathfinish g = pathstart p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_MESON_TAC[moi_s3zb_gam]; ALL_TAC] THEN
  ABBREV_TAC `q = (g:real^1->real^N) ++ p ++ reversepath g` THEN
  SUBGOAL_THEN `path (q:real^1->real^N) /\ path_image q SUBSET UNIONS c /\
                pathstart q = v0 /\ pathfinish q = v0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_REVERSEPATH;
                 PATH_IMAGE_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 UNION_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops (UNIONS c) (q:real^1->real^N) p` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_CONJUGATE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:(real^1->real^N)->bool) q <=> phi p` (SUBST1_TAC o SYM) THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_s33_char]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `moi_s3zb_ycoc c (phi:(real^1->real^N)->bool) gam`;
                 `q:real^1->real^N`; `p:real^1->real^N`] MOI_S3ZB_LPAR_HOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_S3ZB_SURJ_COCYCLE]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC MOI_S3ZB_SURJ_LOOPV THEN EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 8: assembly.  The character of a cocycle z is the loop parity on     *)
(* the loops of UNIONS c; a cocycle class gives the character of any of its *)
(* members; the induced map from classes to characters is injective (INJ)   *)
(* with image all characters (SURJ).                                        *)
(* ========================================================================= *)

let moi_s3zb_fz = new_definition
 `moi_s3zb_fz (c:(real^N->bool)->bool) z (p:real^1->real^N) <=>
    path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p /\
    moi_s3zb_lpar c z p`;;

let MOI_S3ZB_ICHAIN_ADJ = prove
 (`!c (p:real^1->real^N) m v i.
     lf_simplicial_complex c /\ pathfinish p = pathstart p /\
     moi_s3zb_ichain c p m v /\ i < m
     ==> {v i} IN c /\ {v (SUC i)} IN c /\
         (v i = v (SUC i) \/ segment[v i,v (SUC i)] IN c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&m = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= m` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = (p:real^1->real^N)(lift(&(SUC i) / &m))` THEN
  SUBGOAL_THEN `{(v:num->real^N) i} IN c /\ x IN moi_sta_open_star c (v i)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "x" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_OF_NUM_LE; REAL_LE_REFL] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{(v:num->real^N) (SUC i)} IN c /\ x IN moi_sta_open_star c (v (SUC i))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `SUC i < m` THENL
     [FIRST_ASSUM(MP_TAC o SPEC `SUC i`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "x" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_LMUL; REAL_OF_NUM_LE; REAL_LE_REFL] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC i = m` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `i < m:num` THEN UNDISCH_TAC `~(SUC i < m)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^N = (p:real^1->real^N)(vec 0)` SUBST1_TAC THENL
     [EXPAND_TAC "x" THEN
      SUBGOAL_THEN `&m / &m = &1` SUBST1_TAC THENL [ASM_SIMP_TAC[REAL_DIV_REFL]; ALL_TAC] THEN
      REWRITE_TAC[LIFT_NUM] THEN
      UNDISCH_TAC `pathfinish (p:real^1->real^N) = pathstart p` THEN
      REWRITE_TAC[pathfinish; pathstart];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_LE_REFL; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_S3ZB_STAR_COMMON) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3ZB_STAR_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s0:real^N->bool`; `(v:num->real^N) i`;
                 `(v:num->real^N) (SUC i)`] MOI_S3ZB_ADJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

let MOI_S3ZB_LPAR_COB = prove
 (`!c y (p:real^1->real^N).
     lf_simplicial_complex c /\ z2_cocycle c y /\ z2_coboundary c y /\
     path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p
     ==> ~moi_s3zb_lpar c y p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_ICHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `v:num->real^N`)) THEN
  SUBGOAL_THEN `(v:num->real^N) m = v 0 /\ 0 < m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3zb_ichain c (p:real^1->real^N) m v` THEN
    REWRITE_TAC[moi_s3zb_ichain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `m:num`; `v:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `z2_coboundary c (y:(real^N->bool)->bool)` THEN
  REWRITE_TAC[z2_coboundary] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^N->bool`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:(real^N->bool)->bool`; `w:real^N->bool`;
                 `v:num->real^N`; `m:num`] MOI_S3ZB_PAR_COB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i < m:num` THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`;
                       `v:num->real^N`; `i:num`] MOI_S3ZB_ICHAIN_ADJ) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `i = m:num` SUBST1_TAC THENL
       [UNDISCH_TAC `i <= m:num` THEN UNDISCH_TAC `~(i < m:num)` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`;
                     `v:num->real^N`; `0`] MOI_S3ZB_ICHAIN_ADJ) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`; `m:num`;
                     `v:num->real^N`; `i:num`] MOI_S3ZB_ICHAIN_ADJ) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3ZB_TRI_PARITY = prove
 (`!c z (a:real^N) b d.
     lf_simplicial_complex c /\ (!e. e IN z ==> e IN c /\ aff_dim e = &1) /\
     convex hull {a,b,d} IN c /\ ~affine_dependent {a,b,d} /\
     ~(a = b) /\ ~(a = d) /\ ~(b = d)
     ==> (EVEN (CARD {e | e IN z /\ e SUBSET convex hull {a,b,d}}) <=>
          (segment[a,b] IN z <=> ~(segment[b,d] IN z <=> segment[d,a] IN z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`] MOI_S3ZB_TRI_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`segment[a:real^N,b]`; `segment[b:real^N,d]`;
                            `segment[d:real^N,a]`; `\e:real^N->bool. e IN z`]
    MOI_S3ZB_CARD3)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let MOI_S3ZB_COCYCLE_SYMDIFF = prove
 (`!c z z':(real^N->bool)->bool.
     lf_simplicial_complex c /\ z2_cocycle c z /\ z2_cocycle c z'
     ==> z2_cocycle c ((z DIFF z') UNION (z' DIFF z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[z2_cocycle] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN (z DIFF z') UNION (z' DIFF z) ==> e IN c /\ aff_dim e = &1`
  ASSUME_TAC THENL [REWRITE_TAC[IN_UNION; IN_DIFF] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S3ZB_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `EVEN (CARD {e | e IN z /\ e SUBSET convex hull {a:real^N,b,d}}) /\
                EVEN (CARD {e | e IN z' /\ e SUBSET convex hull {a:real^N,b,d}})` MP_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`] MOI_S3ZB_TRI_PARITY) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z':(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`] MOI_S3ZB_TRI_PARITY) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(z DIFF z') UNION (z' DIFF z):(real^N->bool)->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`] MOI_S3ZB_TRI_PARITY) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[IN_UNION; IN_DIFF] THEN CONV_TAC TAUT);;

let MOI_S3ZB_LPAR_SYMDIFF = prove
 (`!c z z' (p:real^1->real^N).
     lf_simplicial_complex c /\ z2_cocycle c z /\ z2_cocycle c z' /\
     path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p
     ==> (moi_s3zb_lpar c ((z DIFF z') UNION (z' DIFF z)) p <=>
          ~(moi_s3zb_lpar c z p <=> moi_s3zb_lpar c z' p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_ICHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_TAC `v:num->real^N`)) THEN
  SUBGOAL_THEN `z2_cocycle c ((z DIFF z') UNION (z' DIFF z):(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_COCYCLE_SYMDIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`; `p:real^1->real^N`;
                 `m:num`; `v:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z':(real^N->bool)->bool`; `p:real^1->real^N`;
                 `m:num`; `v:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(z DIFF z') UNION (z' DIFF z):(real^N->bool)->bool`;
                 `p:real^1->real^N`; `m:num`; `v:num->real^N`] MOI_S3ZB_LPAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MOI_S3ZB_PAR_SYMDIFF]);;

let MOI_S3ZB_FZ_EQ = prove
 (`!c z z':(real^N->bool)->bool.
     moi_s3zb_fz c z' = moi_s3zb_fz c z <=>
     !p. path p /\ path_image p SUBSET UNIONS c /\ pathfinish p = pathstart p
         ==> (moi_s3zb_lpar c z' p <=> moi_s3zb_lpar c z p)`,
  REWRITE_TAC[FUN_EQ_THM; moi_s3zb_fz] THEN MESON_TAC[]);;

let MOI_S3ZB_FZ_CHAR = prove
 (`!c z:(real^N->bool)->bool.
     lf_simplicial_complex c /\ z2_cocycle c z
     ==> moi_s33_char (UNIONS c) (moi_s3zb_fz c z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s33_char; moi_s3zb_fz] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3ZB_LPAR_HOMOTOPIC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^1->real^N`; `q:real^1->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `path ((p:real^1->real^N) ++ q) /\ path_image (p ++ q) SUBSET UNIONS c /\
                  pathfinish (p ++ q) = pathstart (p ++ q)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[PATH_JOIN; PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; UNION_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3ZB_LPAR_JOIN THEN ASM_REWRITE_TAC[]]);;

let MOI_S3ZB_CLASS_SELF = prove
 (`!c z:(real^N->bool)->bool. z2_cocycle c z ==> z IN moi_s33_z2class c z`,
  REWRITE_TAC[moi_s33_z2class; IN_ELIM_THM; DIFF_EQ_EMPTY; UNION_EMPTY] THEN
  SIMP_TAC[MOI_FD_Z2_COBOUNDARY_EMPTY]);;

let MOI_S3ZB_CLASS_IN = prove
 (`!c z z':(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ connected(UNIONS c) /\ ~(UNIONS c = {}) /\
     z2_cocycle c z
     ==> (z' IN moi_s33_z2class c z <=>
          z2_cocycle c z' /\ moi_s3zb_fz c z' = moi_s3zb_fz c z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s33_z2class; IN_ELIM_THM] THEN
  ASM_CASES_TAC `z2_cocycle c (z':(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `z2_cocycle c ((z DIFF z') UNION (z' DIFF z):(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3ZB_COCYCLE_SYMDIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_S3ZB_FZ_EQ] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `(z DIFF z') UNION (z' DIFF z):(real^N->bool)->bool`;
                   `p:real^1->real^N`] MOI_S3ZB_LPAR_COB) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `z':(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_LPAR_SYMDIFF) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    DISCH_TAC THEN MATCH_MP_TAC MOI_S3ZB_INJ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `z':(real^N->bool)->bool`; `p:real^1->real^N`] MOI_S3ZB_LPAR_SYMDIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC TAUT]);;

let MOI_S3ZB_CLASS_FZ = prove
 (`!c z:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c /\ connected(UNIONS c) /\ ~(UNIONS c = {}) /\
     z2_cocycle c z
     ==> moi_s3zb_fz c (@z'. z' IN moi_s33_z2class c z) = moi_s3zb_fz c z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(@z'. z' IN moi_s33_z2class c z) IN moi_s33_z2class c (z:(real^N->bool)->bool)`
  MP_TAC THENL
   [CONV_TAC SELECT_CONV THEN EXISTS_TAC `z:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_S3ZB_CLASS_SELF];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:(real^N->bool)->bool`;
                   `@z'. z' IN moi_s33_z2class c (z:(real^N->bool)->bool)`]
      MOI_S3ZB_CLASS_IN) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let Z2_CHAR = prove
 (MOI_S33_Z2_CHAR,
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `{phi | moi_s33_char (UNIONS c) phi} =
    IMAGE (\kk. moi_s3zb_fz c (@z:(real^N->bool)->bool. z IN kk))
          (moi_s33_h1z2 (c:(real^N->bool)->bool))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; moi_s33_h1z2] THEN BETA_TAC THEN
    X_GEN_TAC `phi:(real^1->real^N)->bool` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `phi:(real^1->real^N)->bool`]
        MOI_S3ZB_SURJ) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `moi_s33_z2class c (y:(real^N->bool)->bool)` THEN
      CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `y:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]] THEN
      ASM_SIMP_TAC[MOI_S3ZB_CLASS_FZ] THEN
      REWRITE_TAC[FUN_EQ_THM; moi_s3zb_fz] THEN X_GEN_TAC `p:real^1->real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^1->real^N`) THEN
      UNDISCH_TAC `moi_s33_char (UNIONS c) (phi:(real^1->real^N)->bool)` THEN
      REWRITE_TAC[moi_s33_char] THEN
      DISCH_THEN(MP_TAC o SPEC `p:real^1->real^N` o CONJUNCT1) THEN
      CONV_TAC TAUT;
      DISCH_THEN(X_CHOOSE_THEN `kk:((real^N->bool)->bool)->bool`
        (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `z:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
      ASM_SIMP_TAC[MOI_S3ZB_CLASS_FZ; MOI_S3ZB_FZ_CHAR]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
  REWRITE_TAC[moi_s33_h1z2; IN_ELIM_THM] THEN BETA_TAC THEN
  MAP_EVERY X_GEN_TAC [`k1:((real^N->bool)->bool)->bool`;
                       `k2:((real^N->bool)->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `z1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z2:(real^N->bool)->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_SIMP_TAC[MOI_S3ZB_CLASS_FZ] THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `z':(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_S3ZB_CLASS_IN]);;

