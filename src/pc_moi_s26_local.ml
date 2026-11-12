needs "src/pc_moi_s26_cross.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s26_local: the local picture of a 2-complex in real^3 near a       *)
(* relative interior point of a triangle (LOCAL_TRI), or of an edge lying in *)
(* exactly two triangles (LOCAL_EDGE), for Moise Sec 26 Theorem 6            *)
(* (MOISE_266).  Small balls meet the complex in a plane, or in two half     *)
(* planes with a common edge line, and the ball minus the complex splits     *)
(* into two open connected sides, each with the whole local sheet in its     *)
(* closure.  Route: isolation of the simplices through y (finiteness), the   *)
(* half plane shape of a triangle near an open edge (TRI_NEAR_EDGE, via      *)
(* functionals vanishing on the other two edges), and explicit half balls    *)
(* (PLANE_SIDES) or wedge sides (WEDGE_SIDES).                               *)
(* ========================================================================= *)

(* Near a point y only the simplices through y matter.                     *)

let MOI_S6L_ISOLATE = prove
 (`!(c:(real^3->bool)->bool) y.
     FINITE c /\ (!s. s IN c ==> closed s)
     ==> ?r. &0 < r /\
             !x. x IN ball(y,r)
                 ==> (x IN UNIONS c <=> x IN UNIONS {s | s IN c /\ y IN s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open ((:real^3) DIFF UNIONS {s | s IN c /\ ~((y:real^3) IN s)})`
  MP_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `ball(y:real^3,r) SUBSET (:real^3) DIFF UNIONS {s | s IN c /\ ~(y IN s)}` THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The simplices through a relative interior point of a triangle, or of an *)
(* edge, of a 2-complex.                                                    *)

let MOI_S6L_STAR_TRI = prove
 (`!(c:(real^3->bool)->bool) q y t.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     q IN c /\ aff_dim q = &2 /\ y IN relative_interior q /\ t IN c /\ y IN t
     ==> t = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `(t INTER q:real^3->bool) face_of t /\ (t INTER q) face_of q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t INTER q:real^3->bool = q` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t INTER q:real^3->bool`; `q:real^3->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior q` THEN
    UNDISCH_TAC `(y:real^3) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `t:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `(t INTER q:real^3->bool) face_of t` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (t:real^3->bool) <= &2` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_S6L_STAR_EDGE = prove
 (`!(c:(real^3->bool)->bool) e q q' y t.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     e IN c /\ aff_dim e = &1 /\
     {s | s IN c /\ aff_dim s = &2 /\ e SUBSET s} = {q,q'} /\
     y IN relative_interior e /\ t IN c /\ y IN t
     ==> t = e \/ t = q \/ t = q'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `(t INTER e:real^3->bool) face_of t /\ (t INTER e) face_of e`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t INTER e:real^3->bool = e` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t INTER e:real^3->bool`; `e:real^3->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `e:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior e` THEN
    UNDISCH_TAC `(y:real^3) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^3->bool = e` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real^3->bool) IN {s | s IN c /\ aff_dim s = &2 /\ e SUBSET s}`
  MP_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`e:real^3->bool`; `t:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
          UNDISCH_TAC `(t INTER e:real^3->bool) face_of t` THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (t:real^3->bool) <= &2` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC `t INTER e:real^3->bool = e` THEN SET_TAC[]];
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]]);;

(* The two open half balls on the two sides of a plane through y.         *)

let MOI_S6L_PLANE_SIDES = prove
 (`!(n:real^3) y r.
     ~(n = vec 0)
     ==> ?u v. open u /\ open v /\ connected u /\ connected v /\ DISJOINT u v /\
               u UNION v = ball(y,r) DIFF {x | n dot (x - y) = &0} /\
               ball(y,r) INTER {x | n dot (x - y) = &0} SUBSET
               closure u INTER closure v`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `ball(y:real^3,r) INTER {x | n dot x > n dot y}` THEN
  EXISTS_TAC `ball(y:real^3,r) INTER {x | n dot x < n dot y}` THEN
  SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_HALFSPACE_GT; OPEN_HALFSPACE_LT] THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_GT;
           CONVEX_HALFSPACE_LT] THEN
  REWRITE_TAC[DOT_RSUB; REAL_SUB_0] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN ball(y,r)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:real^3`; `n dot (y:real^3)`] CLOSURE_HALFSPACE_GT) THEN
  MP_TAC(ISPECL [`n:real^3`; `n dot (y:real^3)`] CLOSURE_HALFSPACE_LT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(y:real^3,r)`; `{x:real^3 | n dot x > n dot y}`]
    OPEN_INTER_CLOSURE_SUBSET) THEN
  MP_TAC(ISPECL [`ball(y:real^3,r)`; `{x:real^3 | n dot x < n dot y}`]
    OPEN_INTER_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_ge] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* A plane through y with a prescribed side.                                *)

let MOI_S6L_PLANE_ORIENT = prove
 (`!(s:real^3->bool) y z.
     aff_dim s = &2 /\ y IN affine hull s /\ ~(z IN affine hull s)
     ==> ?n. affine hull s = {x | n dot (x - y) = &0} /\ &0 < n dot (z - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_EQ_HYPERPLANE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a dot (y:real^3) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN affine hull s` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a dot (z:real^3) = b)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^3) IN affine hull s)` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < a dot ((z:real^3) - y)` THENL
   [EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    EXISTS_TAC `--a:real^3` THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LNEG; DOT_RSUB] THEN
    UNDISCH_TAC `~(&0 < a dot ((z:real^3) - y))` THEN
    ASM_REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC]);;

(* Small steps along a ray stay in an open ball; points approached along   *)
(* a ray are in the closure.                                                *)

let MOI_S6L_RAY_BALL = prove
 (`!(x:real^3) y r z.
     x IN ball(y,r)
     ==> ?d. &0 < d /\ !t. &0 < t /\ t < d ==> x + t % z IN ball(y,r)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(r - dist(y:real^3,x)) / (norm(z:real^3) + &1)` THEN
  UNDISCH_TAC `(x:real^3) IN ball(y,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `dist(y:real^3,x) + dist(x,x + t % z)` THEN
  REWRITE_TAC[DIST_TRIANGLE] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `x - (x + t % z):real^3 = --(t % z)`; NORM_NEG;
              NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  UNDISCH_TAC `t < (r - dist(y:real^3,x)) / (norm(z:real^3) + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;

let MOI_S6L_RAY_CLOSURE = prove
 (`!(s:real^3->bool) x z.
     (?d. &0 < d /\ !t. &0 < t /\ t < d ==> x + t % z IN s)
     ==> x IN closure s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / (norm(z:real^3) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t = min (d / &2) (e / (norm(z:real^3) + &1))` THEN
  SUBGOAL_THEN `&0 < t /\ t < d /\ t <= e / (norm(z:real^3) + &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < d` THEN
    UNDISCH_TAC `&0 < e / (norm(z:real^3) + &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `x + t % z:real^3` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(x + t % z) - x:real^3 = t % z`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  UNDISCH_TAC `t <= e / (norm(z:real^3) + &1)` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;

(* A vector orthogonal to one side of a triangle and positive on the        *)
(* opposite vertex.                                                         *)

let MOI_S6L_PERP = prove
 (`!(e0:real^3) e1 w.
     ~collinear {e0,e1,w}
     ==> ?m. m dot (e1 - e0) = &0 /\ &0 < m dot (w - e0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u:real^3 = e1 - e0` THEN ABBREV_TAC `v:real^3 = w - e0` THEN
  SUBGOAL_THEN `~((u dot u) % v - (u dot v) % (u:real^3) = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear {e0:real^3,e1,w}` THEN
    REWRITE_TAC[COLLINEAR_3_DOT_MULTIPLES] THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    MP_TAC(ISPECL [`u:real^3`; `v:real^3`] DOT_SYM) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((u dot u) % v - (u dot v) % (u:real^3) = vec 0)` THEN
    ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; VECTOR_MUL_LZERO; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `(u dot u) % v - (u dot v) % (u:real^3)` THEN CONJ_TAC THENL
   [REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    MP_TAC(ISPECL [`u:real^3`; `v:real^3`] DOT_SYM) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((u dot u) % v - (u dot v) % (u:real^3)) dot ((u dot u) % v - (u dot v) % u) =
    (u dot u) * (((u dot u) % v - (u dot v) % u) dot v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    MP_TAC(ISPECL [`u:real^3`; `v:real^3`] DOT_SYM) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(u dot u) % v - (u dot v) % (u:real^3)` DOT_POS_LT) THEN
  MP_TAC(ISPEC `u:real^3` DOT_POS_LT) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LT_MUL_EQ]);;

(* Near a point y of an open edge [e0,e1] of a triangle conv{e0,e1,w}, the *)
(* triangle is the closed half plane of its plane on the side of w, cut    *)
(* out by any functional m vanishing along the edge and positive at w.      *)

let MOI_S6L_TRI_NEAR_EDGE = prove
 (`!(e0:real^3) e1 w y m.
     ~collinear {e0,e1,w} /\ y IN segment(e0,e1) /\
     m dot (e1 - e0) = &0 /\ &0 < m dot (w - e0)
     ==> ?r. &0 < r /\
             !x. x IN ball(y,r)
                 ==> (x IN convex hull {e0,e1,w} <=>
                      x IN affine hull {e0,e1,w} /\ &0 <= m dot (x - y))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN segment(e0,e1)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`e1:real^3`; `w:real^3`; `e0:real^3`] MOI_S6L_PERP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~collinear {e0:real^3,e1,w}` THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN AP_TERM_TAC THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `ma:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`e0:real^3`; `w:real^3`; `e1:real^3`] MOI_S6L_PERP) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~collinear {e0:real^3,e1,w}` THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN AP_TERM_TAC THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `mb:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPEC `{x:real^3 | ma dot x > ma dot e1} INTER {x | mb dot x > mb dot e0}`
    OPEN_CONTAINS_BALL) THEN
  SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_GT] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN
    UNDISCH_TAC `&0 < ma dot (e0 - e1:real^3)` THEN
    UNDISCH_TAC `&0 < mb dot (e1 - e0:real^3)` THEN
    REWRITE_TAC[DOT_RSUB] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`&1 - s`; `ma dot (e0:real^3) - ma dot e1`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MP_TAC(ISPECL [`s:real`; `mb dot (e1:real^3) - mb dot e0`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ma dot (x:real^3) > ma dot e1 /\ mb dot x > mb dot e0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(y:real^3,r) SUBSET
                 {x | ma dot x > ma dot e1} INTER {x | mb dot x > mb dot e0}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_3; AFFINE_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `m dot (x - y:real^3) = c * (m dot (w - e0))` SUBST1_TAC THENL
     [UNDISCH_TAC `m dot (e1 - e0:real^3) = &0` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `a + b + c = &1` THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m dot (x - y:real^3) = c * (m dot (w - e0))` ASSUME_TAC THENL
     [UNDISCH_TAC `m dot (e1 - e0:real^3) = &0` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `a + b + c = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `ma dot (x:real^3) - ma dot e1 = a * (ma dot (e0 - e1))` ASSUME_TAC
    THENL
     [UNDISCH_TAC `ma dot (w - e1:real^3) = &0` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `a + b + c = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `mb dot (x:real^3) - mb dot e0 = b * (mb dot (e1 - e0))` ASSUME_TAC
    THENL
     [UNDISCH_TAC `mb dot (w - e0:real^3) = &0` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `a + b + c = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`a:real`; `ma dot (e0 - e1:real^3)`]
        (CONJUNCT2 REAL_LT_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term ((=) `ma:real^3`)) (concl th) &&
        is_eq (concl th) && is_binary "real_sub" (lhs(concl th)))) THEN
      UNDISCH_TAC `ma dot (x:real^3) > ma dot e1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(ISPECL [`b:real`; `mb dot (e1 - e0:real^3)`]
        (CONJUNCT2 REAL_LT_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term ((=) `mb:real^3`)) (concl th) &&
        is_eq (concl th) && is_binary "real_sub" (lhs(concl th)))) THEN
      UNDISCH_TAC `mb dot (x:real^3) > mb dot e0` THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`c:real`; `m dot (w - e0:real^3)`]
        (CONJUNCT2 REAL_LE_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq (concl th) && lhs(concl th) = `m dot (x - y:real^3)`)) THEN
      ASM_REWRITE_TAC[]]]);;

(* An edge of a triangle, with the triangle relabelled so that the edge is *)
(* the segment between its first two vertices.                              *)

let MOI_S6L_EDGE_OF_TRI = prove
 (`!(va:real^3) vb vc e.
     ~collinear {va,vb,vc} /\ e face_of convex hull {va,vb,vc} /\ aff_dim e = &1
     ==> ?e0 e1 w. ~collinear {e0,e1,w} /\
                   convex hull {va,vb,vc} = convex hull {e0,e1,w} /\
                   affine hull {va,vb,vc} = affine hull {e0,e1,w} /\
                   e = segment[e0,e1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {va:real^3,vb,vc}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  UNDISCH_TAC `e face_of convex hull {va:real^3,vb,vc}` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `(va:real^3) IN d` THEN ASM_CASES_TAC `(vb:real^3) IN d` THEN
  ASM_CASES_TAC `(vc:real^3) IN d` THENL
   [SUBGOAL_THEN `d = {va:real^3,vb,vc}` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`va:real^3`; `vb:real^3`; `vc:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
    REWRITE_TAC[ASSUME `~collinear {va:real^3,vb,vc}`] THEN STRIP_TAC THEN
    UNDISCH_TAC `aff_dim (convex hull {va:real^3,vb,vc}) = &1` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];
    SUBGOAL_THEN `d = {va:real^3,vb}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`va:real^3`; `vb:real^3`; `vc:real^3`] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    SUBGOAL_THEN `d = {vc:real^3,va}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`vc:real^3`; `va:real^3`; `vb:real^3`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `{vc:real^3,va,vb} = {va,vb,vc}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `d = {va:real^3}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull {va:real^3}) = &1` THEN
    REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[];
    SUBGOAL_THEN `d = {vb:real^3,vc}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`vb:real^3`; `vc:real^3`; `va:real^3`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `{vb:real^3,vc,va} = {va,vb,vc}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `d = {vb:real^3}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull {vb:real^3}) = &1` THEN
    REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[];
    SUBGOAL_THEN `d = {vc:real^3}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull {vc:real^3}) = &1` THEN
    REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[];
    SUBGOAL_THEN `d:real^3->bool = {}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (convex hull ({}:real^3->bool)) = &1` THEN
    REWRITE_TAC[CONVEX_HULL_EMPTY; AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[]]);;

(* A plane through y as the zero set of a functional centred at y.         *)

let MOI_S6L_PLANE_THROUGH = prove
 (`!(s:real^3->bool) y.
     aff_dim s = &2 /\ y IN affine hull s
     ==> ?n. ~(n = vec 0) /\ affine hull s = {x | n dot (x - y) = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_EQ_HYPERPLANE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a dot (y:real^3) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN affine hull s` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

(* The two sides of two half planes with a common edge line through y, in *)
(* two different planes: f1 = m1.(x - y) and f2 = m2.(x - y) cut out the    *)
(* half planes {f1 = 0, f2 >= 0} and {f2 = 0, f1 >= 0}; z0 points into the  *)
(* convex wedge between them.                                               *)

let MOI_S6L_WEDGE_SIDES = prove
 (`!(m1:real^3) m2 z0 y r.
     &0 < r /\ &0 < m1 dot z0 /\ &0 < m2 dot z0
     ==> ?u v. open u /\ open v /\ connected u /\ connected v /\ DISJOINT u v /\
               u UNION v =
               ball(y,r) DIFF
               ({x | m1 dot (x - y) = &0 /\ &0 <= m2 dot (x - y)} UNION
                {x | m2 dot (x - y) = &0 /\ &0 <= m1 dot (x - y)}) /\
               ball(y,r) INTER
               ({x | m1 dot (x - y) = &0 /\ &0 <= m2 dot (x - y)} UNION
                {x | m2 dot (x - y) = &0 /\ &0 <= m1 dot (x - y)})
               SUBSET closure u INTER closure v`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `ball(y:real^3,r) INTER {x | m1 dot x > m1 dot y} INTER
              {x | m2 dot x > m2 dot y}` THEN
  EXISTS_TAC `ball(y:real^3,r) INTER
              ({x | m1 dot x < m1 dot y} UNION {x | m2 dot x < m2 dot y})` THEN
  SIMP_TAC[OPEN_INTER; OPEN_UNION; OPEN_BALL; OPEN_HALFSPACE_GT;
           OPEN_HALFSPACE_LT] THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_GT] THEN
  SUBGOAL_THEN `~(m1:real^3 = vec 0) /\ ~(m2:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < m1 dot (z0:real^3)` THEN UNDISCH_TAC `&0 < m2 dot (z0:real^3)` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNION_OVER_INTER] THEN MATCH_MP_TAC CONNECTED_UNION THEN
    SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_LT] THEN
    MP_TAC(ISPECL [`y:real^3`; `y:real^3`; `r:real`; `--z0:real^3`] MOI_S6L_RAY_BALL) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y + d / &2 % --z0:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RNEG] THEN
      MP_TAC(ISPECL [`d / &2`; `m1 dot (z0:real^3)`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RNEG] THEN
      MP_TAC(ISPECL [`d / &2`; `m2 dot (z0:real^3)`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RSUB] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN ball(y,r)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `(x:real^3) IN ball(y,r)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  (FIRST_ASSUM(MP_TAC o SPEC `z0:real^3` o MATCH_MP MOI_S6L_RAY_BALL) THEN
   DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o SPEC `--m1:real^3` o MATCH_MP MOI_S6L_RAY_BALL) THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM(MP_TAC o SPEC `--m2:real^3` o MATCH_MP MOI_S6L_RAY_BALL) THEN
   DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
   MP_TAC(ISPEC `m1:real^3` DOT_POS_LT) THEN MP_TAC(ISPEC `m2:real^3` DOT_POS_LT) THEN
   ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
   CONJ_TAC THEN MATCH_MP_TAC MOI_S6L_RAY_CLOSURE THENL
    [EXISTS_TAC `z0:real^3` THEN EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `t:real` THEN STRIP_TAC THEN
     REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
     CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MP_TAC(ISPECL [`t:real`; `m1 dot (z0:real^3)`] REAL_LT_MUL) THEN
     MP_TAC(ISPECL [`t:real`; `m2 dot (z0:real^3)`] REAL_LT_MUL) THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     FIRST
      [EXISTS_TAC `--m1:real^3` THEN EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[] THEN
       X_GEN_TAC `t:real` THEN STRIP_TAC THEN
       REWRITE_TAC[IN_INTER; IN_UNION; IN_ELIM_THM; DOT_RADD; DOT_RMUL; DOT_RNEG] THEN
       CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISJ1_TAC THEN
       MP_TAC(ISPECL [`t:real`; `m1 dot (m1:real^3)`] REAL_LT_MUL) THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
       EXISTS_TAC `--m2:real^3` THEN EXISTS_TAC `d2:real` THEN ASM_REWRITE_TAC[] THEN
       X_GEN_TAC `t:real` THEN STRIP_TAC THEN
       REWRITE_TAC[IN_INTER; IN_UNION; IN_ELIM_THM; DOT_RADD; DOT_RMUL; DOT_RNEG] THEN
       CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISJ2_TAC THEN
       MP_TAC(ISPECL [`t:real`; `m2 dot (m2:real^3)`] REAL_LT_MUL) THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]));;

(* Main theorem: the local picture at a relative interior point of a         *)
(* triangle.                                                                 *)

let LOCAL_TRI = prove
 (MOI_S26_LOCAL_TRI,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (c:(real^3->bool)->bool) /\ (!s. s IN c ==> closed s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_S6L_ISOLATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iso"))) THEN
  SUBGOAL_THEN `UNIONS {s | s IN c /\ (y:real^3) IN s} = q` (LABEL_TAC "star") THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t:real^3->bool = q` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC MOI_S6L_STAR_TRI THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior q` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `y:real^3`] MOI_S6L_PLANE_THROUGH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(y:real^3,r) SUBSET ball(y,r1) /\ ball(y,r) SUBSET ball(y,r2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_INTER] THEN ASM_CASES_TAC `(x:real^3) IN ball(y,r)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "iso" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "star" SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `ball(y:real^3,r2) INTER affine hull q SUBSET q` THEN
    UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(y,r2)` THEN
    UNDISCH_TAC `(x:real^3) IN ball(y,r)` THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6L_PLANE_SIDES THEN ASM_REWRITE_TAC[]]);;

(* The two triangles at an edge lying in exactly two triangles, labelled    *)
(* with a common edge [e0,e1]; the simplices through y in the open edge.   *)

let MOI_S6L_EDGE_SETUP = prove
 (`!(c:(real^3->bool)->bool) e q q' y.
     simplicial_complex c /\ e IN c /\ aff_dim e = &1 /\
     {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {q,q'} /\
     y IN relative_interior e
     ==> q IN c /\ q' IN c /\ aff_dim q = &2 /\ aff_dim q' = &2 /\
         e SUBSET q /\ e SUBSET q' /\
         ?e0 e1 w w'. ~collinear {e0,e1,w} /\ ~collinear {e0,e1,w'} /\
                      q = convex hull {e0,e1,w} /\ q' = convex hull {e0,e1,w'} /\
                      e = segment[e0,e1] /\ y IN segment(e0,e1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(q:real^3->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} /\
    (q':real^3->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t:real^3->bool. t IN c /\ e SUBSET t ==> e face_of t`
  (LABEL_TAC "ef") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`e:real^3->bool`; `t:real^3->bool`] o
               last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e INTER t:real^3->bool = e` SUBST1_TAC THENL
     [UNDISCH_TAC `(e:real^3->bool) SUBSET t` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`] MOI_S6X_SC_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `va:real^3` (X_CHOOSE_THEN `vb:real^3`
    (X_CHOOSE_THEN `vc:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`va:real^3`; `vb:real^3`; `vc:real^3`; `e:real^3->bool`]
    MOI_S6L_EDGE_OF_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `q = convex hull {va:real^3,vb,vc}` (SUBST1_TAC o SYM) THEN
    USE_THEN "ef" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3` (X_CHOOSE_THEN `e1:real^3`
    (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q':real^3->bool`] MOI_S6X_SC_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vd:real^3` (X_CHOOSE_THEN `ve:real^3`
    (X_CHOOSE_THEN `vf:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`vd:real^3`; `ve:real^3`; `vf:real^3`; `e:real^3->bool`]
    MOI_S6L_EDGE_OF_TRI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `~collinear {vd:real^3,ve,vf}`;
                ASSUME `aff_dim (e:real^3->bool) = &1`] THEN
    UNDISCH_THEN `q' = convex hull {vd:real^3,ve,vf}` (SUBST1_TAC o SYM) THEN
    USE_THEN "ef" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^3` (X_CHOOSE_THEN `f1:real^3`
    (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `{f0:real^3,f1} = {e0,e1}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT1 SEGMENT_EQ)] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{f0:real^3,f1,w'} = {e0,e1,w'}` ASSUME_TAC THENL
   [UNDISCH_TAC `{f0:real^3,f1} = {e0,e1}` THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e0:real^3`; `e1:real^3`; `w:real^3`; `w':real^3`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `~collinear {f0:real^3,f1,w'}` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(e0:real^3 = e1)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~collinear {e0:real^3,e1,w}` THEN
      ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior e` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT]]);;

let MOI_S6L_EDGE_STAR = prove
 (`!(c:(real^3->bool)->bool) e q q' y.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     e IN c /\ aff_dim e = &1 /\
     {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {q,q'} /\
     y IN relative_interior e
     ==> UNIONS {s | s IN c /\ y IN s} = q UNION q'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(q:real^3->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} /\
    (q':real^3->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior e` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`; `q:real^3->bool`;
                   `q':real^3->bool`; `y:real^3`; `t:real^3->bool`]
      MOI_S6L_STAR_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET q` THEN SET_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `q:real^3->bool`; EXISTS_TAC `q':real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* A point of the open edge lies in the triangle and in its plane.         *)

let MOI_S6L_SEG_IN_TRI = prove
 (`!(e0:real^3) e1 w y.
     y IN segment(e0,e1)
     ==> y IN convex hull {e0,e1,w} /\ y IN affine hull {e0,e1,w}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull {e0,e1,w}` ASSUME_TAC THENL
   [SUBGOAL_THEN `segment(e0:real^3,e1) SUBSET convex hull {e0,e1,w}` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[e0:real^3,e1]` THEN
      REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM SET_TAC[]];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `{e0:real^3,e1,w}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM SET_TAC[]]);;

(* Two triangles conv{e0,e1,w} and conv{e0,e1,w'} sharing the edge         *)
(* [e0,e1], with y in the open edge.  If they are coplanar and meet in a   *)
(* set of dimension below 2, near y their union is the whole plane.        *)

let MOI_S6L_COPLANAR_PAIR = prove
 (`!(e0:real^3) e1 w w' y.
     ~collinear {e0,e1,w} /\ ~collinear {e0,e1,w'} /\
     w' IN affine hull {e0,e1,w} /\ y IN segment(e0,e1) /\
     aff_dim (convex hull {e0,e1,w} INTER convex hull {e0,e1,w'}) < &2
     ==> ?r. &0 < r /\
             !x. x IN ball(y,r)
                 ==> (x IN convex hull {e0,e1,w} UNION convex hull {e0,e1,w'} <=>
                      x IN affine hull {e0,e1,w})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e0:real^3 = e1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN segment(e0,e1)` THEN SIMP_TAC[IN_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `y:real^3`]
    MOI_S6L_SEG_IN_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`] MOI_S6L_PERP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?cc. ~(cc = &0) /\ m dot (w' - e0:real^3) = cc * (m dot (w - e0))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?a b cc. a + b + cc = &1 /\ w':real^3 = a % e0 + b % e1 + cc % w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w':real^3) IN affine hull {e0,e1,w}` THEN
      REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `cc:real` THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~collinear {e0:real^3,e1,w'}` THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`] COLLINEAR_3_AFFINE_HULL) THEN
      REWRITE_TAC[ASSUME `~(e0:real^3 = e1)`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      UNDISCH_TAC `a + b + cc = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `m dot (e1 - e0:real^3) = &0` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
      UNDISCH_TAC `a + b + cc = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {e0,e1,w'} = affine hull {e0:real^3,e1,w}` ASSUME_TAC
  THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM HULL_HULL] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
      MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
      MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
      ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN SIMP_TAC[INT_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `y:real^3`; `m:real^3`]
    MOI_S6L_TRI_NEAR_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  SUBGOAL_THEN `cc < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < cc` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`; `y:real^3`; `m:real^3`]
      MOI_S6L_TRI_NEAR_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
    SUBGOAL_THEN
     `convex hull {e0,e1,w} INTER ball(y,min r1 r2) SUBSET
      convex hull {e0,e1,w} INTER convex hull {e0:real^3,e1,w'}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN ball(y,r1) /\ x IN ball(y,r2)` STRIP_ASSUME_TAC
      THENL
       [UNDISCH_TAC `(x:real^3) IN ball(y,min r1 r2)` THEN
        REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "n2" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r2)`)]) THEN
      UNDISCH_TAC `(x:real^3) IN convex hull {e0,e1,w}` THEN
      USE_THEN "n1" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r1)`)]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex hull {e0:real^3,e1,w}`; `ball(y:real^3,min r1 r2)`]
      AFF_DIM_CONVEX_INTER_OPEN) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONVEX_CONVEX_HULL; OPEN_BALL; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_MIN];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
    REWRITE_TAC[ASSUME `~collinear {e0:real^3,e1,w}`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`convex hull {e0,e1,w} INTER ball(y:real^3,min r1 r2)`;
      `convex hull {e0,e1,w} INTER convex hull {e0:real^3,e1,w'}`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim (convex hull {e0,e1,w} INTER convex hull {e0:real^3,e1,w'}) < &2` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`; `y:real^3`; `--m:real^3`]
    MOI_S6L_TRI_NEAR_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LNEG] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --(c * k) <=> &0 < --c * k`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN ball(y,r1) /\ x IN ball(y,r2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN ball(y,min r1 r2)` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN
  USE_THEN "n1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN ball(y,r1)`)]) THEN
  USE_THEN "n2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN ball(y,r2)`)]) THEN
  ASM_REWRITE_TAC[DOT_LNEG] THEN
  ASM_CASES_TAC `(x:real^3) IN affine hull {e0,e1,w}` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* If they are not coplanar, near y they are the half planes               *)
(* {n1 = 0, n2 >= 0} and {n2 = 0, n1 >= 0} of two functionals centred at y, *)
(* and (w - y) + (w' - y) points into the wedge between them.              *)

let MOI_S6L_NONCOPLANAR_PAIR = prove
 (`!(e0:real^3) e1 w w' y.
     ~collinear {e0,e1,w} /\ ~collinear {e0,e1,w'} /\
     ~(w' IN affine hull {e0,e1,w}) /\ y IN segment(e0,e1)
     ==> ?n1 n2 r. &0 < r /\
                   &0 < n1 dot ((w - y) + (w' - y)) /\
                   &0 < n2 dot ((w - y) + (w' - y)) /\
                   !x. x IN ball(y,r)
                       ==> (x IN convex hull {e0,e1,w} <=>
                            n1 dot (x - y) = &0 /\ &0 <= n2 dot (x - y)) /\
                           (x IN convex hull {e0,e1,w'} <=>
                            n2 dot (x - y) = &0 /\ &0 <= n1 dot (x - y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `y:real^3`]
    MOI_S6L_SEG_IN_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`; `y:real^3`]
    MOI_S6L_SEG_IN_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim {e0:real^3,e1,w} = &2 /\ aff_dim {e0:real^3,e1,w'} = &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
    MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`] MOI_S6X_TRI_FACE_FACTS) THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^3) IN affine hull {e0,e1,w'})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((w':real^3) IN affine hull {e0,e1,w})` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `affine hull {e0,e1,w} = affine hull {e0:real^3,e1,w'}` SUBST1_TAC
    THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM HULL_HULL] THEN
      MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; INT_LE_REFL]];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{e0:real^3,e1,w}`; `y:real^3`; `w':real^3`] MOI_S6L_PLANE_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{e0:real^3,e1,w'}`; `y:real^3`; `w:real^3`] MOI_S6L_PLANE_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `n1 dot (e0 - y:real^3) = &0 /\ n1 dot (e1 - y:real^3) = &0 /\
    n1 dot (w - y:real^3) = &0 /\ n2 dot (e0 - y:real^3) = &0 /\
    n2 dot (e1 - y:real^3) = &0 /\ n2 dot (w' - y:real^3) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `{e0:real^3,e1,w}`] HULL_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `{e0:real^3,e1,w'}`] HULL_SUBSET) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `y:real^3`; `n2:real^3`]
    MOI_S6L_TRI_NEAR_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `n2 dot (e1 - e0:real^3) = n2 dot (e1 - y) - n2 dot (e0 - y) /\
      n2 dot (w - e0:real^3) = n2 dot (w - y) - n2 dot (e0 - y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t1"))) THEN
  MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w':real^3`; `y:real^3`; `n1:real^3`]
    MOI_S6L_TRI_NEAR_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `n1 dot (e1 - e0:real^3) = n1 dot (e1 - y) - n1 dot (e0 - y) /\
      n1 dot (w' - e0:real^3) = n1 dot (w' - y) - n1 dot (e0 - y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t2"))) THEN
  MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`; `min r1 r2`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; DOT_RADD] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN ball(y,r1) /\ x IN ball(y,r2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN ball(y,min r1 r2)` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "t1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN ball(y,r1)`)]) THEN
  USE_THEN "t2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN ball(y,r2)`)]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* Main theorem: the local picture at a relative interior point of an edge *)
(* lying in exactly two triangles.                                          *)

let LOCAL_EDGE = prove
 (MOI_S26_LOCAL_EDGE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (c:(real^3->bool)->bool) /\ (!s. s IN c ==> closed s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_S6L_ISOLATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iso"))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`; `q:real^3->bool`;
                 `q':real^3->bool`; `y:real^3`] MOI_S6L_EDGE_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "star") THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`; `q:real^3->bool`;
                 `q':real^3->bool`; `y:real^3`] MOI_S6L_EDGE_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3` (X_CHOOSE_THEN `e1:real^3`
    (X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `q':real^3->bool`]
    MOI_S6X_SC_INTER_LOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_THEN `q = convex hull {e0:real^3,e1,w}` SUBST_ALL_TAC THEN
  UNDISCH_THEN `q' = convex hull {e0:real^3,e1,w'}` SUBST_ALL_TAC THEN
  SUBGOAL_THEN `aff_dim {e0:real^3,e1,w} = &2 /\ (y:real^3) IN affine hull {e0,e1,w}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM AFF_DIM_CONVEX_HULL] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `y:real^3`]
        MOI_S6L_SEG_IN_TRI) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w':real^3) IN affine hull {e0,e1,w}` THENL
   [MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `w':real^3`; `y:real^3`]
      MOI_S6L_COPLANAR_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
    MP_TAC(ISPECL [`{e0:real^3,e1,w}`; `y:real^3`] MOI_S6L_PLANE_THROUGH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!x:real^3. x IN ball(y,r)
         ==> (x IN UNIONS c <=>
              x IN convex hull {e0,e1,w} UNION convex hull {e0,e1,w'}) /\
             (x IN convex hull {e0,e1,w} UNION convex hull {e0,e1,w'} <=>
              n dot (x - y) = &0)`
    (LABEL_TAC "pt") THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN ball(y,r1) /\ x IN ball(y,r2)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN ball(y,r)` THEN UNDISCH_TAC `r <= min r1 r2` THEN
        REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "iso" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r1)`)]) THEN
      USE_THEN "star" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r2)`)]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n:real^3`; `y:real^3`; `r:real`] MOI_S6L_PLANE_SIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "pt" MP_TAC THEN SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`u UNION v = ball(y:real^3,r) DIFF {x | n dot (x - y) = &0}`;
      `ball(y:real^3,r) INTER {x | n dot (x - y) = &0} SUBSET
       closure u INTER closure v`] THEN
    REMOVE_THEN "pt" MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
    MP_TAC(ISPECL [`e0:real^3`; `e1:real^3`; `w:real^3`; `w':real^3`; `y:real^3`]
      MOI_S6L_NONCOPLANAR_PAIR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `n2:real^3`
      (X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "loc"))))))) THEN
    EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!x:real^3. x IN ball(y,r)
         ==> (x IN UNIONS c <=>
              x IN convex hull {e0,e1,w} UNION convex hull {e0,e1,w'}) /\
             (x IN convex hull {e0,e1,w} UNION convex hull {e0,e1,w'} <=>
              x IN {x | n1 dot (x - y) = &0 /\ &0 <= n2 dot (x - y)} UNION
                   {x | n2 dot (x - y) = &0 /\ &0 <= n1 dot (x - y)})`
    (LABEL_TAC "pt") THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN ball(y,r1) /\ x IN ball(y,r2)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN ball(y,r)` THEN UNDISCH_TAC `r <= min r1 r2` THEN
        REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "iso" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r1)`)]) THEN
      USE_THEN "star" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN ball(y,r2)`)]);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`n1:real^3`; `n2:real^3`; `(w - y) + (w' - y):real^3`; `y:real^3`;
                   `r:real`] MOI_S6L_WEDGE_SIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "pt" MP_TAC THEN SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`u UNION v =
       ball(y:real^3,r) DIFF
       ({x | n1 dot (x - y) = &0 /\ &0 <= n2 dot (x - y)} UNION
        {x | n2 dot (x - y) = &0 /\ &0 <= n1 dot (x - y)})`;
      `ball(y:real^3,r) INTER
       ({x | n1 dot (x - y) = &0 /\ &0 <= n2 dot (x - y)} UNION
        {x | n2 dot (x - y) = &0 /\ &0 <= n1 dot (x - y)})
       SUBSET closure u INTER closure v`] THEN
    REMOVE_THEN "pt" MP_TAC THEN SET_TAC[]]);;

