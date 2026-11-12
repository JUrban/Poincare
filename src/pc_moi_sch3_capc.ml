(* ========================================================================= *)
(* pc_moi_sch3_capc: main theorem CAP_COUNT, the closed term                *)
(* MOI_STL_CAP_COUNT of pc_moi_sch3_tilt.ml, from which REDUCE_FROM_COUNT   *)
(* gives REDUCE (Moise GTM 47, proof of 17.12, Lemma 1, pp.122-123).        *)
(* Route (perturbation lemma): pull the tilted level of the cap back to     *)
(* the original sphere UNIONS c by g; there it is the zero set of           *)
(* psi y = a1 dot (f y - f p), a Lipschitz perturbation of the flat height  *)
(* a dot (y - p).  On every triangle of c a map, affine on the triangle,    *)
(* sends the zero set of psi injectively into the flat level set; the       *)
(* glued map is PL and injective, so MOI_SLV_HOMEO_POLYGONS compares the    *)
(* polygon counts, and the inner polygon j0 is not hit (side clause).       *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_tilt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Helpers: barycentric relative interior of a triangle, slices of       *)
(* polyhedra, PL maps are Lipschitz on polytopes, positive lower bounds.    *)
(* ------------------------------------------------------------------------- *)

(* A restatement of MOI_SBA_RELINT_3 (pc_moi_smo_base.ml, not in the load   *)
(* closure of this file).                                                   *)

let MOI_SCC_RELINT_3 = prove
 (`!p1 p2 p3 x:real^N.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p2 = p3) /\ ~affine_dependent {p1,p2,p3}
     ==> (x IN relative_interior(convex hull {p1,p2,p3}) <=>
          ?u1 u2 u3. &0 < u1 /\ &0 < u2 /\ &0 < u3 /\
                     u1 + u2 + u3 = &1 /\
                     x = u1 % p1 + u2 % p2 + u3 % p3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{p1,p2,p3}:real^N->bool`
    RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[REAL_ADD_RID; VECTOR_ADD_RID] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`(u:real^N->real) p1`; `(u:real^N->real) p2`; `(u:real^N->real) p3`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
     (X_CHOOSE_THEN `u3:real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `\y:real^N. if y = p1 then u1:real else if y = p2 then u2 else u3` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SCC_POLYHEDRON_HYPERPLANE = prove
 (`!(s:real^N->bool) (b:real^N) r.
     pl_polyhedron s ==> pl_polyhedron (s INTER {x | b dot x = r})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{k INTER {x:real^N | b dot x = r} | k IN c}` THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[POLYTOPE_INTER_POLYHEDRON; POLYHEDRON_HYPERPLANE] THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE] THEN SET_TAC[]);;

let MOI_SCC_POS_LB = prove
 (`!(s:A->bool) (g:A->real).
     FINITE s /\ (!x. x IN s ==> &0 < g x)
     ==> ?m. &0 < m /\ !x. x IN s ==> m <= g x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (g:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
  EXISTS_TAC `inf (IMAGE (g:A->real) s)` THEN ASM_SIMP_TAC[]);;

(* A PL map on a polytope is Lipschitz there: finitely many affine pieces   *)
(* (MOI_PLM_PL_MAP_ON_COMPACT_FINITE), near x only the pieces through x     *)
(* matter, and LOCALLY_LIPSCHITZ_GEN globalises on the convex polytope.     *)

let MOI_SCC_PL_LIPSCHITZ = prove
 (`!(k:real^M->bool) (f:real^M->real^N).
     polytope k /\ pl_map_on k f
     ==> ?M. &0 <= M /\
             !x y. x IN k /\ y IN k ==> norm(f x - f y) <= M * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `f:real^M->real^N`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?L Y. !q. q IN cc
              ==> linear((L:(real^M->bool)->real^M->real^N) q) /\
                  !z. z IN q ==> (f:real^M->real^N) z = L q z + (Y:(real^M->bool)->real^N) q`
  (X_CHOOSE_THEN `L:(real^M->bool)->real^M->real^N`
    (X_CHOOSE_THEN `Y:(real^M->bool)->real^N` (LABEL_TAC "LY"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `M = sum cc (\q:real^M->bool. onorm((L:(real^M->bool)->real^M->real^N) q))` THEN
  SUBGOAL_THEN
   `!q:real^M->bool. q IN cc
      ==> onorm((L:(real^M->bool)->real^M->real^N) q) <= M`
  (LABEL_TAC "onb") THENL
   [MP_TAC(ISPECL
     [`\q:real^M->bool. onorm((L:(real^M->bool)->real^M->real^N) q)`;
      `M:real`; `cc:(real^M->bool)->bool`] SUM_POS_BOUND) THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[ONORM_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `M:real` THEN CONJ_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_MESON_TAC[ONORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_GEN THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `b:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `closed (UNIONS {q:real^M->bool | q IN cc /\ ~(x IN q)})` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `cc:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[IN_ELIM_THM; POLYTOPE_IMP_CLOSED]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [closed]) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
  REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q:real^M->bool. q IN cc /\ y IN q` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^M) IN q` ASSUME_TAC THENL
   [REMOVE_THEN "ball" (MP_TAC o SPEC `y:real^M` o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  USE_THEN "LY" (MP_TAC o C MATCH_MP (ASSUME `(q:real^M->bool) IN cc`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:real^M->real^N) y - f x = (L:(real^M->bool)->real^M->real^N) q (y - x)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `onorm((L:(real^M->bool)->real^M->real^N) q) * norm(y - x:real^M)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ONORM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  USE_THEN "onb" (MP_TAC o C MATCH_MP (ASSUME `(q:real^M->bool) IN cc`)) THEN
  UNDISCH_TAC `M < b` THEN REAL_ARITH_TAC);;

(* Smallness: for finitely many constraints e * X < Y with Y > 0.          *)

let MOI_SCC_SMALL = prove
 (`!X Y. &0 < Y ==> ?e. &0 < e /\ !e'. &0 < e' /\ e' <= e ==> e' * X < Y`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `Y / (abs X + &1)` THEN
  SUBGOAL_THEN `&0 < abs X + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LET_TRANS `e * abs X` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS `Y / (abs X + &1) * abs X` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < z ==> Y / z * x = (Y * x) / z`; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

(* Restatements of MOI_CEL_PL_MAP_ON_EMPTY and                              *)
(* MOI_CEL_PL_MAP_ON_UNIONS_FINITE (pc_moi_cells.ml, not in the load        *)
(* closure of this file):                                                   *)
(* PL maps paste over finitely many closed pieces.                          *)

let MOI_SCC_PL_MAP_ON_EMPTY = prove
 (`!f:real^M->real^N. pl_map_on {} f`,
  REWRITE_TAC[pl_map_on; NOT_IN_EMPTY]);;

let MOI_SCC_PL_MAP_ON_UNIONS_FINITE = prove
 (`!(c:(real^M->bool)->bool) (f:real^M->real^N).
     FINITE c /\ (!s. s IN c ==> closed s /\ pl_map_on s f)
     ==> pl_map_on (UNIONS c) f`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; MOI_SCC_PL_MAP_ON_EMPTY; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `c:(real^M->bool)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed (t:real^M->bool) /\ pl_map_on t (f:real^M->real^N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (UNIONS c:real^M->bool) (f:real^M->real^N)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS c:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Tools for one triangle conv{v0,v1,v2}: coordinates along the edges at *)
(* v0, a normal to v1 - v0 in the plane, strict monotonicity of a Lipschitz *)
(* perturbation of a height along a direction where the height grows, and   *)
(* the intermediate value theorem on a segment.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SCC_TRI_COORD = prove
 (`!v0 v1 v2 (y:real^N).
     y IN convex hull {v0,v1,v2} <=>
     ?s1 s2. &0 <= s1 /\ &0 <= s2 /\ s1 + s2 <= &1 /\
             y = v0 + s1 % (v1 - v0) + s2 % (v2 - v0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
      (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`v:real`; `w:real`] THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `u = &1 - v - w` SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`&1 - s1 - s2`; `s1:real`; `s2:real`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    VECTOR_ARITH_TAC]);;

let MOI_SCC_GRAM = prove
 (`!x y:real^N.
     ~(x = vec 0) /\ ~(?c. y = c % x)
     ==> ((x dot x) % y - (x dot y) % x) dot x = &0 /\
         &0 < ((x dot x) % y - (x dot y) % x) dot y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((x dot x) % y - (x dot y) % x) dot (x:real^N) = &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] DOT_SYM) THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `n:real^N = (x dot x) % y - (x dot y) % x` THEN
  SUBGOAL_THEN `~(n:real^N = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THEN
    EXISTS_TAC `(x dot y) / (x dot (x:real^N))` THEN
    SUBGOAL_THEN `~(x dot (x:real^N) = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
    EXISTS_TAC `x dot (x:real^N)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_LMUL] THEN
    UNDISCH_TAC `(x dot x) % y - (x dot y) % x = vec 0:real^N` THEN
    REWRITE_TAC[VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `n dot n = (x dot (x:real^N)) * (n dot (y:real^N))` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `n dot ((x dot x) % y - (x dot y) % x) =
      (x dot x) * (n dot y) - (x dot y) * (n dot (x:real^N))`
    MP_TAC THENL [REWRITE_TAC[DOT_RSUB; DOT_RMUL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n dot (n:real^N)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < x dot (x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ]);;

let MOI_SCC_TRI_NORMAL = prove
 (`!v0 v1 v2:real^N.
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\ ~affine_dependent {v0,v1,v2}
     ==> ?n. n dot (v1 - v0) = &0 /\ &0 < n dot (v2 - v0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v1 - v0:real^N`; `v2 - v0:real^N`] MOI_SCC_GRAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`]
      COLLINEAR_3_EQ_AFFINE_DEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a:real^N,b,c} = {b,a,c}`] THEN
    REWRITE_TAC[COLLINEAR_3; COLLINEAR_LEMMA] THEN ASM_REWRITE_TAC[];
    MESON_TAC[]]);;

let MOI_SCC_MONO = prove
 (`!(a:real^N) h (psi:real^N->real) lam d y t.
     abs((psi (y + t % d) - (a dot (y + t % d) - h)) -
         (psi y - (a dot y - h))) <= lam * norm(t % d) /\
     lam * norm d < a dot d /\ &0 < t
     ==> psi y < psi (y + t % d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_MUL; DOT_RADD; DOT_RMUL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs t = t` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (lam * norm(d:real^N)) < t * (a dot d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let MOI_SCC_PSI_CONT = prove
 (`!(psi:real^N->real) (a:real^N) h lam s.
     (!x y. x IN s /\ y IN s
            ==> abs((psi x - (a dot x - h)) - (psi y - (a dot y - h))) <=
                lam * norm(x - y))
     ==> (\z. lift(psi z)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
  EXISTS_TAC `norm(a:real^N) + lam` THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^N`; `x - y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC);;

let MOI_SCC_IVT = prove
 (`!(psi:real^N->real) x y.
     (\z. lift(psi z)) continuous_on segment[x,y] /\ psi x <= &0 /\ &0 <= psi y
     ==> ?z. z IN segment[x,y] /\ psi z = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (\z. lift((psi:real^N->real) z)) (segment[x,y])`;
                 `lift((psi:real^N->real) x)`; `lift((psi:real^N->real) y)`;
                 `&0`; `1`] CONNECTED_IVT_COMPONENT) THEN
  ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; CONNECTED_SEGMENT; DIMINDEX_1;
               LE_REFL; GSYM drop; LIFT_DROP] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[EXISTS_IN_IMAGE; LIFT_DROP]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The crossing triangle.  T = conv{v0,v1,v2}, v0 alone below the level  *)
(* h (v1 above, or v1 = p on the level with psi v1 = 0), psi a perturbation *)
(* of the height a dot x - h with Lipschitz constant lam and size below m.  *)
(* The map H x = A + (n.(x - v0) / (r n.(v2 - v0))) (B - A), with A and B   *)
(* the flat zeros on [v0,v1] and [v0,v2], r the parameter of the zero of    *)
(* psi on [v0,v2] and n a normal to v1 - v0 in the plane, is affine, sends  *)
(* the zeros of psi in T injectively to flat zeros in T, keeps relative     *)
(* interior points inside, and keeps zeros on each edge or vertex on it.   *)
(* ------------------------------------------------------------------------- *)

let MOI_SCC_TRI = prove
 (`!(a:real^3) h (psi:real^3->real) v0 v1 v2 lam m D.
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\ ~affine_dependent {v0,v1,v2} /\
     &0 < m /\ &0 <= lam /\
     a dot v0 - h <= --m /\ m <= a dot v2 - h /\
     (m <= a dot v1 - h \/ (a dot v1 = h /\ psi v1 = &0)) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> norm(x - y) <= D) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> abs((psi x - (a dot x - h)) - (psi y - (a dot y - h))) <=
                lam * norm(x - y)) /\
     (!x. x IN convex hull {v0,v1,v2} ==> abs(psi x - (a dot x - h)) < m) /\
     lam * D < m
     ==> ?H. (?l y0. linear l /\ !x. H x = l x + y0) /\
             (!y. y IN convex hull {v0,v1,v2} /\ psi y = &0
                  ==> H y IN convex hull {v0,v1,v2} /\ a dot H y = h) /\
             (!y1 y2. y1 IN convex hull {v0,v1,v2} /\
                      y2 IN convex hull {v0,v1,v2} /\
                      psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2 ==> y1 = y2) /\
             (!y. y IN relative_interior(convex hull {v0,v1,v2}) /\ psi y = &0
                  ==> H y IN relative_interior(convex hull {v0,v1,v2})) /\
             (!x1 x2 y. x1 IN {v0,v1,v2} /\ x2 IN {v0,v1,v2} /\
                        y IN segment[x1,x2] /\ psi y = &0
                        ==> H y IN segment[x1,x2])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "v1") (CONJUNCTS_THEN2 (LABEL_TAC "diam")
   (CONJUNCTS_THEN2 (LABEL_TAC "lip") (CONJUNCTS_THEN2 (LABEL_TAC "small")
    ASSUME_TAC)))))))))))) THEN
  SUBGOAL_THEN
   `v0 IN convex hull {v0:real^3,v1,v2} /\ v1 IN convex hull {v0,v1,v2} /\
    v2 IN convex hull {v0,v1,v2}`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  (* Growth of the height along the two edges at v0. *)
  SUBGOAL_THEN `m <= a dot (v1 - v0:real^3) /\ &2 * m <= a dot (v2 - v0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DOT_RSUB] THEN USE_THEN "v1" MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * norm(v1 - v0:real^3) < a dot (v1 - v0) /\
    lam * norm(v2 - v0:real^3) < a dot (v2 - v0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `lam * norm(v1 - v0:real^3) <= lam * D /\ lam * norm(v2 - v0:real^3) <= lam * D`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `psi(v0:real^3) < &0 /\ &0 < psi v2` STRIP_ASSUME_TAC THENL
   [USE_THEN "small" (MP_TAC o C MATCH_MP
      (ASSUME `v0 IN convex hull {v0:real^3,v1,v2}`)) THEN
    USE_THEN "small" (MP_TAC o C MATCH_MP
      (ASSUME `v2 IN convex hull {v0:real^3,v1,v2}`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Strict monotonicity along d1 = v1 - v0 and d2 = v2 - v0 inside T.    *)
  SUBGOAL_THEN
   `!y t. y IN convex hull {v0:real^3,v1,v2} /\
          y + t % (v1 - v0) IN convex hull {v0,v1,v2} /\ &0 < t
          ==> psi y < psi (y + t % (v1 - v0))`
  (LABEL_TAC "m1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCC_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real^3`; `h:real`; `lam:real`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "lip" (MP_TAC o SPECL [`y + t % (v1 - v0):real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(y + t % d) - y:real^3 = t % d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN convex hull {v0:real^3,v1,v2} /\
          y + t % (v2 - v0) IN convex hull {v0,v1,v2} /\ &0 < t
          ==> psi y < psi (y + t % (v2 - v0))`
  (LABEL_TAC "m2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCC_MONO THEN
    MAP_EVERY EXISTS_TAC [`a:real^3`; `h:real`; `lam:real`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "lip" (MP_TAC o SPECL [`y + t % (v2 - v0):real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(y + t % d) - y:real^3 = t % d`];
    ALL_TAC] THEN
  (* Membership through coordinates. *)
  SUBGOAL_THEN
   `!s1 s2. &0 <= s1 /\ &0 <= s2 /\ s1 + s2 <= &1
            ==> v0 + s1 % (v1 - v0) + s2 % (v2 - v0) IN convex hull {v0:real^3,v1,v2}`
  (LABEL_TAC "mem") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SCC_TRI_COORD] THEN
    MAP_EVERY EXISTS_TAC [`s1:real`; `s2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> v0 + s % (v2 - v0) IN convex hull {v0:real^3,v1,v2}`
  (LABEL_TAC "mem2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "mem" (MP_TAC o SPECL [`&0`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  (* The zero of psi on [v0,v2]. *)
  SUBGOAL_THEN
   `?r. &0 < r /\ r < &1 /\ psi(v0 + r % (v2 - v0):real^3) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`psi:real^3->real`; `v0:real^3`; `v2:real^3`] MOI_SCC_IVT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `convex hull {v0:real^3,v1,v2}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SCC_PSI_CONT THEN
        MAP_EVERY EXISTS_TAC [`a:real^3`; `h:real`; `lam:real`] THEN
        USE_THEN "lip" ACCEPT_TAC;
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `z = (&1 - u) % v0 + u % v2:real^3` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    EXISTS_TAC `u:real` THEN
    REWRITE_TAC[VECTOR_ARITH `v0 + u % (v2 - v0):real^3 = (&1 - u) % v0 + u % v2`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `u = &0` THENL
     [UNDISCH_TAC `psi((&1 - u) % v0 + u % v2:real^3) = &0` THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                      VECTOR_ADD_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `u = &1` THENL
     [UNDISCH_TAC `psi((&1 - u) % v0 + u % v2:real^3) = &0` THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                      VECTOR_ADD_LID] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. r < s /\ s <= &1 ==> &0 < psi(v0 + s % (v2 - v0):real^3)`
  (LABEL_TAC "L1") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "m2" (MP_TAC o SPECL [`v0 + r % (v2 - v0):real^3`; `s - r:real`]) THEN
    REWRITE_TAC[VECTOR_ARITH `(v0 + r % d) + (s - r) % d:real^3 = v0 + s % d`] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "mem2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "mem2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2. &0 < s1 /\ &0 <= s2 /\ s1 + s2 <= &1
            ==> psi(v0 + s2 % (v2 - v0):real^3) <
                psi(v0 + s1 % (v1 - v0) + s2 % (v2 - v0))`
  (LABEL_TAC "L3") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "m1" (MP_TAC o SPECL [`v0 + s2 % (v2 - v0):real^3`; `s1:real`]) THEN
    REWRITE_TAC[VECTOR_ARITH
     `(v0 + s2 % d2) + s1 % d1:real^3 = v0 + s1 % d1 + s2 % d2`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "mem2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2. &0 <= s1 /\ &0 <= s2 /\ s1 + s2 <= &1 /\
            psi(v0 + s1 % (v1 - v0) + s2 % (v2 - v0):real^3) = &0
            ==> s2 <= r /\ (&0 < s1 ==> s2 < r)`
  (LABEL_TAC "s2b") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(r < s2)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "L1" (MP_TAC o SPEC `s2:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `s1 = &0` THENL
       [UNDISCH_TAC `psi(v0 + s1 % (v1 - v0) + s2 % (v2 - v0):real^3) = &0` THEN
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN REAL_ARITH_TAC;
        USE_THEN "L3" (MP_TAC o SPECL [`s1:real`; `s2:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC `s2:real = r` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "L3" (MP_TAC o SPECL [`s1:real`; `r:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* The flat zeros on the two edges at v0. *)
  SUBGOAL_THEN
   `?r1. &0 < r1 /\ r1 <= &1 /\ (a dot v0 - h) + r1 * (a dot (v1 - v0:real^3)) = &0 /\
         (a dot v1 = h ==> r1 = &1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `--(a dot v0 - h) / (a dot (v1 - v0:real^3))` THEN
    SUBGOAL_THEN `&0 < a dot (v1 - v0:real^3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN USE_THEN "v1" MP_TAC THEN
      REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN
      REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r2. &0 < r2 /\ r2 < &1 /\ (a dot v0 - h) + r2 * (a dot (v2 - v0:real^3)) = &0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `--(a dot v0 - h) / (a dot (v2 - v0:real^3))` THEN
    SUBGOAL_THEN `&0 < a dot (v2 - v0:real^3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `v2:real^3`] MOI_SCC_TRI_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?H:real^3->real^3.
      !x. H x = (v0 + r1 % (v1 - v0)) +
                (inv(r * (n dot (v2 - v0))) * (n dot (x - v0))) %
                (r2 % (v2 - v0) - r1 % (v1 - v0))`
  (X_CHOOSE_THEN `H:real^3->real^3` (LABEL_TAC "Hdef")) THENL
   [EXISTS_TAC
     `\x:real^3. (v0 + r1 % (v1 - v0)) +
                 (inv(r * (n dot (v2 - v0))) * (n dot (x - v0))) %
                 (r2 % (v2 - v0) - r1 % (v1 - v0))` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2. H(v0 + s1 % (v1 - v0) + s2 % (v2 - v0)) =
            v0 + ((&1 - s2 / r) * r1) % (v1 - v0) + ((s2 / r) * r2) % (v2 - v0):real^3`
  (LABEL_TAC "Hc") THENL
   [REPEAT GEN_TAC THEN USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_ARITH `(v0 + a % x + b % y) - v0:real^3 = a % x + b % y`] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN
     `inv(r * (n dot (v2 - v0))) * (s2 * (n dot (v2 - v0:real^3))) = s2 / r`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < n dot (v2 - v0:real^3)`] THEN
      CONV_TAC REAL_FIELD;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `H:real^3->real^3` THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC
     `\x:real^3. (inv(r * (n dot (v2 - v0))) * (n dot x)) %
                 (r2 % (v2 - v0) - r1 % (v1 - v0))` THEN
    EXISTS_TAC
     `(v0 + r1 % (v1 - v0)) -
      (inv(r * (n dot (v2 - v0))) * (n dot v0)) %
      (r2 % (v2 - v0) - r1 % (v1 - v0)):real^3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; REAL_ADD_LDISTRIB;
                  VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_AC];
      USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[DOT_RSUB; REAL_SUB_LDISTRIB; VECTOR_SUB_RDISTRIB] THEN
      VECTOR_ARITH_TAC];
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[MOI_SCC_TRI_COORD] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real`
      STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `y = v0 + s1 % (v1 - v0) + s2 % (v2 - v0):real^3` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "s2b" (MP_TAC o SPECL [`s1:real`; `s2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= s2 / r /\ s2 / r <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(&1 - s2 / r) * r1`; `(s2 / r) * r2`] THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(&1 - s2 / r) * r1 <= (&1 - s2 / r) * &1 /\ (s2 / r) * r2 <= (s2 / r) * &1`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (&1 - s2 / r) * r1 /\ &0 <= (s2 / r) * r2` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      MAP_EVERY UNDISCH_TAC
       [`(a dot v0 - h) + r1 * (a dot (v1 - v0:real^3)) = &0`;
        `(a dot v0 - h) + r2 * (a dot (v2 - v0:real^3)) = &0`] THEN
      CONV_TAC REAL_RING];
    MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN
    REWRITE_TAC[MOI_SCC_TRI_COORD] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC))
        STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `y1 = v0 + s1 % (v1 - v0) + s2 % (v2 - v0):real^3` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `y2 = v0 + t1 % (v1 - v0) + t2 % (v2 - v0):real^3` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `s2:real = t2` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. n dot (z - v0)`) THEN
      USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VECTOR_ARITH `(v0 + a % x + b % y) - v0:real^3 = a % x + b % y`] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < r`; `&0 < r2`; `&0 < n dot (v2 - v0:real^3)`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPECL [`s1:real`; `t1:real`] REAL_LT_TOTAL) THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "m1" (MP_TAC o SPECL
       [`v0 + s1 % (v1 - v0) + t2 % (v2 - v0):real^3`; `t1 - s1:real`]) THEN
      REWRITE_TAC[VECTOR_ARITH
       `(v0 + s1 % d1 + t2 % d2) + (t1 - s1) % d1:real^3 = v0 + t1 % d1 + t2 % d2`] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      USE_THEN "m1" (MP_TAC o SPECL
       [`v0 + t1 % (v1 - v0) + t2 % (v2 - v0):real^3`; `s1 - t1:real`]) THEN
      REWRITE_TAC[VECTOR_ARITH
       `(v0 + t1 % d1 + t2 % d2) + (s1 - t1) % d1:real^3 = v0 + s1 % d1 + t2 % d2`] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `y:real^3` THEN
    SUBGOAL_THEN
     `!x:real^3. x IN relative_interior(convex hull {v0,v1,v2}) <=>
                 ?u1 u2 u3. &0 < u1 /\ &0 < u2 /\ &0 < u3 /\ u1 + u2 + u3 = &1 /\
                            x = u1 % v0 + u2 % v1 + u3 % v2`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC MOI_SCC_RELINT_3 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
      (X_CHOOSE_THEN `u3:real` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    SUBGOAL_THEN `y = v0 + u2 % (v1 - v0) + u3 % (v2 - v0):real^3` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `y = u1 % v0 + u2 % v1 + u3 % v2:real^3` THEN
      SUBGOAL_THEN `u1 = &1 - u2 - u3` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "s2b" (MP_TAC o SPECL [`u2:real`; `u3:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < u2`) o CONJUNCT2) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < u3 / r /\ u3 / r < &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (&1 - u3 / r) * r1 - (u3 / r) * r2`; `(&1 - u3 / r) * r1`;
      `(u3 / r) * r2`] THEN
    SUBGOAL_THEN
     `(&1 - u3 / r) * r1 <= (&1 - u3 / r) * &1 /\ (u3 / r) * r2 < (u3 / r) * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - u3 / r) * r1 /\ &0 < (u3 / r) * r2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    (* Zeros on edges and vertices stay there. *)
    SUBGOAL_THEN
     `segment[v0,v1] SUBSET convex hull {v0:real^3,v1,v2} /\
      segment[v0,v2] SUBSET convex hull {v0,v1,v2} /\
      segment[v1,v2] SUBSET convex hull {v0,v1,v2}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN segment[v0,v1] /\ psi y = &0 ==> H y IN segment[v0:real^3,v1]`
    (LABEL_TAC "F01") THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      UNDISCH_TAC `y = (&1 - u) % v0 + u % v1:real^3` THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN
       `(&1 - u) % v0 + u % v1 = v0 + u % (v1 - v0) + &0 % (v2 - v0):real^3`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
      EXISTS_TAC `r1:real` THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_LID] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN segment[v0,v2] /\ psi y = &0 ==> H y IN segment[v0:real^3,v2]`
    (LABEL_TAC "F02") THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      UNDISCH_TAC `y = (&1 - u) % v0 + u % v2:real^3` THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(&1 - u) % v0 + u % v2 = v0 + u % (v2 - v0):real^3`
      SUBST_ALL_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `u:real = r` SUBST_ALL_TAC THENL
       [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPECL [`u:real`; `r:real`] REAL_LT_TOTAL) THENL
         [ASM_REWRITE_TAC[];
          USE_THEN "m2" (MP_TAC o SPECL [`v0 + u % (v2 - v0):real^3`; `r - u:real`]) THEN
          REWRITE_TAC[VECTOR_ARITH `(v0 + u % d) + (r - u) % d:real^3 = v0 + r % d`] THEN
          ANTS_TAC THENL
           [REPEAT CONJ_TAC THENL
             [USE_THEN "mem2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
              USE_THEN "mem2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
              ASM_REAL_ARITH_TAC];
            ASM_REAL_ARITH_TAC];
          USE_THEN "L1" (MP_TAC o SPEC `u:real`) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN `v0 + r % (v2 - v0) = v0 + &0 % (v1 - v0) + r % (v2 - v0):real^3`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_SUB_REFL; REAL_MUL_LZERO;
                   REAL_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
      EXISTS_TAC `r2:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN segment[v1,v2] /\ psi y = &0 ==> y = v1 /\ H y = v1:real^3`
    (LABEL_TAC "Z12") THENL
     [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN convex hull {v0,v1,v2}` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN segment[v1,v2]` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y = v1:real^3 /\ a dot v1 = h`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
       [SUBGOAL_THEN `u = &0 /\ a dot (v1:real^3) = h` STRIP_ASSUME_TAC THENL
         [ALL_TAC;
          ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
        USE_THEN "small" (MP_TAC o C MATCH_MP
          (ASSUME `(y:real^3) IN convex hull {v0,v1,v2}`)) THEN
        USE_THEN "lip" (MP_TAC o C MATCH_MP (CONJ
          (ASSUME `(y:real^3) IN convex hull {v0,v1,v2}`)
          (ASSUME `(v1:real^3) IN convex hull {v0,v1,v2}`))) THEN
        UNDISCH_TAC `psi(y:real^3) = &0` THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `y = (&1 - u) % v1 + u % v2:real^3` THEN
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[VECTOR_ARITH
          `((&1 - u) % v1 + u % v2) - v1:real^3 = u % (v2 - v1)`] THEN
        REWRITE_TAC[NORM_MUL; DOT_RADD; DOT_RMUL] THEN
        SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `norm(v2 - v1:real^3) <= D` ASSUME_TAC THENL
         [USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `u * (lam * norm(v2 - v1:real^3)) <= u * (lam * D)`
        ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `u * m <= u * ((a:real^3) dot v2 - h) /\
                      (m <= a dot v1 - h
                       ==> (&1 - u) * m <= (&1 - u) * (a dot v1 - h)) /\
                      (&0 < u ==> u * (lam * D) < u * m)`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        USE_THEN "v1" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
         [DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `m <= (a:real^3) dot v1 - h`)) THEN
          UNDISCH_TAC `&0 <= u` THEN UNDISCH_TAC `u <= &1` THEN
          UNDISCH_TAC `u * m <= u * ((a:real^3) dot v2 - h)` THEN
          UNDISCH_TAC `m <= (a:real^3) dot v1 - h` THEN
          POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
          FIRST_X_ASSUM(SUBST_ALL_TAC o check
            (fun th -> concl th = `(a:real^3) dot v1 = h`)) THEN
          UNDISCH_TAC `psi(v1:real^3) = &0` THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[REAL_SUB_REFL] THEN
          REPEAT STRIP_TAC THEN
          ASM_CASES_TAC `u = &0` THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `&0 < u` (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_REAL_ARITH_TAC];
       ALL_TAC] THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(H:real^3->real^3) v1 = H(v0 + &1 % (v1 - v0) + &0 % (v2 - v0))`
      SUBST1_TAC THENL [AP_TERM_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "Hc" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `r1 = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `a dot (v1:real^3) = h ==> r1 = &1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_LID] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN segment[v1,v2] /\ psi y = &0 ==> H y IN segment[v1:real^3,v2]`
    (LABEL_TAC "F12") THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "Z12" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[ENDS_IN_SEGMENT]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!y. y IN segment[v0,v0] /\ psi y = &0 ==> H y IN segment[v0:real^3,v0]) /\
      (!y. y IN segment[v1,v1] /\ psi y = &0 ==> H y IN segment[v1:real^3,v1]) /\
      (!y. y IN segment[v2,v2] /\ psi y = &0 ==> H y IN segment[v2:real^3,v2])`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_REFL; IN_SING] THEN REPEAT CONJ_TAC THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THENL
       [UNDISCH_TAC `psi(v0:real^3) < &0` THEN ASM_REWRITE_TAC[REAL_LT_REFL];
        USE_THEN "Z12" (MP_TAC o SPEC `v1:real^3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; SIMP_TAC[]];
        UNDISCH_TAC `&0 < psi(v2:real^3)` THEN ASM_REWRITE_TAC[REAL_LT_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(!y. y IN segment[v1,v0] /\ psi y = &0 ==> H y IN segment[v1:real^3,v0]) /\
      (!y. y IN segment[v2,v0] /\ psi y = &0 ==> H y IN segment[v2:real^3,v0]) /\
      (!y. y IN segment[v2,v1] /\ psi y = &0 ==> H y IN segment[v2:real^3,v1])`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      USE_THEN "F01" (fun th1 -> USE_THEN "F02" (fun th2 -> USE_THEN "F12"
        (fun th3 -> REWRITE_TAC[th1; th2; th3])));
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`; `y:real^3`] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)]);;

(* ------------------------------------------------------------------------- *)
(* 4. Every triangle of a generic complex.  The property moi_scc_good of a  *)
(* map H on a triangle t (affine; zeros of psi in t go injectively to flat  *)
(* zeros in t; relative interior kept; zeros on a segment between two       *)
(* vertices of c in t stay on it), the non-crossing triangles (identity),   *)
(* the mirrored crossing triangle, and the classification of all triangles *)
(* by sorted vertex heights.                                                *)
(* ------------------------------------------------------------------------- *)

let moi_scc_good = new_definition
 `moi_scc_good (c:(real^3->bool)->bool) (a:real^3) (p:real^3)
               (psi:real^3->real) (t:real^3->bool) (H:real^3->real^3) <=>
    (?l y0. linear l /\ !x. H x = l x + y0) /\
    (!y. y IN t /\ psi y = &0 ==> H y IN t /\ a dot H y = a dot p) /\
    (!y1 y2. y1 IN t /\ y2 IN t /\ psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2
             ==> y1 = y2) /\
    (!y. y IN relative_interior t /\ psi y = &0 ==> H y IN relative_interior t) /\
    (!x1 x2 y. {x1} IN c /\ {x2} IN c /\ x1 IN t /\ x2 IN t /\
               y IN segment[x1,x2] /\ psi y = &0 ==> H y IN segment[x1,x2])`;;

let MOI_SCC_NOCROSS = prove
 (`!(a:real^3) h (psi:real^3->real) v0 v1 v2 lam m D.
     &0 < m /\ &0 <= lam /\
     (m <= a dot v0 - h \/ (a dot v0 = h /\ psi v0 = &0)) /\
     m <= a dot v1 - h /\ m <= a dot v2 - h /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> norm(x - y) <= D) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> abs((psi x - (a dot x - h)) - (psi y - (a dot y - h))) <=
                lam * norm(x - y)) /\
     (!x. x IN convex hull {v0,v1,v2} ==> abs(psi x - (a dot x - h)) < m) /\
     lam * D < m
     ==> !y. y IN convex hull {v0,v1,v2} /\ psi y = &0
             ==> y = v0 /\ a dot v0 = h`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "v0") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "diam")
   (CONJUNCTS_THEN2 (LABEL_TAC "lip") (CONJUNCTS_THEN2 (LABEL_TAC "small")
    ASSUME_TAC)))))))) THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `v0 IN convex hull {v0:real^3,v1,v2} /\ v1 IN convex hull {v0,v1,v2} /\
    v2 IN convex hull {v0,v1,v2}`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(v1 - v0:real^3) <= D /\ norm(v2 - v0:real^3) <= D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "small" (MP_TAC o C MATCH_MP
    (ASSUME `(y:real^3) IN convex hull {v0,v1,v2}`)) THEN
  USE_THEN "lip" (MP_TAC o C MATCH_MP (CONJ
    (ASSUME `(y:real^3) IN convex hull {v0,v1,v2}`)
    (ASSUME `(v0:real^3) IN convex hull {v0,v1,v2}`))) THEN
  UNDISCH_TAC `(y:real^3) IN convex hull {v0,v1,v2}` THEN
  REWRITE_TAC[MOI_SCC_TRI_COORD] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `psi(y:real^3) = &0` THEN
  UNDISCH_TAC `y = v0 + s1 % (v1 - v0) + s2 % (v2 - v0):real^3` THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `(v0 + s1 % d1 + s2 % d2) - v0:real^3 = s1 % d1 + s2 % d2`] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB] THEN
  SUBGOAL_THEN
   `norm(s1 % (v1 - v0) + s2 % (v2 - v0):real^3) <= (s1 + s2) * D`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `norm(s1 % (v1 - v0):real^3) + norm(s2 % (v2 - v0):real^3)` THEN
    REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
    SUBGOAL_THEN `abs s1 = s1 /\ abs s2 = s2` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s1 * norm(v1 - v0:real^3) <= s1 * D /\
                  s2 * norm(v2 - v0:real^3) <= s2 * D`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s1 * m <= s1 * ((a:real^3) dot v1 - h) /\ s2 * m <= s2 * (a dot v2 - h) /\
    lam * norm(s1 % (v1 - v0) + s2 % (v2 - v0):real^3) <= lam * ((s1 + s2) * D) /\
    (&0 < s1 + s2 ==> (s1 + s2) * (lam * D) < (s1 + s2) * m) /\
    (m <= a dot v0 - h ==> (&1 - s1 - s2) * m <= (&1 - s1 - s2) * (a dot v0 - h))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "v0" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `m <= (a:real^3) dot v0 - h`)) THEN
    UNDISCH_TAC `s1 * m <= s1 * ((a:real^3) dot v1 - h)` THEN
    UNDISCH_TAC `s2 * m <= s2 * ((a:real^3) dot v2 - h)` THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o check
      (fun th -> concl th = `(a:real^3) dot v0 = h`)) THEN
    UNDISCH_TAC `psi(v0:real^3) = &0` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s1 + s2 = &0` THENL
     [SUBGOAL_THEN `s1 = &0 /\ s2 = &0` (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s1 + s2` (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_SCC_NOCROSS_NEG = prove
 (`!(a:real^3) h (psi:real^3->real) v0 v1 v2 lam m D.
     &0 < m /\ &0 <= lam /\
     (a dot v0 - h <= --m \/ (a dot v0 = h /\ psi v0 = &0)) /\
     a dot v1 - h <= --m /\ a dot v2 - h <= --m /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> norm(x - y) <= D) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> abs((psi x - (a dot x - h)) - (psi y - (a dot y - h))) <=
                lam * norm(x - y)) /\
     (!x. x IN convex hull {v0,v1,v2} ==> abs(psi x - (a dot x - h)) < m) /\
     lam * D < m
     ==> !y. y IN convex hull {v0,v1,v2} /\ psi y = &0
             ==> y = v0 /\ a dot v0 = h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^3`; `--h:real`; `\x:real^3. --(psi x:real)`;
                 `v0:real^3`; `v1:real^3`; `v2:real^3`;
                 `lam:real`; `m:real`; `D:real`] MOI_SCC_NOCROSS) THEN
  REWRITE_TAC[DOT_LNEG; REAL_NEG_EQ_0; REAL_EQ_NEG2] THEN
  REWRITE_TAC[REAL_ARITH `--x - (--y - --z) = --(x - (y - z))`;
              REAL_ARITH `--x - --y = --(x - y)`; REAL_ABS_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SCC_TRI_NEG = prove
 (`!(a:real^3) h (psi:real^3->real) v0 v1 v2 lam m D.
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\ ~affine_dependent {v0,v1,v2} /\
     &0 < m /\ &0 <= lam /\
     m <= a dot v0 - h /\ a dot v2 - h <= --m /\
     (a dot v1 - h <= --m \/ (a dot v1 = h /\ psi v1 = &0)) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> norm(x - y) <= D) /\
     (!x y. x IN convex hull {v0,v1,v2} /\ y IN convex hull {v0,v1,v2}
            ==> abs((psi x - (a dot x - h)) - (psi y - (a dot y - h))) <=
                lam * norm(x - y)) /\
     (!x. x IN convex hull {v0,v1,v2} ==> abs(psi x - (a dot x - h)) < m) /\
     lam * D < m
     ==> ?H. (?l y0. linear l /\ !x. H x = l x + y0) /\
             (!y. y IN convex hull {v0,v1,v2} /\ psi y = &0
                  ==> H y IN convex hull {v0,v1,v2} /\ a dot H y = h) /\
             (!y1 y2. y1 IN convex hull {v0,v1,v2} /\
                      y2 IN convex hull {v0,v1,v2} /\
                      psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2 ==> y1 = y2) /\
             (!y. y IN relative_interior(convex hull {v0,v1,v2}) /\ psi y = &0
                  ==> H y IN relative_interior(convex hull {v0,v1,v2})) /\
             (!x1 x2 y. x1 IN {v0,v1,v2} /\ x2 IN {v0,v1,v2} /\
                        y IN segment[x1,x2] /\ psi y = &0
                        ==> H y IN segment[x1,x2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`--a:real^3`; `--h:real`; `\x:real^3. --(psi x:real)`;
                 `v0:real^3`; `v1:real^3`; `v2:real^3`;
                 `lam:real`; `m:real`; `D:real`] MOI_SCC_TRI) THEN
  REWRITE_TAC[DOT_LNEG; REAL_NEG_EQ_0; REAL_EQ_NEG2] THEN
  REWRITE_TAC[REAL_ARITH `--x - (--y - --z) = --(x - (y - z))`;
              REAL_ARITH `--x - --y = --(x - y)`; REAL_ABS_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SCC_SORT3 = prove
 (`!(a:real^3) A B C.
     ~(a dot A = a dot B) /\ ~(a dot A = a dot C) /\ ~(a dot B = a dot C)
     ==> ?x0 x1 x2. {x0,x1,x2} = {A,B,C} /\
                    a dot x0 < a dot x1 /\ a dot x1 < a dot x2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(a:real^3) dot A < a dot B` THEN
  ASM_CASES_TAC `(a:real^3) dot B < a dot C` THEN
  ASM_CASES_TAC `(a:real^3) dot A < a dot C` THEN
  FIRST (map (fun l -> MAP_EVERY EXISTS_TAC l THEN CONJ_TAC THENL
                        [SET_TAC[]; ASM_REAL_ARITH_TAC])
    [[`A:real^3`; `B:real^3`; `C:real^3`]; [`A:real^3`; `C:real^3`; `B:real^3`];
     [`B:real^3`; `A:real^3`; `C:real^3`]; [`B:real^3`; `C:real^3`; `A:real^3`];
     [`C:real^3`; `A:real^3`; `B:real^3`]; [`C:real^3`; `B:real^3`; `A:real^3`]]));;

let MOI_SCC_VERTEX_IN_HULL = prove
 (`!c t (S:real^N->bool) x.
     simplicial_complex c /\ t IN c /\ {x} IN c /\ x IN t /\
     ~affine_dependent S /\ t = convex hull S
     ==> x IN S`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N} face_of t` MP_TAC THENL
   [SUBGOAL_THEN `{x:real^N} = {x} INTER t` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_SCC_ID_GOOD = prove
 (`!c (a:real^3) p (psi:real^3->real) t v0.
     aff_dim t = &2 /\ v0 extreme_point_of t /\
     (!y. y IN t /\ psi y = &0 ==> y = v0 /\ a dot v0 = a dot p)
     ==> moi_scc_good c a p psi t (\x. x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_scc_good] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `vec 0:real^3`] THEN
    REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID];
    ASM_MESON_TAC[];
    MESON_TAC[];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = v0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^3->bool`; `v0:real^3`]
      EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(t:real^3->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    MESON_TAC[]]);;

let MOI_SCC_TRI_TRANSLATE = prove
 (`!c (a:real^3) p (psi:real^3->real) H v0 v1 v2.
     simplicial_complex c /\ convex hull {v0,v1,v2} IN c /\
     ~affine_dependent {v0,v1,v2} /\
     (?l y0. linear l /\ !x. H x = l x + y0) /\
     (!y. y IN convex hull {v0,v1,v2} /\ psi y = &0
          ==> H y IN convex hull {v0,v1,v2} /\ a dot H y = a dot p) /\
     (!y1 y2. y1 IN convex hull {v0,v1,v2} /\ y2 IN convex hull {v0,v1,v2} /\
              psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2 ==> y1 = y2) /\
     (!y. y IN relative_interior(convex hull {v0,v1,v2}) /\ psi y = &0
          ==> H y IN relative_interior(convex hull {v0,v1,v2})) /\
     (!x1 x2 y. x1 IN {v0,v1,v2} /\ x2 IN {v0,v1,v2} /\
                y IN segment[x1,x2] /\ psi y = &0 ==> H y IN segment[x1,x2])
     ==> moi_scc_good c a p psi (convex hull {v0,v1,v2}) H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_scc_good] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_SCC_VERTEX_IN_HULL THEN
  MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `convex hull {v0:real^3,v1,v2}`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SCC_TRI_ANY = prove
 (`!c (a:real^3) p (psi:real^3->real) lam m D t.
     moi_sch3_generic c a /\ t IN c /\ aff_dim t = &2 /\ {p} IN c /\ psi p = &0 /\
     &0 < m /\ &0 <= lam /\
     (!v. {v} IN c /\ ~(v = p) ==> m <= abs(a dot v - a dot p)) /\
     (!x y. x IN t /\ y IN t ==> norm(x - y) <= D) /\
     (!x y. x IN t /\ y IN t
            ==> abs((psi x - (a dot x - a dot p)) - (psi y - (a dot y - a dot p))) <=
                lam * norm(x - y)) /\
     (!x. x IN t ==> abs(psi x - (a dot x - a dot p)) < m) /\
     lam * D < m
     ==> ?H. moi_scc_good c a p psi t H`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mb")
   STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "gen" (fun th -> MESON_TAC[th; moi_sch3_generic]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w. {v} IN c /\ {w} IN c /\ (a:real^3) dot v = a dot w ==> v = w`
  (LABEL_TAC "inj") THENL
   [USE_THEN "gen" (fun th -> MESON_TAC[th; moi_sch3_generic]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. {v} IN c
        ==> (a:real^3) dot v = a dot p \/ m <= a dot v - a dot p \/
            a dot v - a dot p <= --m`
  (LABEL_TAC "sides") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `v:real^3 = p` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mb" (MP_TAC o SPEC `v:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (t:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` ASSUME_TAC) THEN
    SUBGOAL_THEN `n:int = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^3->bool` MOI_STL_TRIANGLE_CORNERS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3` (X_CHOOSE_THEN `B:real^3`
    (X_CHOOSE_THEN `C:real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> is_eq(concl th) && lhs(concl th) = `t:real^3->bool`)) THEN
  SUBGOAL_THEN `{A:real^3} IN c /\ {B} IN c /\ {C} IN c` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN
    EXISTS_TAC `convex hull {A:real^3,B,C}` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((a:real^3) dot A = a dot B) /\ ~(a dot A = a dot C) /\ ~(a dot B = a dot C)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `A:real^3`; `B:real^3`; `C:real^3`] MOI_SCC_SORT3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `x1:real^3`
    (X_CHOOSE_THEN `x2:real^3`
      (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `{x0:real^3} IN c /\ {x1} IN c /\ {x2} IN c` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_SLV_SC_VERTEX_SING THEN
    EXISTS_TAC `convex hull {x0:real^3,x1,x2}` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x0:real^3 = x1) /\ ~(x0 = x2) /\ ~(x1 = x2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {x2,x1,x0} = convex hull {x0:real^3,x1,x2} /\
                ~affine_dependent {x2:real^3,x1,x0}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{x2,x1,x0} = {x0:real^3,x1,x2}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sides" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `{x0:real^3} IN c`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `{x1:real^3} IN c`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `{x2:real^3} IN c`))) THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `(a:real^3) dot p <= a dot x0` THENL
   [EXISTS_TAC `\x:real^3. x` THEN MATCH_MP_TAC MOI_SCC_ID_GOOD THEN
    EXISTS_TAC `x0:real^3` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT] THEN
    MATCH_MP_TAC MOI_SCC_NOCROSS THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `m:real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(a:real^3) dot x0 = a dot p` THENL
     [SUBGOAL_THEN `x0:real^3 = p` SUBST_ALL_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^3) dot x2 <= a dot p` THENL
   [EXISTS_TAC `\x:real^3. x` THEN MATCH_MP_TAC MOI_SCC_ID_GOOD THEN
    EXISTS_TAC `x2:real^3` THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT] THEN
    REWRITE_TAC[GSYM(ASSUME
      `convex hull {x2,x1,x0} = convex hull {x0:real^3,x1,x2}`)] THEN
    MATCH_MP_TAC MOI_SCC_NOCROSS_NEG THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `m:real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(a:real^3) dot x2 = a dot p` THENL
     [SUBGOAL_THEN `x2:real^3 = p` SUBST_ALL_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^3) dot x1 < a dot p` THENL
   [MP_TAC(ISPECL [`a:real^3`; `(a:real^3) dot p`; `psi:real^3->real`;
                   `x2:real^3`; `x1:real^3`; `x0:real^3`;
                   `lam:real`; `m:real`; `D:real`] MOI_SCC_TRI_NEG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` ASSUME_TAC) THEN
    EXISTS_TAC `H:real^3->real^3` THEN
    REWRITE_TAC[GSYM(ASSUME
      `convex hull {x2,x1,x0} = convex hull {x0:real^3,x1,x2}`)] THEN
    MATCH_MP_TAC MOI_SCC_TRI_TRANSLATE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `(a:real^3) dot p`; `psi:real^3->real`;
                 `x0:real^3`; `x1:real^3`; `x2:real^3`;
                 `lam:real`; `m:real`; `D:real`] MOI_SCC_TRI) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_CASES_TAC `(a:real^3) dot x1 = a dot p` THENL
     [SUBGOAL_THEN `x1:real^3 = p` SUBST_ALL_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` ASSUME_TAC) THEN
  EXISTS_TAC `H:real^3->real^3` THEN
  MATCH_MP_TAC MOI_SCC_TRI_TRANSLATE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. Gluing the triangle maps.  Carriers (the simplex whose relative       *)
(* interior contains a point), consistency of the triangle maps on shared   *)
(* edges and vertices, and the glued map H on the zero set of psi: PL,      *)
(* injective, into the flat level set, and H y IN e ==> y IN e for every    *)
(* simplex e of c.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SCC_RESTRICT1 = prove
 (`!(t:real^N->bool) s (P:real^N->bool).
     t SUBSET s /\ (!x. x IN s ==> P x) ==> (!x. x IN t ==> P x)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let MOI_SCC_RESTRICT2 = prove
 (`!(t:real^N->bool) s (P:real^N->real^N->bool).
     t SUBSET s /\ (!x y. x IN s /\ y IN s ==> P x y)
     ==> (!x y. x IN t /\ y IN t ==> P x y)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

let MOI_SCC_CARRIER = prove
 (`!c (y:real^N).
     simplicial_complex c /\ y IN UNIONS c
     ==> ?f. f IN c /\ y IN relative_interior f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_FEU_UNIONS_RELATIVE_INTERIORS th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_SCC_SAME_DIM = prove
 (`!c f (t:real^N->bool).
     simplicial_complex c /\ f IN c /\ t IN c /\ f SUBSET t /\
     aff_dim f = aff_dim t
     ==> f = t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
  SUBGOAL_THEN `(f:real^N->bool) face_of t` ASSUME_TAC THENL
   [SUBGOAL_THEN `f:real^N->bool = f INTER t` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `f:real^N->bool = t` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_SIMP_TAC[INT_LT_REFL]);;

let MOI_SCC_LOW_DIM = prove
 (`!c (f:real^N->bool).
     simplicial_complex c /\ f IN c /\ ~(f = {}) /\ aff_dim f <= &1
     ==> ?u w. {u} IN c /\ {w} IN c /\ f = segment[u,w]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(f:real^N->bool) = &0 \/ aff_dim f = &1` MP_TAC THENL
   [MP_TAC(ISPEC `f:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `v:real^N`] THEN
    ASM_REWRITE_TAC[SEGMENT_REFL];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`] MOI_SLV_EDGE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let MOI_SCC_SEG_UNIQUE = prove
 (`!c (a:real^3) u w x y.
     moi_sch3_generic c a /\ {u} IN c /\ {w} IN c /\
     x IN segment[u,w] /\ y IN segment[u,w] /\ a dot x = a dot y
     ==> x = y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u:real^3 = w` THENL
   [UNDISCH_TAC `(x:real^3) IN segment[u,w]` THEN
    UNDISCH_TAC `(y:real^3) IN segment[u,w]` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_STL_SEGMENT_LEVEL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `u:real^3`; `w:real^3`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(u:real^3 = w)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_sch3_generic c (a:real^3)` THEN REWRITE_TAC[moi_sch3_generic] THEN
  ASM_MESON_TAC[]);;

let MOI_SCC_NO_ZERO_AT_P = prove
 (`!(a:real^3) p (psi:real^3->real) w lam m D y.
     psi p = &0 /\ m <= abs(a dot w - a dot p) /\ &0 < m /\ &0 <= lam /\
     norm(w - p) <= D /\ lam * D < m /\
     abs((psi y - (a dot y - a dot p)) - (psi p - (a dot p - a dot p))) <=
     lam * norm(y - p) /\
     y IN segment(p,w)
     ==> ~(psi y = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `abs((psi y - (a dot y - a dot p)) - (psi p - (a dot p - a dot p))) <=
    lam * norm(y - p:real^3)` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((&1 - u) % p + u % w) - p:real^3 = u % (w - p)`] THEN
  REWRITE_TAC[NORM_MUL; DOT_RADD; DOT_RMUL] THEN
  SUBGOAL_THEN `abs u = u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u * m <= u * abs((a:real^3) dot w - a dot p) /\
                u * (lam * norm(w - p:real^3)) <= u * (lam * D) /\
                u * (lam * D) < u * m`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `u * abs((a:real^3) dot w - a dot p) =
                abs((&1 - u) * (a dot p) + u * (a dot w) - a dot p)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(&1 - u) * ap + u * aw - ap:real = u * (aw - ap)`; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < u ==> abs u = u`];
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let MOI_SCC_CONS = prove
 (`!c (a:real^3) p (psi:real^3->real) HT.
     moi_sch3_generic c a /\
     (!t. t IN c /\ aff_dim t = &2 ==> moi_scc_good c a p psi t (HT t))
     ==> !t1 t2 y. t1 IN c /\ aff_dim t1 = &2 /\ t2 IN c /\ aff_dim t2 = &2 /\
                   y IN t1 /\ y IN t2 /\ psi y = &0
                   ==> HT t1 y = HT t2 y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HT")) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_SCC_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t1:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(f:real^3->bool) SUBSET t1 /\ f SUBSET t2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN f` ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN f` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(f:real^3->bool) = &2` THENL
   [SUBGOAL_THEN `f:real^3->bool = t1 /\ f = t2`
    (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_SCC_SAME_DIM THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(f:real^3->bool) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->bool`; `t1:real^3->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `f:real^3->bool`] MOI_SCC_LOW_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(u:real^3) IN t1 /\ w IN t1 /\ u IN t2 /\ w IN t2 /\ y IN segment[u,w]`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^3->bool) SUBSET t1` THEN
    UNDISCH_TAC `(f:real^3->bool) SUBSET t2` THEN
    UNDISCH_TAC `(y:real^3) IN f` THEN
    UNDISCH_TAC `f = segment[u:real^3,w]` THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`u:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t1:real^3->bool) IN c`)
    (ASSUME `aff_dim(t1:real^3->bool) = &2`))) THEN
  USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t2:real^3->bool) IN c`)
    (ASSUME `aff_dim(t2:real^3->bool) = &2`))) THEN
  REWRITE_TAC[moi_scc_good] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "i2")
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "s2"))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "i1")
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "s1"))))) THEN
  MATCH_MP_TAC MOI_SCC_SEG_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `u:real^3`; `w:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "s1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "s2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "i1" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN t1`)
      (ASSUME `psi(y:real^3) = &0`))) THEN
    USE_THEN "i2" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN t2`)
      (ASSUME `psi(y:real^3) = &0`))) THEN
    SIMP_TAC[]]);;

let MOI_SCC_GLUE = prove
 (`!c (a:real^3) p (psi:real^3->real) HT.
     moi_sch3_generic c a /\ {p} IN c /\
     (!s. s IN c /\ ~(s = {}) ==> ?t. t IN c /\ aff_dim t = &2 /\ s SUBSET t) /\
     (!t. t IN c /\ aff_dim t = &2 ==> moi_scc_good c a p psi t (HT t)) /\
     (!w y. {w} IN c /\ ~(w = p) /\ segment[p,w] IN c /\ y IN segment(p,w)
            ==> ~(psi y = &0)) /\
     pl_polyhedron {y | y IN UNIONS c /\ psi y = &0}
     ==> ?H. pl_map_on {y | y IN UNIONS c /\ psi y = &0} H /\
             (!y. y IN UNIONS c /\ psi y = &0
                  ==> H y IN UNIONS c /\ a dot H y = a dot p) /\
             (!y1 y2. y1 IN UNIONS c /\ y2 IN UNIONS c /\
                      psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2 ==> y1 = y2) /\
             (!y e. y IN UNIONS c /\ psi y = &0 /\ e IN c /\ H y IN e ==> y IN e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "pure") (CONJUNCTS_THEN2 (LABEL_TAC "HT")
   (CONJUNCTS_THEN2 (LABEL_TAC "noedge") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "gen" (fun th -> MESON_TAC[th; moi_sch3_generic]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w. {v} IN c /\ {w} IN c /\ (a:real^3) dot v = a dot w ==> v = w`
  (LABEL_TAC "inj") THENL
   [USE_THEN "gen" (fun th -> MESON_TAC[th; moi_sch3_generic]); ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
                 `psi:real^3->real`; `HT:(real^3->bool)->real^3->real^3`]
    MOI_SCC_CONS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "gen" ACCEPT_TAC; USE_THEN "HT" ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "cons")] THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS c ==> ?t. t IN c /\ aff_dim t = &2 /\ (y:real^3) IN t`
  (LABEL_TAC "tri") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "pure" (MP_TAC o SPEC `s:real^3->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      MESON_TAC[SUBSET; ASSUME `(y:real^3) IN s`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?H:real^3->real^3. !y. H y = (HT:(real^3->bool)->real^3->real^3)
                                 (@t. t IN c /\ aff_dim t = &2 /\ y IN t) y`
  (X_CHOOSE_THEN `H:real^3->real^3` (LABEL_TAC "Hdef")) THENL
   [EXISTS_TAC `\y:real^3. (HT:(real^3->bool)->real^3->real^3)
                             (@t. t IN c /\ aff_dim t = &2 /\ y IN t) y` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. t IN c /\ aff_dim t = &2 /\ y IN t /\ psi y = &0
          ==> H y = (HT:(real^3->bool)->real^3->real^3) t y`
  (LABEL_TAC "Heq") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "Hdef" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `(@t. t IN c /\ aff_dim t = &2 /\ (y:real^3) IN t) IN c /\
      aff_dim (@t. t IN c /\ aff_dim t = &2 /\ (y:real^3) IN t) = &2 /\
      y IN (@t. t IN c /\ aff_dim t = &2 /\ (y:real^3) IN t)`
    STRIP_ASSUME_TAC THENL
     [CONV_TAC SELECT_CONV THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cons" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "Hdef" (K ALL_TAC) THEN
  (* H y lies in the relative interior of the carrier of y. *)
  SUBGOAL_THEN
   `!y f. y IN UNIONS c /\ psi y = &0 /\ f IN c /\ y IN relative_interior f
          ==> (H:real^3->real^3) y IN relative_interior f`
  (LABEL_TAC "relint") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN f` ASSUME_TAC THENL
     [MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "pure" (MP_TAC o SPEC `f:real^3->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN f` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
     [UNDISCH_TAC `(f:real^3->bool) SUBSET t` THEN
      UNDISCH_TAC `(y:real^3) IN f` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(H:real^3->real^3) y = HT (t:real^3->bool) y` SUBST1_TAC THENL
     [USE_THEN "Heq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t:real^3->bool) IN c`)
      (ASSUME `aff_dim(t:real^3->bool) = &2`))) THEN
    REWRITE_TAC[moi_scc_good] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "gi")
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "gr")
      (LABEL_TAC "gs"))))) THEN
    ASM_CASES_TAC `aff_dim(f:real^3->bool) = &2` THENL
     [SUBGOAL_THEN `f:real^3->bool = t` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_SCC_SAME_DIM THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "gr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(f:real^3->bool) <= &1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`f:real^3->bool`; `t:real^3->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `f:real^3->bool`] MOI_SCC_LOW_DIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN f` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `w:real^3`
        STRIP_ASSUME_TAC))] THEN
    SUBGOAL_THEN `(u:real^3) IN t /\ w IN t /\ y IN segment[u,w]`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f:real^3->bool) SUBSET t` THEN
      UNDISCH_TAC `(y:real^3) IN f` THEN
      UNDISCH_TAC `f = segment[u:real^3,w]` THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`u:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(HT:(real^3->bool)->real^3->real^3) t y IN segment[u,w] /\
      (a:real^3) dot HT t y = a dot p`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "gs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "gi" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN t`)
          (ASSUME `psi(y:real^3) = &0`))) THEN SIMP_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `f = segment[u:real^3,w]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_CASES_TAC `u:real^3 = w` THENL
     [UNDISCH_TAC `u:real^3 = w` THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(HT:(real^3->bool)->real^3->real^3) t y IN segment[w,w]` THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT; SEGMENT_REFL] THEN SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior(segment[u,w])` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN DISCH_TAC THEN
    ASM_CASES_TAC `u:real^3 = p` THENL
     [UNDISCH_TAC `u:real^3 = p` THEN DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "noedge" (MP_TAC o SPECL [`w:real^3`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(p:real^3 = w)` THEN
        CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `w:real^3 = p` THENL
     [UNDISCH_TAC `w:real^3 = p` THEN DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "noedge" (MP_TAC o SPECL [`u:real^3`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM; CONJUNCT2 SEGMENT_SYM] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(a:real^3) dot HT (t:real^3->bool) (y:real^3) = a dot p` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(u:real^3 = p)`; UNDISCH_TAC `~(w:real^3 = p)`] THEN
    REWRITE_TAC[] THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `H:real^3->real^3` THEN REPEAT CONJ_TAC THENL
   [(* PL by pasting the affine pieces. *)
    SUBGOAL_THEN
     `{y | y IN UNIONS c /\ psi y = &0} =
      UNIONS {{y:real^3 | y IN t /\ psi y = &0} | t IN c /\ aff_dim t = &2}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET] THEN CONJ_TAC THEN
      X_GEN_TAC `y:real^3` THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "tri" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN UNIONS c`)) THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `{y:real^3 | y IN t /\ psi y = &0}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_SCC_PL_MAP_ON_UNIONS_FINITE THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{t:real^3->bool | t IN c /\ P t} = {t | t IN c /\ P t}`] THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{y:real^3 | y IN t /\ psi y = &0} =
      t INTER {y | y IN UNIONS c /\ psi y = &0}`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) IN c` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `pl_polyhedron {y:real^3 | y IN t /\ psi y = &0}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_POLYHEDRON_INTER THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t:real^3->bool) IN c`)
      (ASSUME `aff_dim(t:real^3->bool) = &2`))) THEN
    REWRITE_TAC[moi_scc_good] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `y0:real^3`
      STRIP_ASSUME_TAC) o CONJUNCT1) THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. (l:real^3->real^3) x + y0` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(H:real^3->real^3) x = HT (t:real^3->bool) x` SUBST1_TAC THENL
       [USE_THEN "Heq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]];
    (* Into the flat level set. *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "tri" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN UNIONS c`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(H:real^3->real^3) y = HT (t:real^3->bool) y` SUBST1_TAC THENL
     [USE_THEN "Heq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t:real^3->bool) IN c`)
      (ASSUME `aff_dim(t:real^3->bool) = &2`))) THEN
    REWRITE_TAC[moi_scc_good] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN t`)
      (ASSUME `psi(y:real^3) = &0`)) o CONJUNCT1 o CONJUNCT2) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    (* Injective. *)
    MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y1:real^3`] MOI_SCC_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y2:real^3`] MOI_SCC_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f2:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(H:real^3->real^3) y1 IN relative_interior f1 /\
      (H:real^3->real^3) y2 IN relative_interior f2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "relint" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `f1:real^3->bool = f2` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THENL
       [EXISTS_TAC `(H:real^3->real^3) y1`; EXISTS_TAC `(H:real^3->real^3) y2`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `f1:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `f2:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(H:real^3->real^3) y1 IN relative_interior f1` THEN
      UNDISCH_TAC `(H:real^3->real^3) y2 IN relative_interior f2` THEN
      UNDISCH_TAC `(H:real^3->real^3) y1 = H y2` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^3) IN f2 /\ (y2:real^3) IN f2` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `f2:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y1:real^3) IN relative_interior f2` THEN
      UNDISCH_TAC `(y2:real^3) IN relative_interior f2` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "pure" (MP_TAC o SPEC `f2:real^3->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y1:real^3) IN f2` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(y1:real^3) IN t /\ (y2:real^3) IN t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(f2:real^3->bool) SUBSET t` THEN
      UNDISCH_TAC `(y1:real^3) IN f2` THEN UNDISCH_TAC `(y2:real^3) IN f2` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "HT" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(t:real^3->bool) IN c`)
      (ASSUME `aff_dim(t:real^3->bool) = &2`))) THEN
    REWRITE_TAC[moi_scc_good] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(H:real^3->real^3) y1 = HT (t:real^3->bool) y1 /\
                  (H:real^3->real^3) y2 = HT (t:real^3->bool) y2`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
     [CONJ_TAC THEN USE_THEN "Heq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    (* Membership in simplices is reflected. *)
    MAP_EVERY X_GEN_TAC [`y:real^3`; `e:real^3->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_SCC_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^3->bool) SUBSET e` MP_TAC THENL
     [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `(H:real^3->real^3) y`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "relint" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN SET_TAC[]]);;

(* The perturbation lemma: a Lipschitz perturbation psi of the flat height  *)
(* on a generically triangulated PL 2-sphere, vanishing at the vertex p and *)
(* smaller than the vertex gap m, has a zero set that maps PL and           *)
(* injectively into the flat level set of p, reflecting simplices.          *)

let MOI_SCC_PERTURB = prove
 (`!c (a:real^3) p (psi:real^3->real) lam m D.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\ psi p = &0 /\
     &0 < m /\ &0 <= lam /\
     (!v. {v} IN c /\ ~(v = p) ==> m <= abs(a dot v - a dot p)) /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(x - y) <= D) /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c
            ==> abs((psi x - (a dot x - a dot p)) - (psi y - (a dot y - a dot p))) <=
                lam * norm(x - y)) /\
     lam * D < m /\
     pl_polyhedron {y | y IN UNIONS c /\ psi y = &0}
     ==> ?H. pl_map_on {y | y IN UNIONS c /\ psi y = &0} H /\
             (!y. y IN UNIONS c /\ psi y = &0
                  ==> H y IN UNIONS c /\ a dot H y = a dot p) /\
             (!y1 y2. y1 IN UNIONS c /\ y2 IN UNIONS c /\
                      psi y1 = &0 /\ psi y2 = &0 /\ H y1 = H y2 ==> y1 = y2) /\
             (!y e. y IN UNIONS c /\ psi y = &0 /\ e IN c /\ H y IN e ==> y IN e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "mb") (CONJUNCTS_THEN2 (LABEL_TAC "diam")
   (CONJUNCTS_THEN2 (LABEL_TAC "lip") (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "gen" (fun th -> MESON_TAC[th; moi_sch3_generic]); ALL_TAC] THEN
  MP_TAC(ISPEC `(:3)` MOI_SMO_SURFACE_COMPLEX) THEN
  REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "pure") (K ALL_TAC))) THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS c ==> abs(psi x - ((a:real^3) dot x - a dot p)) < m`
  (LABEL_TAC "small") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "lip" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN UNIONS c`)
      (ASSUME `(p:real^3) IN UNIONS c`))) THEN
    USE_THEN "diam" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN UNIONS c`)
      (ASSUME `(p:real^3) IN UNIONS c`))) THEN
    REWRITE_TAC[ASSUME `psi(p:real^3) = &0`; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `lam * norm(x - p:real^3) <= lam * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lam * D < m` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?HT. !t. t IN c /\ aff_dim t = &2
             ==> moi_scc_good c a p psi t ((HT:(real^3->bool)->real^3->real^3) t)`
  (X_CHOOSE_TAC `HT:(real^3->bool)->real^3->real^3`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCC_TRI_ANY THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `m:real`; `D:real`] THEN
    SUBGOAL_THEN `(t:real^3->bool) SUBSET UNIONS c` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) IN c` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCC_RESTRICT2 THEN EXISTS_TAC `UNIONS c:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SCC_RESTRICT2 THEN EXISTS_TAC `UNIONS c:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SCC_RESTRICT1 THEN EXISTS_TAC `UNIONS c:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCC_GLUE THEN
  EXISTS_TAC `HT:(real^3->bool)->real^3->real^3` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`w:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN UNIONS c /\ (y:real^3) IN UNIONS c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:real^3`; `w:real^3`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
    MP_TAC(ISPECL [`p:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[p:real^3,w] IN c` THEN
    UNDISCH_TAC `(y:real^3) IN segment(p,w)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCC_NO_ZERO_AT_P THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^3`; `p:real^3`; `w:real^3`; `lam:real`; `m:real`; `D:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "mb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "lip" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN UNIONS c`)
      (ASSUME `(p:real^3) IN UNIONS c`))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Tools for the application: the tilt leaves the triangle t except at  *)
(* q, zeros of the perturbed height on an edge are near the flat zero, the *)
(* escape argument with the side clause, the abstract polygon count, a     *)
(* crossing edge with its flat zero on a given level polygon, the Lipschitz *)
(* and diameter bounds on the sphere and the vertex gap.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SCC_CONE_BOUND = prove
 (`!A B C (q:real^3) (b:real^3) mt.
     &0 <= mt /\
     (!V. V IN {A,B,C} ==> mt * norm(V - q) <= b dot (V - q))
     ==> !x. x IN convex hull {A,B,C} ==> mt * norm(x - q) <= b dot (x - q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(u % A + v % B + w % C) - q:real^3 = u % (A - q) + v % (B - q) + w % (C - q)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `u = &1 - v - w` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  TRANS_TAC REAL_LE_TRANS
   `mt * (norm(u % (A - q:real^3)) + norm(v % (B - q:real^3)) +
          norm(w % (C - q:real^3)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x + y + z:real^3) <= norm x + norm(y + z) /\
      norm(y + z) <= norm y + norm z
      ==> norm(x + y + z) <= norm x + norm y + norm z`) THEN
    REWRITE_TAC[NORM_TRIANGLE];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `abs u = u /\ abs v = v /\ abs w = w`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `u * (mt * norm(A - q:real^3)) <= u * (b dot (A - q)) /\
    v * (mt * norm(B - q:real^3)) <= v * (b dot (B - q)) /\
    w * (mt * norm(C - q:real^3)) <= w * (b dot (C - q))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let MOI_SCC_TILT_TRIANGLE = prove
 (`!t (q:real^3) (b:real^3).
     &2 simplex t /\ (!x. x IN t /\ ~(x = q) ==> &0 < b dot (x - q))
     ==> ?mt. &0 < mt /\ !x. x IN t ==> mt * norm(x - q) <= b dot (x - q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^3->bool` MOI_STL_TRIANGLE_CORNERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3` (X_CHOOSE_THEN `B:real^3`
    (X_CHOOSE_THEN `C:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`{V:real^3 | V IN {A,B,C} /\ ~(V = q)}`;
                 `\V:real^3. (b dot (V - q)) / norm(V - q)`] MOI_SCC_POS_LB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    X_GEN_TAC `V:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mt:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mt:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SCC_CONE_BOUND THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  X_GEN_TAC `V:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `V:real^3 = q` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; DOT_RZERO; REAL_MUL_RZERO;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `V:real^3`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `&0 < norm(V - q:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let MOI_SCC_TILT_MISS = prove
 (`!t (q:real^3) (a:real^3) (b:real^3) a1 sigma eta e mt.
     (!x. x IN t ==> a dot x = a dot q) /\
     (!x. x IN t ==> mt * norm(x - q) <= b dot (x - q)) /\
     (sigma = &1 \/ sigma = -- &1) /\ &0 < eta /\ e <= mt /\
     norm(a1 - (a + (sigma * eta) % b)) < e * eta
     ==> !x. x IN t /\ a1 dot x = a1 dot q ==> x = q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev") (CONJUNCTS_THEN2 (LABEL_TAC "cone")
   (CONJUNCTS_THEN2 (LABEL_TAC "sg") STRIP_ASSUME_TAC))) THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = q` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(x - q:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `?dl:real^3. a1 = a + (sigma * eta) % b + dl /\ norm dl < e * eta`
  (X_CHOOSE_THEN `dl:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
   [EXISTS_TAC `a1 - (a + (sigma * eta) % b):real^3` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a + (sigma * eta) % b + dl) dot (x - q:real^3) = &0` MP_TAC THENL
   [REWRITE_TAC[DOT_RSUB; REAL_SUB_0] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `dl:real^3`)) (concl th)));
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN
  SUBGOAL_THEN `(a:real^3) dot (x - q) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[DOT_RSUB; REAL_SUB_0] THEN USE_THEN "lev" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((dl:real^3) dot (x - q)) < (e * eta) * norm(x - q:real^3)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LET_TRANS `norm(dl:real^3) * norm(x - q:real^3)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e * eta) * norm(x - q:real^3) <= eta * (b dot (x - q))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `eta * (mt * norm(x - q:real^3))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(e * eta) * n = eta * (e * n):real`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      USE_THEN "cone" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sg" (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  UNDISCH_TAC `abs((dl:real^3) dot (x - q)) < (e * eta) * norm(x - q:real^3)` THEN
  UNDISCH_TAC `(e * eta) * norm(x - q:real^3) <= eta * (b dot (x - q))` THEN
  REAL_ARITH_TAC);;

let MOI_SCC_EDGE_NEAR = prove
 (`!(a:real^3) w1 w2 u y X.
     a dot w1 < a dot w2 /\ u IN segment[w1,w2] /\ y IN segment[w1,w2] /\
     abs(a dot y - a dot u) <= X
     ==> norm(y - u) <= (X * norm(w2 - w1)) / (a dot (w2 - w1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) MP_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((&1 - r) % w1 + r % w2) - ((&1 - s) % w1 + s % w2):real^3 =
    (r - s) % (w2 - w1)`] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; NORM_MUL] THEN
  SUBGOAL_THEN `&0 < (a:real^3) dot (w2 - w1)` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 - r) * (a dot w1) + r * (a dot w2)) - ((&1 - s) * (a dot w1) + s * (a dot w2)) =
    (r - s) * ((a:real^3) dot (w2 - w1))`
  SUBST1_TAC THENL [REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(abs d * n) * ad = (abs d * ad) * n:real`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let MOI_SCC_ESCAPE = prove
 (`!(a:real^3) (b:real^3) (wv:real^3) (dl:real^3) sigma eta e
    (fy:real^3) (fu:real^3) (q:real^3) h r rr.
     (sigma = &1 \/ sigma = -- &1) /\ &0 < eta /\ norm dl <= e * eta /\
     wv = (sigma * eta) % b + dl /\
     a dot fy - h = --(wv dot (fy - q)) /\
     norm(fy - fu) <= rr /\ rr < r /\
     (dist(fu,fy) < r ==> &0 <= sigma * (a dot fy - h)) /\
     norm(b) * rr + e * (norm(fu - q) + rr) < b dot (fu - q)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sg") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dist(fu:real^3,fy) < r` ASSUME_TAC THENL
   [REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `dist(fu:real^3,fy) < r`)) THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `abs((dl:real^3) dot (fy - q)) <= (e * eta) * (norm(fu - q:real^3) + rr)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `norm(dl:real^3) * norm(fy - q:real^3)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(NORM_ARITH `norm(fy - q:real^3) <= norm(fu - q) + norm(fy - fu)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3) dot (fu - q) - norm(b) * rr <= b dot (fy - q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:real^3`; `fy - fu:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    SUBGOAL_THEN `norm(b:real^3) * norm(fy - fu:real^3) <= norm b * rr` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eta * (e * (norm(fu - q:real^3) + rr)) < eta * ((b:real^3) dot (fy - q))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LTE_TRANS `eta * ((b:real^3) dot (fu - q) - norm(b) * rr)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sg" (DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REAL_ARITH_TAC);;

let MOI_SCC_COUNT = prove
 (`!(Z:real^3->bool) (L:real^3->bool) (Phi:real^3->real^3) j0 u.
     pl_polyhedron Z /\ pl_map_on Z Phi /\
     (!x y. x IN Z /\ y IN Z /\ Phi x = Phi y ==> x = y) /\
     IMAGE Phi Z SUBSET L /\ FINITE {P | pl_sphere 1 P /\ P SUBSET L} /\
     pl_sphere 1 j0 /\ j0 SUBSET L /\ u IN j0 /\ ~(u IN IMAGE Phi Z)
     ==> CARD {P | pl_sphere 1 P /\ P SUBSET Z} + 1 <=
         CARD {P | pl_sphere 1 P /\ P SUBSET L}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "IL")
    STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`Z:real^3->bool`; `Phi:real^3->real^3`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real^3->real^3`) THEN
  SUBGOAL_THEN
   `{P | pl_sphere 1 P /\ P SUBSET IMAGE (Phi:real^3->real^3) Z} SUBSET
    ({P | pl_sphere 1 P /\ P SUBSET L} DELETE (j0:real^3->bool))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `~((u:real^3) IN IMAGE (Phi:real^3->real^3) Z)` THEN
    UNDISCH_TAC `(u:real^3) IN j0` THEN USE_THEN "IL" MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (Phi:real^3->real^3) Z`; `Z:real^3->bool`;
                 `G:real^3->real^3`; `Phi:real^3->real^3`] MOI_SLV_HOMEO_POLYGONS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{P | pl_sphere 1 P /\ P SUBSET (L:real^3->bool)} DELETE j0` THEN
    ASM_REWRITE_TAC[FINITE_DELETE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`j0:real^3->bool`; `{P | pl_sphere 1 P /\ P SUBSET (L:real^3->bool)}`]
    CARD_DELETE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{P | pl_sphere 1 P /\ P SUBSET IMAGE (Phi:real^3->real^3) Z}`;
                 `{P | pl_sphere 1 P /\ P SUBSET L} DELETE (j0:real^3->bool)`]
    CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN
  SUBGOAL_THEN `~(CARD {P | pl_sphere 1 P /\ P SUBSET (L:real^3->bool)} = 0)`
  MP_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `j0:real^3->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ARITH_TAC]);;

let MOI_SCC_CIRCLE_SOME_EDGE = prove
 (`!K (j0:real^N->bool).
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     pl_sphere 1 j0 /\ j0 SUBSET UNIONS K
     ==> ?u1 u2. ~(u1 = u2) /\ {u1} IN K /\ {u2} IN K /\
                 segment[u1,u2] SUBSET j0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `j0:real^N->bool`] MOI_SLV_CIRCLE_EDGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(j0:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC[EMPTY_UNIONS; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `E:real^N->bool`] MOI_SLV_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N`; `u2:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_SCC_POLYGON_EDGE = prove
 (`!c (a:real^3) p j0.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     j0 IN moi_sch3_level_polygons (UNIONS c) a (a dot p)
     ==> ?w1 w2 u. segment[w1,w2] IN c /\ a dot w1 < a dot p /\ a dot p < a dot w2 /\
                   u IN segment[w1,w2] /\ a dot u = a dot p /\ u IN j0 /\ ~(u = p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `(a:real^3) dot p`]
    MOI_SLV_LEVEL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `j0 IN moi_sch3_level_polygons (UNIONS c) (a:real^3) (a dot p)` THEN
  REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{s INTER {x:real^3 | a dot x = a dot p} | s IN c}`;
                 `j0:real^3->bool`] MOI_SCC_CIRCLE_SOME_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?u. {u} IN {s INTER {x:real^3 | a dot x = a dot p} | s IN c} /\
        u IN j0 /\ ~(u = p)`
  (X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `(u1:real^3) IN j0 /\ (u2:real^3) IN j0` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`u1:real^3`; `u2:real^3`] ENDS_IN_SEGMENT) THEN
      UNDISCH_TAC `segment[u1:real^3,u2] SUBSET j0` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `u1:real^3 = p` THENL
     [EXISTS_TAC `u2:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u1:real^3 = u2)` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      EXISTS_TAC `u1:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`; `s:real^3->bool`;
                 `u:real^3`] MOI_SLV_LEVEL_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`; `u:real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`w1:real^3`; `w2:real^3`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
    UNDISCH_TAC `(u:real^3) IN segment(w1,w2)` THEN SET_TAC[];
    UNDISCH_TAC `{u:real^3} = s INTER {x | a dot x = a dot p}` THEN SET_TAC[]]);;

let MOI_SCC_SPHERE_BOUNDS = prove
 (`!c (f:real^3->real^3).
     simplicial_complex c /\ pl_map_on (:real^3) f
     ==> ?M D. &0 <= M /\ &0 <= D /\
               (!x y. x IN UNIONS c /\ y IN UNIONS c
                      ==> norm(f x - f y) <= M * norm(x - y)) /\
               (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(x - y) <= D)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(UNIONS c:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL o
    MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `lo:real^3` (X_CHOOSE_TAC `hi:real^3`)) THEN
  MP_TAC(ISPECL [`interval[lo:real^3,hi]`; `f:real^3->real^3`]
    MOI_SCC_PL_LIPSCHITZ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[POLYTOPE_INTERVAL] THEN MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS] o
    MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`M:real`; `&2 * B`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(NORM_ARITH `norm(x - y:real^3) <= norm x + norm y`) THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_SCC_VERTEX_GAP = prove
 (`!c (a:real^3) p.
     moi_sch3_generic c a /\ {p} IN c
     ==> ?m. &0 < m /\ !v. {v} IN c /\ ~(v = p) ==> m <= abs(a dot v - a dot p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN c /\ ~(v = p)}`;
                 `\v:real^3. abs((a:real^3) dot v - a dot p)`] MOI_SCC_POS_LB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN c}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC MOI_SLV_VERTICES_FINITE THEN
      UNDISCH_TAC `moi_sch3_generic c (a:real^3)` THEN
      SIMP_TAC[moi_sch3_generic; simplicial_complex];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(v:real^3 = p)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_sch3_generic c (a:real^3)` THEN
      REWRITE_TAC[moi_sch3_generic] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. The tilted level of the cap, towards CAP_COUNT.                       *)
(* ------------------------------------------------------------------------- *)

(* Basic facts on a level-preserving PL homeomorphism of real^3.             *)

let MOI_SCC_PLH_FACTS = prove
 (`!(f:real^3->real^3) g (a:real^3).
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x)
     ==> (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
         pl_map_on (:real^3) f /\ pl_map_on (:real^3) g /\
         (!x. a dot g x = a dot x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "lev")) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. (f:real^3->real^3)((g:real^3->real^3) y) = y` (LABEL_TAC "fg") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN
  TRANS_TAC EQ_TRANS `(a:real^3) dot (f:real^3->real^3)((g:real^3->real^3) x)` THEN
  CONJ_TAC THENL
   [USE_THEN "lev" (fun th -> REWRITE_TAC[th]);
    USE_THEN "fg" (fun th -> REWRITE_TAC[th])]);;

(* The zero set of the tilted height pulled back to UNIONS c, and the map H *)
(* of the perturbation lemma for it.                                        *)

let MOI_SCC_TILT_MAP = prove
 (`!c (a:real^3) p (f:real^3->real^3) g a1 M D m.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     &0 < m /\ (!v. {v} IN c /\ ~(v = p) ==> m <= abs(a dot v - a dot p)) /\
     &0 <= M /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(f x - f y) <= M * norm(x - y)) /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(x - y) <= D) /\
     norm(a1 - a) * M * D < m
     ==> ?H. pl_map_on {y | y IN UNIONS c /\ a1 dot (f y - f p) = &0} H /\
             (!y. y IN UNIONS c /\ a1 dot (f y - f p) = &0
                  ==> H y IN UNIONS c /\ a dot H y = a dot p) /\
             (!y1 y2. y1 IN UNIONS c /\ y2 IN UNIONS c /\
                      a1 dot (f y1 - f p) = &0 /\ a1 dot (f y2 - f p) = &0 /\
                      H y1 = H y2 ==> y1 = y2) /\
             (!y e. y IN UNIONS c /\ a1 dot (f y - f p) = &0 /\ e IN c /\ H y IN e
                    ==> y IN e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "lipf") (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `a:real^3`]
    MOI_SCC_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
                 `\y:real^3. (a1:real^3) dot (f y - f p)`;
                 `norm(a1 - a:real^3) * M`; `m:real`; `D:real`] MOI_SCC_PERTURB) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `((a1:real^3) dot (f x - f p) - (a dot x - a dot p)) -
      (a1 dot ((f:real^3->real^3) y - f p) - (a dot y - a dot p)) =
      (a1 - a) dot (f x - f y)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `(a:real^3) dot x = a dot f x /\ a dot y = a dot f y /\
                    a dot p = a dot f p`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `norm(a1 - a:real^3) * norm((f:real^3->real^3) x - f y)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "lipf" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    SUBGOAL_THEN
     `{y | y IN UNIONS c /\ (a1:real^3) dot (f y - f p) = &0} =
      IMAGE (g:real^3->real^3)
        (IMAGE f (UNIONS c) INTER {x | a1 dot x = a1 dot f p})`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER; DOT_RSUB;
                  REAL_SUB_0] THEN
      X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `(f:real^3->real^3) y` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)
           ASSUME_TAC))) THEN
        UNDISCH_TAC `(a1:real^3) dot x = a1 dot (f:real^3->real^3) p` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pl_polyhedron(UNIONS c:real^3->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SLV_SC_BASIC) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    SUBGOAL_THEN
     `pl_polyhedron (IMAGE (f:real^3->real^3) (UNIONS c) INTER
                     {x | (a1:real^3) dot x = a1 dot f p})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SCC_POLYHEDRON_HYPERPLANE THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN ASM_REWRITE_TAC[]]]);;

(* The flat zero u on the crossing edge is not hit: its preimage would be  *)
(* a zero of the tilted height on the edge near u whose image under f lies *)
(* in d near f u, against the side clause.                                  *)

let MOI_SCC_NOT_HIT = prove
 (`!c (a:real^3) p (f:real^3->real^3) g (d:real^3->bool) (b:real^3) sigma
    a1 eta e M D w1 w2 u r (H:real^3->real^3).
     (!x. g(f x) = x) /\ (!y. f(g y) = y) /\ (!x. a dot f x = a dot x) /\
     d SUBSET IMAGE f (UNIONS c) /\ p IN UNIONS c /\
     (sigma = &1 \/ sigma = -- &1) /\
     &0 <= M /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(f x - f y) <= M * norm(x - y)) /\
     &0 <= D /\ (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(x - y) <= D) /\
     segment[w1,w2] IN c /\ a dot w1 < a dot w2 /\ u IN segment[w1,w2] /\
     a dot u = a dot p /\
     (!y. y IN d /\ dist(f u,y) < r ==> &0 <= sigma * (a dot y - a dot p)) /\
     &0 < eta /\ &0 < e /\ e <= &1 /\ norm(a1 - (a + (sigma * eta) % b)) < e * eta /\
     norm(a1 - a) <= e * (norm b + &1) /\
     e * ((norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) < r /\
     e * (norm b * ((norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) +
          norm(f u - f p) +
          (norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) <
     b dot (f u - f p) /\
     (!y e'. y IN UNIONS c /\ a1 dot (f y - f p) = &0 /\ e' IN c /\ H y IN e'
             ==> y IN e')
     ==> ~(u IN IMAGE (H o g) (d INTER {x | a1 dot x = a1 dot f p}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gf") (CONJUNCTS_THEN2 (LABEL_TAC "fg")
   (CONJUNCTS_THEN2 (LABEL_TAC "lev") (CONJUNCTS_THEN2 (LABEL_TAC "dsub")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sg")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lipf")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "diam")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "side") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "refl"))))))))))))))))))))))) THEN
  REWRITE_TAC[IN_IMAGE; o_THM; IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (LABEL_TAC "uz")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?y. y IN UNIONS c /\ z = (f:real^3->real^3) y` STRIP_ASSUME_TAC THENL
   [USE_THEN "dsub" MP_TAC THEN UNDISCH_TAC `(z:real^3) IN d` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) z = y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "gf" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^3->real^3) y = u` ASSUME_TAC THENL
   [USE_THEN "uz" MP_TAC THEN
    UNDISCH_TAC `(g:real^3->real^3) z = y` THEN
    DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "uz" (K ALL_TAC) THEN
  SUBGOAL_THEN `(a1:real^3) dot ((f:real^3->real^3) y - f p) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(a1:real^3) dot z = a1 dot (f:real^3->real^3) p` THEN
    ASM_REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN segment[w1,w2]` ASSUME_TAC THENL
   [USE_THEN "refl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN UNIONS c /\ (y:real^3) IN UNIONS c` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[w1:real^3,w2]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The height of y is within |a1 - a| M D of the level. *)
  SUBGOAL_THEN
   `abs((a:real^3) dot y - a dot u) <= norm(a1 - a:real^3) * M * D`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(a:real^3) dot y - a dot u = --((a1 - a) dot ((f:real^3->real^3) y - f p))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(a1:real^3) dot ((f:real^3->real^3) y - f p) = &0` THEN
      USE_THEN "lev" (fun th -> REWRITE_TAC[DOT_LSUB; DOT_RSUB; th]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN
    TRANS_TAC REAL_LE_TRANS
     `norm(a1 - a:real^3) * norm((f:real^3->real^3) y - f p)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    TRANS_TAC REAL_LE_TRANS `M * norm(y - p:real^3)` THEN CONJ_TAC THENL
     [USE_THEN "lipf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "diam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `w1:real^3`; `w2:real^3`; `u:real^3`; `y:real^3`;
                 `norm(a1 - a:real^3) * M * D`] MOI_SCC_EDGE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= norm(w2 - w1:real^3) / ((a:real^3) dot (w2 - w1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE; DOT_RSUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `KE = norm(w2 - w1:real^3) / ((a:real^3) dot (w2 - w1))` THEN
  SUBGOAL_THEN
   `norm((f:real^3->real^3) y - f u) <=
    norm(a1 - a:real^3) * (M * (M * (D * KE)))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `M * norm(y - u:real^3)` THEN CONJ_TAC THENL
     [USE_THEN "lipf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `M * ((norm(a1 - a:real^3) * M * D) * KE)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `norm(y - u:real^3) <=
        ((norm(a1 - a:real^3) * M * D) * norm(w2 - w1:real^3)) /
        ((a:real^3) dot (w2 - w1))` THEN
      EXPAND_TAC "KE" THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * (M * (D * KE))` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]); ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(a1 - a:real^3) * (M * (M * (D * KE))) <=
    e * ((norm(b:real^3) + &1) * (M * (M * (D * KE))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `w * X <= (e * B) * X ==> w * X <= e * (B * X)`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`a:real^3`; `b:real^3`; `a1 - a:real^3`; `a1 - (a + (sigma * eta) % b):real^3`;
    `sigma:real`; `eta:real`; `e:real`; `(f:real^3->real^3) y`;
    `(f:real^3->real^3) u`; `(f:real^3->real^3) p`; `(a:real^3) dot p`; `r:real`;
    `norm(a1 - a:real^3) * (M * (M * (D * KE)))`] MOI_SCC_ESCAPE) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "sg" ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    VECTOR_ARITH_TAC;
    UNDISCH_TAC `(a1:real^3) dot ((f:real^3->real^3) y - f p) = &0` THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN
    USE_THEN "lev" (fun th -> REWRITE_TAC[th]) THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN USE_THEN "side" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^3) IN d` THEN ASM_REWRITE_TAC[];
    ABBREV_TAC `RR = (norm(b:real^3) + &1) * (M * (M * (D * KE)))` THEN
    SUBGOAL_THEN `&0 <= RR` ASSUME_TAC THENL
     [EXPAND_TAC "RR" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `b:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `rr = norm(a1 - a:real^3) * (M * (M * (D * KE)))` THEN
    SUBGOAL_THEN `norm(b:real^3) * rr <= norm b * (e * RR)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `e * RR <= &1 * RR` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `e * (norm((f:real^3->real^3) u - f p) + rr) <= e * (norm(f u - f p) + RR)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `e * (norm(b:real^3) * RR + norm((f:real^3->real^3) u - f p) + RR) <
      b dot (f u - f p)` THEN
    UNDISCH_TAC `norm(b:real^3) * rr <= norm b * (e * RR)` THEN
    UNDISCH_TAC
     `e * (norm((f:real^3->real^3) u - f p) + rr) <= e * (norm(f u - f p) + RR)` THEN
    REAL_ARITH_TAC]);;

(* The count for one admissible tilt a1 = a + sigma eta b + small, given    *)
(* the constants of the construction.                                       *)

let MOI_SCC_TILT_COUNT = prove
 (`!c (a:real^3) p (f:real^3->real^3) g (t:real^3->bool) (d:real^3->bool)
    (b:real^3) sigma a1 eta e M D m mt w1 w2 u r.
     moi_sch3_generic c a /\ pl_sphere 2 (UNIONS c) /\ {p} IN c /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ (!x. a dot f x = a dot x) /\
     &2 simplex t /\ t SUBSET {x | a dot x = a dot p} /\
     IMAGE f (UNIONS c) INTER t = relative_frontier t /\
     d SUBSET IMAGE f (UNIONS c) /\ pl_polyhedron d /\ f p IN d /\
     (sigma = &1 \/ sigma = -- &1) /\
     &0 < m /\ (!v. {v} IN c /\ ~(v = p) ==> m <= abs(a dot v - a dot p)) /\
     &0 <= M /\
     (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(f x - f y) <= M * norm(x - y)) /\
     &0 <= D /\ (!x y. x IN UNIONS c /\ y IN UNIONS c ==> norm(x - y) <= D) /\
     (!x. x IN t ==> mt * norm(x - f p) <= b dot (x - f p)) /\
     segment[w1,w2] IN c /\ a dot w1 < a dot w2 /\
     u IN segment[w1,w2] /\ a dot u = a dot p /\ u IN IMAGE g (relative_frontier t) /\
     (!y. y IN d /\ dist(f u,y) < r ==> &0 <= sigma * (a dot y - a dot p)) /\
     &0 < eta /\ eta < e /\ &0 < e /\ e <= &1 /\ e <= mt /\
     norm(a1 - (a + (sigma * eta) % b)) < e * eta /\
     e * ((norm b + &1) * M * D) < m /\
     e * ((norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) < r /\
     e * (norm b * ((norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) +
          norm(f u - f p) +
          (norm b + &1) * (M * (M * (D * (norm(w2 - w1) / (a dot (w2 - w1))))))) <
     b dot (f u - f p)
     ==> CARD (moi_sch3_level_polygons (d UNION t) a1 (a1 dot f p)) + 1 <=
         CARD (moi_sch3_level_polygons (UNIONS c) a (a dot p))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `a:real^3`]
    MOI_SCC_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(a1 - a:real^3) <= e * (norm(b:real^3) + &1)` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `norm(a1 - (a + (sigma * eta) % b):real^3) + norm((sigma * eta) % b:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC(NORM_ARITH
       `!x y z:real^3. norm(x - y) <= norm(x - (y + z)) + norm(z)`);
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs sigma = &1 /\ abs eta = eta` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * norm(b:real^3) <= e * norm b /\ e * eta <= e`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a1 - a:real^3) * M * D < m` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!w X e B m:real. w * X <= (e * B) * X /\ e * (B * X) < m ==> w * X < m`) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `norm(b:real^3) + &1`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
                 `f:real^3->real^3`; `g:real^3->real^3`; `a1:real^3`;
                 `M:real`; `D:real`; `m:real`] MOI_SCC_TILT_MAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Hin")
      (CONJUNCTS_THEN2 (LABEL_TAC "Hinj") (LABEL_TAC "Hrefl"))))) THEN
  SUBGOAL_THEN `(f:real^3->real^3) p IN relative_frontier t ==> f p IN d`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_sch3_level_polygons] THEN
  (* The cap meets the tilted plane only in d. *)
  SUBGOAL_THEN
   `(d UNION t) INTER {x | (a1:real^3) dot x = a1 dot (f:real^3->real^3) p} =
    d INTER {x | a1 dot x = a1 dot f p}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`t:real^3->bool`; `(f:real^3->real^3) p`; `a:real^3`; `b:real^3`;
                   `a1:real^3`; `sigma:real`; `eta:real`; `e:real`; `mt:real`]
      MOI_SCC_TILT_MISS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `t SUBSET {x:real^3 | a dot x = a dot p}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(f:real^3->real^3) p IN d` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCC_COUNT THEN
  MAP_EVERY EXISTS_TAC
   [`(H:real^3->real^3) o (g:real^3->real^3)`;
    `IMAGE (g:real^3->real^3) (relative_frontier t)`; `u:real^3`] THEN
  SUBGOAL_THEN
   `!z. z IN d /\ (a1:real^3) dot z = a1 dot (f:real^3->real^3) p
        ==> (g:real^3->real^3) z IN UNIONS c /\ a1 dot (f (g z) - f p) = &0`
  (LABEL_TAC "gz") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_0] THEN
    UNDISCH_TAC `(z:real^3) IN d` THEN
    UNDISCH_TAC `d SUBSET IMAGE (f:real^3->real^3) (UNIONS c)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (d INTER {x | (a1:real^3) dot x = a1 dot (f:real^3->real^3) p})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCC_POLYHEDRON_HYPERPLANE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `{y | y IN UNIONS c /\ (a1:real^3) dot ((f:real^3->real^3) y - f p) = &0}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_PL_MAP_ON_POLYHEDRON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "gz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    USE_THEN "gz" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN d`)
      (ASSUME `(a1:real^3) dot x = a1 dot (f:real^3->real^3) p`))) THEN
    USE_THEN "gz" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN d`)
      (ASSUME `(a1:real^3) dot y = a1 dot (f:real^3->real^3) p`))) THEN
    SUBGOAL_THEN `(g:real^3->real^3) x = g y` MP_TAC THENL
     [USE_THEN "Hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `f:real^3->real^3`) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "gz" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `(z:real^3) IN d`)
      (ASSUME `(a1:real^3) dot z = a1 dot (f:real^3->real^3) p`))) THEN
    USE_THEN "Hin" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `(g:real^3->real^3) z IN UNIONS c`)
      (ASSUME `(a1:real^3) dot ((f:real^3->real^3) ((g:real^3->real^3) z) - f p) = &0`))) THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM];
    REWRITE_TAC[GSYM MOI_SLV_LEVEL_POLYGONS_EQ] THEN
    MATCH_MP_TAC LEVEL_POLYGONS_FINITE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_STL_SPHERE_IMAGE THEN EXISTS_TAC `f:real^3->real^3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c) INTER t` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t SUBSET {x:real^3 | a dot x = a dot p}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x = (f:real^3->real^3) y` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SCC_NOT_HIT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `a:real^3`; `b:real^3`;
                          `sigma:real`; `eta:real`; `e:real`;
                          `M:real`; `D:real`; `w1:real^3`; `w2:real^3`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The main theorem CAP_COUNT (the statement MOI_STL_CAP_COUNT).         *)
(* ------------------------------------------------------------------------- *)

let MOI_SCC_CELL_BOUNDARY_SUBSET = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `h1:real^N->real^N`
    (X_CHOOSE_THEN `h2:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (h1:real^N->real^N) k = d` THEN SET_TAC[]);;

let CAP_COUNT = prove
 (MOI_STL_CAP_COUNT,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_sch3_generic]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `a:real^3`]
    MOI_SCC_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (d:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCC_CELL_BOUNDARY_SUBSET THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_STL_CELL_POLYHEDRON THEN
    MAP_EVERY EXISTS_TAC [`2`; `relative_frontier t:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) p IN d` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^3->real^3) p IN d UNION t` MP_TAC THENL
     [UNDISCH_TAC `UNIONS c1 = d UNION (t:real^3->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{(f:real^3->real^3) p}` THEN ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:real^3->real^3) p IN relative_frontier t` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (UNIONS c) INTER t = relative_frontier t` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `relative_frontier t SUBSET (d:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* Constants of the construction. *)
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `f:real^3->real^3`] MOI_SCC_SPHERE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`] MOI_SCC_VERTEX_GAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `IMAGE (g:real^3->real^3) (relative_frontier t) IN
    moi_sch3_level_polygons (UNIONS c) a (a dot p)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SLV_LEVEL_POLYGONS_EQ; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_STL_SPHERE_IMAGE THEN EXISTS_TAC `f:real^3->real^3` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`];
        ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN IMAGE (f:real^3->real^3) (UNIONS c) INTER t`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t SUBSET {x:real^3 | a dot x = a dot p}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x = (f:real^3->real^3) y` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`; `p:real^3`;
                 `IMAGE (g:real^3->real^3) (relative_frontier t)`]
    MOI_SCC_POLYGON_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3`
    (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `(f:real^3->real^3) u IN relative_frontier t /\ ~(f u = f p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN IMAGE (g:real^3->real^3) (relative_frontier t)` THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `g:real^3->real^3`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!x. x IN relative_frontier t /\ ~(x = (f:real^3->real^3) p)
        ==> ?r. &0 < r /\
                !y. y IN d /\ dist(x,y) < r
                    ==> &0 <= sigma * ((a:real^3) dot y - a dot p)` THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^3->real^3) u`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (b:real^3) dot ((f:real^3->real^3) u - f p)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `!x. x IN t /\ ~(x = (f:real^3->real^3) p) ==> &0 < (b:real^3) dot (x - f p)` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `relative_frontier t SUBSET (t:real^3->bool)` THEN
    UNDISCH_TAC `(f:real^3->real^3) u IN relative_frontier t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `(f:real^3->real^3) p`; `b:real^3`]
    MOI_SCC_TILT_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `mt:real` STRIP_ASSUME_TAC) THEN
  (* The choice of e. *)
  MP_TAC(ISPECL [`(norm(b:real^3) + &1) * M * D`; `m:real`] MOI_SCC_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1"))) THEN
  MP_TAC(ISPECL
   [`(norm(b:real^3) + &1) *
     (M * (M * (D * (norm(w2 - w1:real^3) / ((a:real^3) dot (w2 - w1))))))`;
    `r:real`] MOI_SCC_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s2"))) THEN
  MP_TAC(ISPECL
   [`norm(b:real^3) * ((norm(b:real^3) + &1) *
       (M * (M * (D * (norm(w2 - w1:real^3) / ((a:real^3) dot (w2 - w1))))))) +
     norm((f:real^3->real^3) u - f p) +
     (norm(b:real^3) + &1) *
       (M * (M * (D * (norm(w2 - w1:real^3) / ((a:real^3) dot (w2 - w1))))))`;
    `(b:real^3) dot ((f:real^3->real^3) u - f p)`] MOI_SCC_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s3"))) THEN
  EXISTS_TAC `min (&1) (min mt (min e1 (min e2 e3)))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a1:real^3`; `eta:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < min (&1) (min mt (min e1 (min e2 e3))) /\
    min (&1) (min mt (min e1 (min e2 e3))) <= &1 /\
    min (&1) (min mt (min e1 (min e2 e3))) <= mt /\
    min (&1) (min mt (min e1 (min e2 e3))) <= e1 /\
    min (&1) (min mt (min e1 (min e2 e3))) <= e2 /\
    min (&1) (min mt (min e1 (min e2 e3))) <= e3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCC_TILT_COUNT THEN
  MAP_EVERY EXISTS_TAC
   [`g:real^3->real^3`; `b:real^3`; `sigma:real`; `eta:real`;
    `min (&1) (min mt (min e1 (min e2 e3)))`; `M:real`; `D:real`; `m:real`;
    `mt:real`; `w1:real^3`; `w2:real^3`; `u:real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    USE_THEN "s1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "s2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "s3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

