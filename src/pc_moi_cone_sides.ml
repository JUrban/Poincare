prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_cone_sides: the Jordan curve theorem on a round 2-sphere of        *)
(* real^3, and the two local sides of a cone over a simple closed curve on   *)
(* a small sphere.  The file loads only the HOL Light library; it is used by *)
(* pc_moi_s32_sides and pc_moi_fnd_sptrace.                                  *)
(*   SPHERE_JORDAN  a curve c on sphere(q,r) homeomorphic to the circle     *)
(*                  splits the sphere into two connected nonempty disjoint   *)
(*                  pieces, each with c in its closure;                      *)
(*   CONE_SIDES     if y meets ball(q,r) exactly in the cone from q over c, *)
(*                  then ball(q,r) DIFF y is the union of two disjoint       *)
(*                  connected nonempty sets, each with the cone in its       *)
(*                  closure.                                                 *)
(* Route: a punctured sphere is homeomorphic to real^2 (library); the plane *)
(* Jordan curve theorem there (JORDAN_INSIDE_OUTSIDE_GEN); the outside      *)
(* together with the puncture is connected (the outside is unbounded); the  *)
(* open cones over the two pieces are the two sides.                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The Jordan curve theorem on a round 2-sphere of real^3, and the two    *)
(* sides of a cone over a simple closed curve on a small sphere.             *)
(* ------------------------------------------------------------------------- *)

let MOI_CSD_PUNCTURED_SPHERE_R2 = prove
 (`!(q:real^3) r p.
     &0 < r /\ p IN sphere(q,r)
     ==> ?(f:real^3->real^2) g.
           homeomorphism (sphere(q,r) DELETE p,(:real^2)) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `p:real^3`; `(:real^2)`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE) THEN
  ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2; DIMINDEX_3] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[homeomorphic]);;

let MOI_CSD_IMAGE_DISJ = prove
 (`!(g:real^2->real^3) s t p.
     (!y. ~(g y = p)) /\ (!y1 y2. g y1 = g y2 ==> y1 = y2) /\ DISJOINT s t
     ==> DISJOINT (IMAGE g s) (p INSERT IMAGE g t)`,
  SET_TAC[]);;

let MOI_CSD_IMAGE_COMPL = prove
 (`!(f:real^3->real^2) (g:real^2->real^3) s c.
     (!x. x IN s ==> g(f x) = x) /\ (!y. f(g y) = y) /\ IMAGE g (:real^2) = s /\
     c SUBSET s
     ==> IMAGE g ((:real^2) DIFF IMAGE f c) = s DIFF c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    STRIP_TAC THEN EXISTS_TAC `(f:real^3->real^2) x` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let MOI_CSD_SPHERE_JORDAN = prove
 (`!(q:real^3) r (c:real^3->bool).
     &0 < r /\ c SUBSET sphere(q,r) /\ c homeomorphic sphere(vec 0:real^2,&1)
     ==> ?o1 o2. connected o1 /\ connected o2 /\ ~(o1 = {}) /\ ~(o2 = {}) /\
                 DISJOINT o1 o2 /\ o1 UNION o2 = sphere(q,r) DIFF c /\
                 c SUBSET closure o1 /\ c SUBSET closure o2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^3. p IN sphere(q,r) /\ ~(p IN c)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(c:real^3->bool) SUBSET s /\ ~(c = s) ==> ?p. p IN s /\ ~(p IN c)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(c:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ; DIMINDEX_2; DIMINDEX_3; ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `p:real^3`] MOI_CSD_PUNCTURED_SPHERE_R2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^2` (X_CHOOSE_TAC `g:real^2->real^3`)) THEN
  ABBREV_TAC `d = IMAGE (f:real^3->real^2) c` THEN
  SUBGOAL_THEN `(d:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`d:real^2->bool`; `c:real^3->bool`;
                          `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^2`; `g:real^2->real^3`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`sphere(q:real^3,r) DELETE p`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (sphere(q:real^3,r) DELETE p,(:real^2))
                 ((f:real^3->real^2),(g:real^2->real^3))` THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. ~((g:real^2->real^3) y = p) /\ g y IN sphere(q,r)` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^3) y IN sphere(q,r) DELETE p` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^3) (:real^2) = sphere(q,r) DELETE p` THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN closure(IMAGE (g:real^2->real^3) (outside d))` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded(outside(d:real^2->bool))` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~((p:real^3) IN closure(IMAGE (g:real^2->real^3) (outside d)))` THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM;
                DE_MORGAN_THM; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `compact(sphere(q:real^3,r) DIFF ball(p,e))` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_SPHERE; OPEN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `sphere(q:real^3,r) DIFF ball(p,e) SUBSET sphere(q,r) DELETE p`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_DELETE] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((p:real^3) IN ball(p,e))` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^3->real^2) (sphere(q,r) DIFF ball(p,e))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(q:real^3,r) DELETE p` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `(g:real^2->real^3) y` THEN ASM_REWRITE_TAC[IN_DIFF; IN_BALL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^2->real^3) y`) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (~a \/ b) ==> c`) THEN CONJ_TAC THENL
     [EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. (g:real^2->real^3) y1 = g y2 ==> y1 = y2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o AP_TERM `f:real^3->real^2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) ((:real^2) DIFF d) = (sphere(q,r) DELETE p) DIFF c`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^2) c = d`)) THEN MATCH_MP_TAC MOI_CSD_IMAGE_COMPL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET sphere(q,r)` THEN
    UNDISCH_TAC `~((p:real^3) IN c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (g:real^2->real^3) continuous_on s` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN c ==> x IN sphere(q:real^3,r) DELETE p` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^3->bool) SUBSET sphere(q,r)` THEN
    UNDISCH_TAC `~((p:real^3) IN c)` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^2->real^3) (inside d)` THEN
  EXISTS_TAC `(p:real^3) INSERT IMAGE (g:real^2->real^3) (outside d)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `IMAGE (g:real^2->real^3) (outside d)` THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE] THEN
    MP_TAC(ISPEC `IMAGE (g:real^2->real^3) (outside d)` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN closure(IMAGE (g:real^2->real^3) (outside d))` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    SET_TAC[];
    MATCH_MP_TAC MOI_CSD_IMAGE_DISJ THEN ASM_REWRITE_TAC[DISJOINT];
    REWRITE_TAC[SET_RULE `a UNION ((p:real^3) INSERT b) = p INSERT (a UNION b)`;
                GSYM IMAGE_UNION] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:real^3) IN sphere(q,r)` THEN UNDISCH_TAC `~((p:real^3) IN c)` THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN sphere(q,r) DELETE p` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^2) x IN closure(inside d)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(f:real^3->real^2) x IN frontier(inside d)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^2) c = d`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^2->real^3`; `inside(d:real^2->bool)`;
                   `closure(IMAGE (g:real^2->real^3) (inside d))`] IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^3->real^2) x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^3) ((f:real^3->real^2) x) = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `sphere(q:real^3,r) DELETE p`)) (concl th) &&
        not (can (find_term (fun t -> t = `c:real^3->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN sphere(q,r) DELETE p` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^2) x IN closure(outside d)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(f:real^3->real^2) x IN frontier(outside d)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^2) c = d`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^2->real^3`; `outside(d:real^2->bool)`;
                   `closure(IMAGE (g:real^2->real^3) (outside d))`] IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^3->real^2) x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^3) ((f:real^3->real^2) x) = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `sphere(q:real^3,r) DELETE p`)) (concl th) &&
        not (can (find_term (fun t -> t = `c:real^3->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (g:real^2->real^3) (outside d)`;
                   `(p:real^3) INSERT IMAGE (g:real^2->real^3) (outside d)`]
      SUBSET_CLOSURE) THEN
    ANTS_TAC THENL [SET_TAC[]; SET_TAC[]]]);;

(* Rays from the centre of a sphere: polar form of the points of the ball,  *)
(* uniqueness of the polar form, distances along a ray.                      *)

let MOI_CSD_SPHERE_RAY = prove
 (`!(q:real^3) r z z' t t'.
     &0 < r /\ z IN sphere(q,r) /\ z' IN sphere(q,r) /\ &0 <= t /\ &0 <= t' /\
     q + t % (z - q) = q + t' % (z' - q)
     ==> t = t' /\ (t = &0 \/ z = z')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t % (z - q) = t' % (z' - q):real^3` ASSUME_TAC THENL
   [UNDISCH_TAC `q + t % (z - q) = q + t' % (z' - q):real^3` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z - q:real^3) = r /\ norm(z' - q:real^3) = r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `t:real = t'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `norm:real^3->real` o
      check (fun th -> is_eq(concl th) && not (is_comb(lhs(concl th)) &&
                       fst(dest_const(rator(rator(lhs(concl th))))) = "vector_add")
             && type_of(lhs(concl th)) = `:real^3`)) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t' = &0` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t % (z - q) = t' % (z' - q):real^3` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN VECTOR_ARITH_TAC);;

let MOI_CSD_BALL_POLAR = prove
 (`!(q:real^3) r x.
     &0 < r /\ x IN ball(q,r) /\ ~(x = q)
     ==> ?t z. z IN sphere(q,r) /\ &0 < t /\ t < &1 /\ x = q + t % (z - q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x - q:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - q:real^3) < r` ASSUME_TAC THENL
   [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
  EXISTS_TAC `norm(x - q:real^3) / r` THEN
  EXISTS_TAC `q + (r / norm(x - q:real^3)) % (x - q)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG;
                NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[REAL_LT_DIV];
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
    REWRITE_TAC[VECTOR_ARITH `(q + a) - q:real^3 = a`; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `norm(x - q:real^3) / r * r / norm(x - q) = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(x - q:real^3)` THEN UNDISCH_TAC `&0 < r` THEN
      CONV_TAC REAL_FIELD;
      VECTOR_ARITH_TAC]]);;

let MOI_CSD_CONE_DIST = prove
 (`!(q:real^3) r z t.
     z IN sphere(q,r) /\ &0 <= t ==> dist(q,q + t % (z - q)) = t * r`,
  REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG;
              NORM_MUL] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
  AP_TERM_TAC THEN ASM_MESON_TAC[NORM_SUB]);;

let MOI_CSD_CONE_CONNECTED = prove
 (`!(q:real^3) u.
     connected u
     ==> connected {q + t % (z - q) | t,z | z IN u /\ &0 < t /\ t < &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{q + t % (z - q) | t,z | z IN u /\ &0 < t /\ t < &1} =
                IMAGE (\w:real^(1,3)finite_sum. q + drop(fstcart w) % (sndcart w - q))
                      (interval(vec 0:real^1,vec 1) PCROSS u)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_VEC] THEN
    REWRITE_TAC[EXISTS_LIFT; LIFT_DROP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX];
    MATCH_MP_TAC CONNECTED_PCROSS THEN ASM_REWRITE_TAC[CONNECTED_INTERVAL]]);;

let MOI_CSD_CONE_CLOSURE_LEMMA = prove
 (`!(q:real^3) r u w s.
     &0 < r /\ ~(u = {}) /\ u SUBSET sphere(q,r) /\ w IN closure u /\
     &0 <= s /\ s < &1
     ==> q + s % (w - q) IN
         closure {q + t % (z - q) | t,z | z IN u /\ &0 < t /\ t < &1}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = {q + t % (z - q) | t,z | z IN u /\ &0 < t /\ t < &1}:real^3->bool` THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    UNDISCH_TAC `~(u:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z0:real^3`) THEN
    SUBGOAL_THEN `~(q:real^3 = z0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z0:real^3) IN sphere(q,r)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_SPHERE; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `segment(q:real^3,z0) SUBSET k` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `z0:real^3`] THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`segment(q:real^3,z0)`; `k:real^3->bool`] SUBSET_CLOSURE) THEN
    ASM_REWRITE_TAC[CLOSURE_SEGMENT] THEN
    MP_TAC(ISPECL [`q:real^3`; `z0:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. q + s % (x - q)) u SUBSET k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. q + s % (x - q)`; `u:real^3->bool`; `closure k:real^3->bool`]
    IMAGE_CLOSURE_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CLOSED_CLOSURE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      MP_TAC(ISPEC `k:real^3->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The two sides of a cone over a simple closed curve c on sphere(q,r):    *)
(* if y meets the ball exactly in the cone, the ball minus y is the union  *)
(* of two disjoint connected open cones, both with the cone in the closure. *)

let MOI_CSD_CONE_SIDES = prove
 (`!(q:real^3) r c y.
     &0 < r /\ c SUBSET sphere(q,r) /\ c homeomorphic sphere(vec 0:real^2,&1) /\
     y INTER ball(q,r) = {q + t % (z - q) | t,z | z IN c /\ &0 <= t /\ t < &1}
     ==> ?s1 s2. connected s1 /\ connected s2 /\ ~(s1 = {}) /\ ~(s2 = {}) /\
                 DISJOINT s1 s2 /\ ball(q,r) DIFF y = s1 UNION s2 /\
                 y INTER ball(q,r) SUBSET closure s1 /\
                 y INTER ball(q,r) SUBSET closure s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `c:real^3->bool`] MOI_CSD_SPHERE_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` (X_CHOOSE_THEN `o2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(c:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(c:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY] THEN
    REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN o1 \/ z IN o2 ==> z IN sphere(q:real^3,r) /\ ~(z IN c)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `o1 UNION o2 = sphere(q:real^3,r) DIFF c` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN y INTER ball(q:real^3,r) <=>
                    ?t z. z IN c /\ &0 <= t /\ t < &1 /\ x = q + t % (z - q)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(y:real^3->bool) INTER ball(q,r)`)) THEN
  EXISTS_TAC `{q + t % (z - q) | t,z | z IN o1 /\ &0 < t /\ t < &1}:real^3->bool` THEN
  EXISTS_TAC `{q + t % (z - q) | t,z | z IN o2 /\ &0 < t /\ t < &1}:real^3->bool` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CSD_CONE_CONNECTED THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CSD_CONE_CONNECTED THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(o1:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    MAP_EVERY EXISTS_TAC [`q + inv(&2) % (z - q):real^3`; `inv(&2)`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    UNDISCH_TAC `~(o2:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    MAP_EVERY EXISTS_TAC [`q + inv(&2) % (z - q):real^3`; `inv(&2)`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`q:real^3`; `r:real`; `z1:real^3`; `z2:real^3`; `t1:real`; `t2:real`]
      MOI_CSD_SPHERE_RAY) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (o1:real^3->bool) o2` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z1:real^3`) THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `~(x:real^3 = q)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN y)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(x:real^3) IN y INTER ball(q,r)` (fun th -> MP_TAC th THEN SET_TAC[]) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(c:real^3->bool = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
        MAP_EVERY EXISTS_TAC [`&0`; `z:real^3`] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`q:real^3`; `r:real`; `x:real^3`] MOI_CSD_BALL_POLAR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `~((z:real^3) IN c)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN y)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(x:real^3) IN y INTER ball(q,r)` (fun th -> MP_TAC th THEN SET_TAC[]) THEN
        ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`t:real`; `z:real^3`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN o1 \/ z IN o2` MP_TAC THENL
       [UNDISCH_TAC `o1 UNION o2 = sphere(q:real^3,r) DIFF c` THEN
        UNDISCH_TAC `(z:real^3) IN sphere(q,r)` THEN UNDISCH_TAC `~((z:real^3) IN c)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`t:real`; `z:real^3`] THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`t:real`; `z:real^3`] THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(DISJ_CASES_THEN
        (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC))) THEN
      (SUBGOAL_THEN `(z:real^3) IN sphere(q,r) /\ ~(z IN c)` STRIP_ASSUME_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `(x:real^3) IN ball(q,r)` ASSUME_TAC THENL
        [ASM_REWRITE_TAC[IN_BALL] THEN
         ASM_SIMP_TAC[MOI_CSD_CONE_DIST; REAL_LT_IMP_LE] THEN
         GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
         MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN DISCH_TAC THEN
       MP_TAC(CONJ (ASSUME `(x:real^3) IN y`) (ASSUME `(x:real^3) IN ball(q,r)`)) THEN
       REWRITE_TAC[GSYM IN_INTER] THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN(X_CHOOSE_THEN `t':real` (X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC)) THEN
       SUBGOAL_THEN `(z':real^3) IN sphere(q,r)` ASSUME_TAC THENL
        [UNDISCH_TAC `(c:real^3->bool) SUBSET sphere(q,r)` THEN
         UNDISCH_TAC `(z':real^3) IN c` THEN SET_TAC[];
         ALL_TAC] THEN
       SUBGOAL_THEN `q + t % (z - q) = q + t' % (z' - q):real^3` ASSUME_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC] THEN
       MP_TAC(ISPECL [`q:real^3`; `r:real`; `z:real^3`; `z':real^3`; `t:real`; `t':real`]
         MOI_CSD_SPHERE_RAY) THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
       STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]])];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^3`; `r:real`; `o1:real^3->bool`; `z:real^3`; `t:real`]
      MOI_CSD_CONE_CLOSURE_LEMMA) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `o1 UNION o2 = sphere(q:real^3,r) DIFF c` THEN SET_TAC[];
      UNDISCH_TAC `(c:real^3->bool) SUBSET closure o1` THEN
      UNDISCH_TAC `(z:real^3) IN c` THEN SET_TAC[]];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^3`; `r:real`; `o2:real^3->bool`; `z:real^3`; `t:real`]
      MOI_CSD_CONE_CLOSURE_LEMMA) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `o1 UNION o2 = sphere(q:real^3,r) DIFF c` THEN SET_TAC[];
      UNDISCH_TAC `(c:real^3->bool) SUBSET closure o2` THEN
      UNDISCH_TAC `(z:real^3) IN c` THEN SET_TAC[]]]);;

