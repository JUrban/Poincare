(* ========================================================================= *)
(* pc_moi_s35_ext2: Moise GTM 47, Sec 35.1, the two-disk extension         *)
(* TWO_DISK_EXT (the term MOI_S35_TWO_DISK_EXT of pc_moi_s35_stmt.ml).     *)
(* Route: the sphere map and the annulus between the two disks reduce the  *)
(* problem to a PLH gamma of the square circle; by MOI_S5W_DICHOTOMY       *)
(* (pc_moi_s35_ext2t) gamma or gamma composed with the diagonal reflection  *)
(* extends over the square annulus.  In the first case the extension is    *)
(* glued and extended over the ball.  In the second case the same          *)
(* construction gives a PLH of the balls equal to g1 composed with a       *)
(* reflection R of d1; comparing local determinant signs (LOCAL_SIGN of    *)
(* pc_moi_s35_deg) at flat points of d0 and d1 through pasted maps (the    *)
(* H-trick) contradicts moi_s35_same_orient gg0 o0 gg1 o1.                 *)
(* ========================================================================= *)

needs "src/pc_moi_s35_ext2t.ml";;
needs "src/pc_moi_s35_ext.ml";;
needs "src/pc_moi_s35_deg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* B1: PL maps are affine on small balls; local linear parts.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_PL_AFFINE_BALL = prove
 (`!(f:real^M->real^N) s t.
     pl_map_on s f /\ open t /\ t SUBSET s /\ ~(t = {})
     ==> ?x r l y. &0 < r /\ ball(x,r) SUBSET t /\ linear l /\
                   !z. z IN ball(x,r) ==> f z = l z + y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^M` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0:real^M` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?r. &0 < r /\ cball(x0:real^M,r) SUBSET t INTER v`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t INTER v:real^M->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `x0:real^M`) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. k IN c /\ ~(interior(k INTER cball(x0:real^M,r)) = {})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{k INTER cball(x0:real^M,r) | k IN c}`
      NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_CBALL] THEN
        ASM_MESON_TAC[POLYTOPE_IMP_CLOSED];
        ASM_MESON_TAC[]];
      SUBGOAL_THEN `UNIONS {k INTER cball(x0:real^M,r) | k IN c} = cball(x0,r)`
      SUBST1_TAC THENL
       [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `polytope:(real^M->bool)->bool`))
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^M` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x:real^M`; `d:real`; `l:real^M->real^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[]]);;

let MOI_S5T_LIN_AT_BALL = prove
 (`!(f:real^3->real^3) s t.
     pl_map_on s f /\ open t /\ t SUBSET s /\ ~(t = {})
     ==> ?x m. x IN t /\ moi_s35_lin_at f x m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `t:real^3->bool`]
    MOI_S5T_PL_AFFINE_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`x:real^3`; `l:real^3->real^3`] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET; CENTRE_IN_BALL]; ALL_TAC] THEN
  REWRITE_TAC[moi_s35_lin_at] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN ball(x,r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC);;

let MOI_S5T_LIN_AT_LOCAL = prove
 (`!(f:real^3->real^3) g x m t.
     moi_s35_lin_at f x m /\ open t /\ x IN t /\ (!z. z IN t ==> g z = f z)
     ==> moi_s35_lin_at g x m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e r` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN t /\ x IN t /\ z IN ball(x,r)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `ball(x:real^3,e) SUBSET t` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let MOI_S5T_LIN_AT_COMPOSE = prove
 (`!(f:real^3->real^3) e q y m.
     linear e /\ moi_s35_lin_at f (q + e(y - q)) m
     ==> moi_s35_lin_at (\x. f(q + e(x - q))) y (m o e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE] THEN
  MP_TAC(ISPEC `e:real^3->real^3` LINEAR_BOUNDED_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / b` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3) + e(z - q) IN ball(q + e(y - q),r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN
    SUBGOAL_THEN `(q + e(y - q)) - (q + e(z - q)) = (e:real^3->real^3)(y - z)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `b * norm(y - z:real^3)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(y:real^3,z) < r / b` THEN REWRITE_TAC[dist] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(q + a) - (q + b):real^N = a - b`] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let MOI_S5T_SIGN3 = prove
 (`!a b c:real. &0 < a * b /\ &0 < a * c ==> &0 < b * c`,
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* B2: sides of a PL 3-ball, flat pieces of its frontier, images of open    *)
(* plane sets in a 2-sphere.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_BALL_SIDES = prove
 (`!u:real^3->bool.
     pl_ball 3 u
     ==> pl_sphere 2 (frontier u) /\ compact u /\ closed u /\
         interior u = inside(frontier u) /\
         outside(frontier u) = (:real^3) DIFF u /\
         frontier u SUBSET u /\ frontier u INTER interior u = {} /\
         open(interior u) /\ connected(interior u) /\
         frontier u SUBSET closure(interior u) /\
         frontier u SUBSET closure((:real^3) DIFF u)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP MOI_S5C_PL_BALL_3_FILL (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MP_TAC(MATCH_MP MOI_S5C_JB_CLOSURE
    (ASSUME `pl_sphere 2 (frontier u:real^3->bool)`)) THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed(u:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `outside(frontier u) = (:real^3) DIFF u` ASSUME_TAC THENL
   [UNDISCH_TAC `u = frontier u UNION inside(frontier u:real^3->bool)` THEN
    UNDISCH_TAC `inside (frontier u) INTER outside (frontier u:real^3->bool) = {}` THEN
    UNDISCH_TAC `inside (frontier u) UNION outside (frontier u:real^3->bool) =
                 (:real^3) DIFF frontier u` THEN
    SPEC_TAC(`frontier u:real^3->bool`,`s:real^3->bool`) THEN
    SPEC_TAC(`u:real^3->bool`,`c:real^3->bool`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier u SUBSET (u:real^3->bool) /\
                frontier u INTER interior u = {}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[OPEN_INTERIOR];
    UNDISCH_TAC `interior u = inside(frontier u:real^3->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `interior u = inside(frontier u:real^3->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `outside(frontier u) = (:real^3) DIFF u` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5T_HALF_CONVEX = prove
 (`!(p:real^3) n r.
     convex {x | x IN ball(p,r) /\ &0 < n dot (x - p)} /\
     convex {x | x IN ball(p,r) /\ n dot (x - p) < &0}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{x | x IN ball(p:real^3,r) /\ &0 < n dot (x - p)} =
    ball(p,r) INTER {x | n dot x > n dot p} /\
    {x | x IN ball(p:real^3,r) /\ n dot (x - p) < &0} =
    ball(p,r) INTER {x | n dot x < n dot p}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_RSUB; real_gt;
                REAL_ARITH `!a b:real. &0 < a - b <=> b < a`;
                REAL_ARITH `!a b:real. a - b < &0 <=> a < b`];
    SIMP_TAC[CONVEX_INTER; CONVEX_BALL; CONVEX_HALFSPACE_GT; CONVEX_HALFSPACE_LT]]);;

let MOI_S5T_FLAT_SIDES = prove
 (`!s (p:real^3) n r.
     pl_sphere 2 s /\ p IN s /\ &0 < r /\
     (!x. x IN ball(p,r) ==> (x IN s <=> n dot (x - p) = &0))
     ==> ({x | x IN ball(p,r) /\ &0 < n dot (x - p)} SUBSET inside s /\
          {x | x IN ball(p,r) /\ n dot (x - p) < &0} SUBSET outside s) \/
         ({x | x IN ball(p,r) /\ &0 < n dot (x - p)} SUBSET outside s /\
          {x | x IN ball(p,r) /\ n dot (x - p) < &0} SUBSET inside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5C_JB_CLOSURE (ASSUME `pl_sphere 2 (s:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3`; `n:real^3`; `r:real`] MOI_S5T_HALF_CONVEX) THEN
  ABBREV_TAC `hp = {x:real^3 | x IN ball(p,r) /\ &0 < n dot (x - p)}` THEN
  ABBREV_TAC `hm = {x:real^3 | x IN ball(p,r) /\ n dot (x - p) < &0}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(p,r) /\ ~(x IN s) ==> x IN hp \/ x IN hm`
  (LABEL_TAC "cov") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((x:real^3) IN s)` THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (s:real^3->bool) hp /\ DISJOINT s hm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN ball(p,r)` THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN inside s /\ (y IN hp \/ y IN hm)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) SUBSET closure(inside s)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ASM_REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "cov" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]];
    ALL_TAC;
    ALL_TAC] THEN
  (SUBGOAL_THEN `?y:real^3. y IN outside s /\ (y IN hp \/ y IN hm)` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `(s:real^3->bool) SUBSET closure(outside s)` THEN
     REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
     ASM_REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN USE_THEN "cov" MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[IN_BALL] THEN CONJ_TAC THENL
      [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
       MP_TAC(ISPEC `s:real^3->bool` OUTSIDE_NO_OVERLAP) THEN ASM SET_TAC[]];
     ALL_TAC;
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `hp:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `hm:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(rhs(concl th))))) THEN
  ASM SET_TAC[]);;

let MOI_S5T_SPHERE_OPEN_IMAGE = prove
 (`!s (f:real^2->real^3) t w.
     s homeomorphic sphere(vec 0:real^3,&1) /\ open t /\ f continuous_on t /\
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\
     IMAGE f t SUBSET s /\ w IN s /\ ~(w IN IMAGE f t)
     ==> open_in (subtopology euclidean s) (IMAGE f t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `w:real^3`] MOI_S5C_PUNCTURED_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^2` (X_CHOOSE_TAC `p':real^2->real^3`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) t SUBSET s DELETE w` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE ((p:real^3->real^2) o (f:real^2->real^3)) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s DELETE (w:real^3)` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `f:real^2->real^3`)) (concl th) && is_forall(concl th) &&
        can (find_term ((=) `t:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:real^2->real^3) x IN s DELETE w /\ f y IN s DELETE w`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `s DELETE (w:real^3)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (f:real^2->real^3) t =
                  {y | y IN s DELETE w /\
                       (p:real^3->real^2) y IN IMAGE ((p:real^3->real^2) o f) t}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; o_THM] THEN
      X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
        CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(f:real^2->real^3) x IN s DELETE w` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC OPEN_IN_DELETE THEN REWRITE_TAC[OPEN_IN_REFL]]);;

let MOI_S5T_CHART_FLAT = prove
 (`!s (psi:real^2->real^3) a e l y0 w.
     pl_sphere 2 s /\ &0 < e /\ linear l /\ (!v. l v = vec 0 ==> v = vec 0) /\
     (!z. z IN ball(a,e) ==> psi z = l z + y0) /\
     IMAGE psi (ball(a,e)) SUBSET s /\ w IN s /\ ~(w IN IMAGE psi (ball(a,e)))
     ==> ?n r. ~(n = vec 0) /\ &0 < r /\ (!v. n dot l v = &0) /\
               (!x. x IN ball(psi a,r) ==> (x IN s <=> n dot (x - psi a) = &0)) /\
               (!x. x IN ball(psi a,r) /\ x IN s
                    ==> ?v. norm v < e /\ x = psi a + l v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y:real^2. (l:real^2->real^3) x = l y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (l:real^2->real^3) (:real^2)` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dim(:real^2)` THEN
    ASM_SIMP_TAC[DIM_LINEAR_IMAGE_LE] THEN REWRITE_TAC[DIM_UNIV; DIMINDEX_2; DIMINDEX_3] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; orthogonal] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^3. n dot z = &0 ==> ?v. z = (l:real^2->real^3) v`
  (LABEL_TAC "pl") THENL
   [SUBGOAL_THEN `IMAGE (l:real^2->real^3) (:real^2) = {z:real^3 | n dot z = &0}`
    MP_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (l:real^2->real^3) (:real^2)`;
                     `{z:real^3 | n dot z = &0}`] DIM_EQ_SPAN) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`l:real^2->real^3`; `(:real^2)`] DIM_INJECTIVE_LINEAR_IMAGE) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          ASM_SIMP_TAC[DIM_HYPERPLANE] THEN
          REWRITE_TAC[DIM_UNIV; DIMINDEX_2; DIMINDEX_3] THEN ARITH_TAC];
        ASM_SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_HYPERPLANE; SUBSPACE_LINEAR_IMAGE;
                     SUBSPACE_UNIV]];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^2->real^3) continuous_on ball(a,e)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z:real^2. (l:real^2->real^3) z + y0` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `psi:real^2->real^3`; `ball(a:real^2,e)`;
                 `w:real^3`] MOI_S5T_SPHERE_OPEN_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; OPEN_BALL] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      not(can (find_term ((=) `vec 0:real^2`)) (concl th)) &&
      can (find_term ((=) `l:real^2->real^3`)) (concl th) &&
      not(can (find_term ((=) `psi:real^2->real^3`)) (concl th)))) THEN
    UNDISCH_TAC `(psi:real^2->real^3) x = psi y` THEN ASM_SIMP_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(psi:real^2->real^3) a IN uu` ASSUME_TAC THENL
   [SUBGOAL_THEN `(psi:real^2->real^3) a IN IMAGE psi (ball(a,e))` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
    concl th = `open (uu:real^3->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:real^2->real^3) a`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `l:real^2->real^3` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(l:real^2->real^3) a + y0 = psi a` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:real^3`; `min r1 (b * e)`] THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_MUL] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(psi a,min r1 (b * e)) /\ x IN s
                ==> ?v. norm v < e /\ x = (psi:real^2->real^3) a + (l:real^2->real^3) v`
  (LABEL_TAC "in") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (psi:real^2->real^3) (ball(a,e))` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `ball((psi:real^2->real^3) a,r1) SUBSET uu` THEN
      UNDISCH_TAC `(x:real^3) IN ball((psi:real^2->real^3) a,min r1 (b * e))` THEN
      REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z - a:real^2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN ball(a,e)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      REWRITE_TAC[NORM_SUB];
      ASM_SIMP_TAC[LINEAR_SUB] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(l:real^2->real^3) a + y0 = psi a`)) THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; USE_THEN "in" ACCEPT_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN USE_THEN "in" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `(x:real^3) IN ball((psi:real^2->real^3) a,min r1 (b * e))`)
      (ASSUME `(x:real^3) IN s`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(p + q) - p:real^N = q`];
    DISCH_TAC THEN USE_THEN "pl" (MP_TAC o C MATCH_MP
      (ASSUME `(n:real^3) dot (x - (psi:real^2->real^3) a) = &0`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` ASSUME_TAC) THEN
    SUBGOAL_THEN `norm(v:real^2) < e` ASSUME_TAC THENL
     [SUBGOAL_THEN `norm(v:real^2) * b < e * b` MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm((l:real^2->real^3) v)` THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `x - (psi:real^2->real^3) a = (l:real^2->real^3) v`)) THEN
        UNDISCH_TAC `(x:real^3) IN ball((psi:real^2->real^3) a,min r1 (b * e))` THEN
        REWRITE_TAC[IN_BALL; dist; REAL_LT_MIN] THEN
        MP_TAC(ISPECL [`x:real^3`; `(psi:real^2->real^3) a`] NORM_SUB) THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `a + v:real^2 IN ball(a,e)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `a - (a + v):real^N = --v`; NORM_NEG] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) = (psi:real^2->real^3) (a + v)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD] THEN
      UNDISCH_TAC `x - (psi:real^2->real^3) a = (l:real^2->real^3) v` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(l:real^2->real^3) a + y0 = psi a`)) THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(a,e)) SUBSET s` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B3: the outside lemma and the H-trick.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_OUTSIDE = prove
 (`!u w (gg:real^3->real^3) q r n.
     pl_ball 3 u /\ pl_ball 3 w /\ &0 < r /\
     gg continuous_on ball(q,r) /\
     (!x y. x IN ball(q,r) /\ y IN ball(q,r) /\ gg x = gg y ==> x = y) /\
     q IN frontier u /\
     (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0)) /\
     {x | x IN ball(q,r) /\ &0 < n dot (x - q)} SUBSET interior u /\
     IMAGE gg (ball(q,r) INTER u) SUBSET w /\
     (!x. x IN ball(q,r) /\ gg x IN frontier w ==> x IN frontier u) /\
     gg q IN frontier w
     ==> IMAGE gg {x | x IN ball(q,r) /\ n dot (x - q) < &0} SUBSET (:real^3) DIFF w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5C_JB_CLOSURE
    (ASSUME `pl_sphere 2 (frontier w:real^3->bool)`)) THEN STRIP_TAC THEN
  ABBREV_TAC `hm = {x:real^3 | x IN ball(q,r) /\ n dot (x - q) < &0}` THEN
  SUBGOAL_THEN `(hm:real^3->bool) SUBSET ball(q,r) /\ DISJOINT hm (frontier u)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hm" THEN REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER;
                                     IN_ELIM_THM; NOT_IN_EMPTY] THEN
    SIMP_TAC[] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN ball(q,r)` THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (gg:real^3->real^3) hm)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(q:real^3,r)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN EXPAND_TAC "hm" THEN
      REWRITE_TAC[MOI_S5T_HALF_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (frontier w) (IMAGE (gg:real^3->real^3) hm)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^3) IN frontier u` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `frontier w:real^3->bool`)) (concl th))) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier w:real^3->bool`; `IMAGE (gg:real^3->real^3) hm`]
    MOI_S5C_CONNECTED_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  SUBGOAL_THEN `IMAGE (gg:real^3->real^3) (ball(q,r)) SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN hm` THENL
     [SUBGOAL_THEN `(gg:real^3->real^3) x IN interior w` MP_TAC THENL
       [ASM SET_TAC[]; MP_TAC(ISPEC `w:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^3) IN hm)` THEN EXPAND_TAC "hm" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      ASM_CASES_TAC `(n:real^3) dot (x - q) = &0` THENL
       [SUBGOAL_THEN `(x:real^3) IN frontier u` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM SET_TAC[]];
        SUBGOAL_THEN `(x:real^3) IN interior u` MP_TAC THENL
         [UNDISCH_TAC `{x:real^3 | x IN ball(q,r) /\ &0 < n dot (x - q)} SUBSET interior u` THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]]];
      ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (gg:real^3->real^3) (ball(q,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real^3->real^3) q IN interior w` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (x:real^3). x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `IMAGE (gg:real^3->real^3) (ball(q,r))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S5T_HTRICK = prove
 (`!u w (f:real^3->real^3) (g:real^3->real^3) q r x y m m'.
     pl_ball 3 u /\ pl_ball 3 w /\ &0 < r /\
     f continuous_on u /\ (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
     IMAGE f u SUBSET w /\
     g continuous_on ball(q,r) /\
     (!x y. x IN ball(q,r) /\ y IN ball(q,r) /\ g x = g y ==> x = y) /\
     (!x. x IN ball(q,r) INTER frontier u ==> f x = g x) /\
     IMAGE g (ball(q,r) DIFF u) SUBSET (:real^3) DIFF w /\
     x IN ball(q,r) INTER interior u /\ y IN ball(q,r) DIFF u /\
     moi_s35_lin_at f x m /\ moi_s35_lin_at g y m'
     ==> &0 < det(matrix m) * det(matrix m')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. if z IN u then (f:real^3->real^3) z else g z`;
                 `ball(q:real^3,r)`; `x:real^3`; `y:real^3`;
                 `m:real^3->real^3`; `m':real^3->real^3`] LOCAL_SIGN) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_BALL; CONNECTED_BALL] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `ball(q:real^3,r) = (ball(q,r) INTER u) UNION (ball(q,r) DIFF interior u)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `ball(q:real^3,r)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
      EXISTS_TAC `ball(q:real^3,r)` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `ball(q:real^3,r) DIFF interior u =
                      ball(q,r) INTER ((:real^3) DIFF interior u)` SUBST1_TAC THENL
         [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
        REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR];
        ALL_TAC] THEN
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(q:real^3,r)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN
      ASM_CASES_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `frontier u:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN ASM_SIMP_TAC[CLOSURE_CLOSED]];
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(if (a:real^3) IN u then (f:real^3->real^3) a else g a) =
                 (if (b:real^3) IN u then f b else g b)` THEN
    ASM_CASES_TAC `(a:real^3) IN u` THEN ASM_CASES_TAC `(b:real^3) IN u` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) a IN w /\ ~((g:real^3->real^3) b IN w)` MP_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ASM_MESON_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) b IN w /\ ~((g:real^3->real^3) a IN w)` MP_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_S5T_LIN_AT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `ball(q:real^3,r) INTER interior u`] THEN
    SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR;
             ASSUME `moi_s35_lin_at (f:real^3->real^3) x m`;
             ASSUME `(x:real^3) IN ball(q,r) INTER interior u`] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN u` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    MATCH_MP_TAC MOI_S5T_LIN_AT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `ball(q:real^3,r) DIFF u`] THEN
    SIMP_TAC[OPEN_DIFF; OPEN_BALL; ASSUME `closed (u:real^3->bool)`;
             ASSUME `moi_s35_lin_at (g:real^3->real^3) y m'`;
             ASSUME `(y:real^3) IN ball(q,r) DIFF u`] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B4: the linear reflection of real^3 that swaps l(e1), l(e2) and fixes   *)
(* the normal n of the plane l(real^2) has negative determinant.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_L2_EXPAND = prove
 (`!(l:real^2->real^3) v. linear l ==> l v = v$1 % l(basis 1) + v$2 % l(basis 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v:real^2 = v$1 % basis 1 + v$2 % basis 2` MP_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]]);;

let MOI_S5T_REFLECT = prove
 (`!(l:real^2->real^3) n.
     linear l /\ (!v. l v = vec 0 ==> v = vec 0) /\ ~(n = vec 0) /\
     (!v. n dot l v = &0)
     ==> ?e. linear e /\ (!v. e (l v) = l (vector[v$2; v$1])) /\
             (!z. n dot e z = n dot z) /\ det(matrix e) < &0 /\
             (!x y. e x = e y ==> x = y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `bb = \x:real^3. x$1 % (l:real^2->real^3)(basis 1) + x$2 % l(basis 2) +
                              x$3 % n` THEN
  SUBGOAL_THEN `linear (bb:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. n dot (bb:real^3->real^3) x = x$3 * (n dot n)`
  ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. (bb:real^3->real^3) x = bb y ==> x = y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN SPEC_TAC(`x - y:real^3`,`d:real^3`) THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(d:real^3)$3 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. n dot z`) THEN
      ASM_REWRITE_TAC[DOT_RZERO] THEN
      ASM_REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `vector[(d:real^3)$1; d$2]:real^2 = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`l:real^2->real^3`; `vector[(d:real^3)$1; d$2]:real^2`]
        MOI_S5T_L2_EXPAND) THEN
      ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(bb:real^3->real^3) d = vec 0` THEN EXPAND_TAC "bb" THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2;
                VEC_COMPONENT] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bb:real^3->real^3` LINEAR_INJECTIVE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb':real^3->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t3 = \x:real^3. vector[x$2; x$1; x$3]:real^3` THEN
  SUBGOAL_THEN `linear (t3:real^3->real^3) /\ (!x. t3 (t3 x) = x) /\
                det(matrix t3) = -- &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t3" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3];
      SIMP_TAC[DET_3; matrix; LAMBDA_BETA; DIMINDEX_3; ARITH; VECTOR_3;
               BASIS_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  EXISTS_TAC `(bb:real^3->real^3) o (t3:real^3->real^3) o (bb':real^3->real^3)` THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^2` THEN
    SUBGOAL_THEN `(l:real^2->real^3) v = (bb:real^3->real^3)(vector[v$1; v$2; &0])` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`l:real^2->real^3`; `v:real^2`] MOI_S5T_L2_EXPAND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "bb" THEN REWRITE_TAC[VECTOR_3] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t3" THEN EXPAND_TAC "bb" THEN
    REWRITE_TAC[VECTOR_3] THEN
    MP_TAC(ISPECL [`l:real^2->real^3`; `vector[(v:real^2)$2; v$1]:real^2`]
      MOI_S5T_L2_EXPAND) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN `z:real^3 = bb((bb':real^3->real^3) z)` (fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t3" THEN REWRITE_TAC[VECTOR_3];
    ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; DET_MUL] THEN
    SUBGOAL_THEN `det(matrix(bb:real^3->real^3)) * det(matrix(bb':real^3->real^3)) = &1`
    MP_TAC THENL
     [ASM_SIMP_TAC[GSYM DET_MUL; GSYM MATRIX_COMPOSE] THEN
      SUBGOAL_THEN `(bb:real^3->real^3) o (bb':real^3->real^3) = (\x. x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MATRIX_ID; DET_I]];
      REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(bb':real^3->real^3) x = bb' y` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
        `!x y:real^3. (bb:real^3->real^3) x = bb y ==> x = y`)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `t3:real^3->real^3`) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `bb:real^3->real^3`) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* B5: a cone move of the square, the identity on C1, sending vec 0 to a    *)
(* given interior point b and affine (z -> z - z2 b + b) near vec 0.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_Q1_RELINT = prove
 (`!z:real^2. abs(z$1) < &1 /\ abs(z$2) < &1 ==> z IN relative_interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) = interval(--vector[&1;&1]:real^2,vector[&1;&1])`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR; ALL_TAC] THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S5T_Q1_CONE = prove
 (`!c:real^2. c IN relative_interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]])
     ==> ~(c IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) /\
         (!x y. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ y IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ y IN segment[c,x] ==> y = x) /\
         UNIONS {segment[c,x] | x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))} = (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `c:real^2`] THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL];
    MATCH_MP_TAC MOI_CON_CONE_RF THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(vector[&1;&1]:real^2)` THEN
    REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC]);;

let MOI_S5T_CONE_MOVE = prove
 (`!b:real^2. abs(b$1) < &1 /\ abs(b$2) < &1
     ==> ?mm mm' e. pl_homeomorphism ((interval[--vector[&1;&1]:real^2,vector[&1;&1]]),(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) (mm,mm') /\
                    (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> mm x = x) /\ &0 < e /\
                    (!z. z IN ball(vec 0,e) ==> mm z = z - z$2 % b + b)`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `m = max (abs((b:real^2)$1)) (abs(b$2))` THEN
  ABBREV_TAC `d = (&1 - m) / &4` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 / &4 /\ abs((b:real^2)$1) <= m /\ abs(b$2) <= m /\
                m < &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "m"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(d * (b:real^2)$1) <= d /\ abs(d * b$2) <= d` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs d = d` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `max (abs ((b:real^2)$1)) (abs (b$2)) = m` (K ALL_TAC) THEN
  ABBREV_TAC `c = vector[&0; --d]:real^2` THEN
  ABBREV_TAC `c' = c + (&1 + d) % b:real^2` THEN
  SUBGOAL_THEN `(c:real^2) IN relative_interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ (c':real^2) IN relative_interior (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5T_Q1_RELINT THEN
    MAP_EVERY EXPAND_TAC ["c'"; "c"] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `c:real^2` MOI_S5T_Q1_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `c':real^2` MOI_S5T_Q1_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `c:real^2`; `c':real^2`; `\x:real^2. x`; `\x:real^2. x`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S5W_MM_POLY] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(vector[&1;&1]:real^2)` THEN
      REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_S5W_ID_PLH THEN REWRITE_TAC[MOI_S5W_MM_POLY]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`moi_con_conemap (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) c c' (\x:real^2. x)`;
                        `moi_con_conemap (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) c' c (\x:real^2. x)`; `d / &4`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((z:real^2)$1) < d / &4 /\ abs(z$2) < d / &4` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`z:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((z:real^2)$2 + d) / (&1 + d) * (&1 + d) = z$2 + d /\
                &0 < (z$2 + d) / (&1 + d) /\ (z$2 + d) / (&1 + d) <= &1 /\
                abs(z$1) <= (z$2 + d) / (&1 + d)` MP_TAC THENL
   [SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ;
             REAL_LE_RDIV_EQ; ASSUME `&0 < &1 + d`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `abs((z:real^2)$1) * (&1 + d) <= d / &4 * (&5 / &4)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ABBREV_TAC `r = ((z:real^2)$2 + d) / (&1 + d)` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `vector[(z:real^2)$1 / r; &1]:real^2 IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
    SUBGOAL_THEN `abs((z:real^2)$1 / r) <= &1` MP_TAC THENL
     [SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < r ==> abs r = r`;
               REAL_LE_LDIV_EQ; ASSUME `&0 < r`] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:real^2 = c + r % (vector[(z:real^2)$1 / r; &1] - c)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_LID] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; ASSUME `&0 < r`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `c:real^2`; `c':real^2`; `\x:real^2. x`;
                 `vector[(z:real^2)$1 / r; &1]:real^2`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `z:real^2`)) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(c + r % (vector[(z:real^2)$1 / r; &1] - c)) +
              ((&1 - r) * (&1 + d)) % (b:real^2)` THEN
  CONJ_TAC THENL [EXPAND_TAC "c'" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `z:real^2`)) THEN
  SUBGOAL_THEN `(&1 - r) * (&1 + d) = &1 - (z:real^2)$2` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* B6: a chart of a 2-cell d extending a given PLH of the square circle    *)
(* onto the boundary of d, affine near vec 0 with vec 0 sent into o.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_Q1_CELL = prove
 (`pl_cell_with_boundary 2 (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ polytope (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ pl_polyhedron (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
   (!z:real^2. z IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ ~(z IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))) <=> abs(z$1) < &1 /\ abs(z$2) < &1)`,
  SUBGOAL_THEN `polytope (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
   [REWRITE_TAC[POLYTOPE_INTERVAL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{(interval[--vector[&1;&1]:real^2,vector[&1;&1]])}` THEN
    ASM_REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; UNIONS_1];
    REWRITE_TAC[relative_frontier] THEN
    SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL] THEN SET_TAC[];
    GEN_TAC THEN REWRITE_TAC[MOI_S5C_IN_RF1; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                             VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S5T_AFFINE_INJ = prove
 (`!(f:real^M->real^N) s l y b r.
     (!x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x') /\ ball(b,r) SUBSET s /\
     &0 < r /\ linear l /\ (!z. z IN ball(b,r) ==> f z = l z + y)
     ==> !v. l v = vec 0 ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^M)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / (&2 * norm(v:real^M)) /\ r / (&2 * norm v) * norm v < r`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
    ASM_REAL_ARITH_TAC;
    ABBREV_TAC `t = r / (&2 * norm(v:real^M))` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `b + t % v:real^M IN ball(b,r) /\ (b:real^M) IN ball(b,r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `b - (b + t % v):real^N = --(t % v)`;
                  NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b + t % v:real^M = b` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `s:real^M->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(b:real^M,r) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ball(b:real^M,r) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_MUL_RZERO; VECTOR_ADD_RID]];
    REWRITE_TAC[VECTOR_ARITH `b + t % v:real^N = b <=> t % v = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]]);;

let MOI_S5T_SPECIAL_CHART = prove
 (`!(d:real^3->bool) j (phi:real^2->real^3) phi' oo.
     pl_cell_with_boundary 2 d j /\ pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),j) (phi,phi') /\
     open oo /\ ~(oo INTER (d DIFF j) = {})
     ==> ?psi psi' e l y0.
           pl_homeomorphism ((interval[--vector[&1;&1]:real^2,vector[&1;&1]]),d) (psi,psi') /\
           (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> psi x = phi x) /\
           &0 < e /\ e <= &1 / &2 /\ linear l /\ (!v. l v = vec 0 ==> v = vec 0) /\
           (!z. z IN ball(vec 0,e) ==> psi z = l z + y0) /\
           IMAGE psi (ball(vec 0,e)) SUBSET oo INTER (d DIFF j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5T_Q1_CELL THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `d:real^3->bool`; `j:real^3->bool`;
                 `phi:real^2->real^3`; `phi':real^3->real^2`] MOI_S5C_CELL_EXT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^2->real^3` (X_CHOOSE_THEN `p0':real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(LABEL_TAC "pp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `p0:real^2->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `IMAGE (p0:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = j` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
        can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `j:real^3->bool`)) THEN
    MATCH_MP_TAC(SET_RULE `!f g (s:real^2->bool).
       (!x. x IN s ==> (f:real^2->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ww = {z:real^2 | z IN interval(--vector[&1;&1],vector[&1;&1]) /\
                               (p0:real^2->real^3) z IN oo}` THEN
  SUBGOAL_THEN `!z:real^2. z IN interval(--vector[&1;&1],vector[&1;&1]) <=>
                           abs(z$1) < &1 /\ abs(z$2) < &1` (LABEL_TAC "iv") THENL
   [REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (ww:real^2->bool) /\ ww SUBSET (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ ~(ww = {})`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ww" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
        check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
          can (find_term ((=) `p0:real^2->real^3`)) (concl th))) THEN
      SIMP_TAC[homeomorphism];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
        is_neg(concl th) && can (find_term ((=) `oo:real^3->bool`)) (concl th))) THEN
      REWRITE_TAC[IN_INTER; IN_DIFF; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(p0':real^3->real^2) x` THEN
      USE_THEN "pp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(x:real^3) IN d`] o
        SPECL [`(p0':real^3->real^2) x`; `x:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "iv" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `~((p0':real^3->real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))` MP_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN j)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `IMAGE (p0:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = j`)) THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(p0':real^3->real^2) x` THEN
        ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        MP_TAC(SPEC `(p0':real^3->real^2) x` (CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
          MOI_S5T_Q1_CELL))))) THEN
        MATCH_MP_TAC(TAUT `p /\ q ==> (p /\ q <=> r) ==> r`) THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. x IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ y IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\ (p0:real^2->real^3) x = p0 y
                             ==> x = y` (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pp" (MP_TAC o REWRITE_RULE[ASSUME `(x:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`] o CONJUNCT1 o
      SPECL [`x:real^2`; `vec 0:real^3`]) THEN
    USE_THEN "pp" (MP_TAC o REWRITE_RULE[ASSUME `(y:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`] o CONJUNCT1 o
      SPECL [`y:real^2`; `vec 0:real^3`]) THEN
    UNDISCH_TAC `(p0:real^2->real^3) x = p0 y` THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p0:real^2->real^3`; `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `ww:real^2->bool`] MOI_S5T_PL_AFFINE_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
        can (find_term ((=) `p0:real^2->real^3`)) (concl th)));
    DISCH_THEN(X_CHOOSE_THEN `b:real^2` (X_CHOOSE_THEN `r:real`
      (X_CHOOSE_THEN `l0:real^2->real^3` (X_CHOOSE_THEN `y0:real^3`
        STRIP_ASSUME_TAC))))] THEN
  SUBGOAL_THEN `abs((b:real^2)$1) < &1 /\ abs(b$2) < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(b:real^2) IN ww` MP_TAC THENL
     [UNDISCH_TAC `ball(b:real^2,r) SUBSET ww` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    EXPAND_TAC "ww" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "iv" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. (l0:real^2->real^3) v = vec 0 ==> v = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_AFFINE_INJ THEN
    MAP_EVERY EXISTS_TAC [`p0:real^2->real^3`; `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `y0:real^3`; `b:real^2`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ww:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `b:real^2` MOI_S5T_CONE_MOVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:real^2->real^2` (X_CHOOSE_THEN `mm':real^2->real^2`
    (X_CHOOSE_THEN `em:real` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(LABEL_TAC "mp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `mm:real^2->real^2`)) (concl th))) THEN
  SUBGOAL_THEN `norm(b:real^2) < &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:real^2` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_2; SUM_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(p0:real^2->real^3) o (mm:real^2->real^2)`;
    `(mm':real^2->real^2) o (p0':real^3->real^2)`;
    `min em (min (r / &3) (&1 / &2))`;
    `(l0:real^2->real^3) o (\z:real^2. z - z$2 % b)`;
    `(l0:real^2->real^3) b + y0`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(x:real^2) IN relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`)]));
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `v:real^2` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v - (v:real^2)$2 % b = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(AP_TERM `\x:real^2. x$2` th)) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `a - a * c = &0 <=> a * (&1 - c) = &0`; REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(&1 - (b:real^2)$2 = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `abs((b:real^2)$2) < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO];
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_BALL_0; REAL_LT_MIN] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(mm:real^2->real^2) z = z - z$2 % b + b` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN `z - (z:real^2)$2 % b + b IN ball(b,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `b - (z - c % b + b):real^N = c % b - z`] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `abs((z:real^2)$2) * norm(b:real^2) + norm(z:real^2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM NORM_MUL] THEN
        MP_TAC(ISPECL [`(z:real^2)$2 % (b:real^2)`; `--(z:real^2)`] NORM_TRIANGLE) THEN
        REWRITE_TAC[NORM_NEG; GSYM VECTOR_SUB] THEN MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`z:real^2`; `2`] COMPONENT_LE_NORM) THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((z:real^2)$2) * norm(b:real^2) <= norm z * &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        UNDISCH_TAC `norm(b:real^2) < &2` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `norm(z:real^2) < r / &3` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `z - (z:real^2)$2 % b + b IN ball(b,r)`)]) THEN
    SIMP_TAC[LINEAR_ADD; ASSUME `linear (l0:real^2->real^3)`] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; REAL_LT_MIN; o_THM] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(mm:real^2->real^2) z = z - z$2 % b + b` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN `z - (z:real^2)$2 % b + b IN ww` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(b:real^2,r) SUBSET ww` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `b - (z - c % b + b):real^N = c % b - z`] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `abs((z:real^2)$2) * norm(b:real^2) + norm(z:real^2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM NORM_MUL] THEN
        MP_TAC(ISPECL [`(z:real^2)$2 % (b:real^2)`; `--(z:real^2)`] NORM_TRIANGLE) THEN
        REWRITE_TAC[NORM_NEG; GSYM VECTOR_SUB] THEN MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`z:real^2`; `2`] COMPONENT_LE_NORM) THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((z:real^2)$2) * norm(b:real^2) <= norm z * &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        UNDISCH_TAC `norm(b:real^2) < &2` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `norm(z:real^2) < r / &3` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `z - (z:real^2)$2 % b + b IN ww` THEN EXPAND_TAC "ww" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ABBREV_TAC `y = z - (z:real^2)$2 % b + b` THEN
    SUBGOAL_THEN `(y:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
    USE_THEN "pp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(y:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`] o
      CONJUNCT1 o SPECL [`y:real^2`; `vec 0:real^3`]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (p0:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = j`)) THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `c:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^2) = c` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5T_Q1_CELL)))) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(c:real^2) IN interval(--vector[&1;&1],vector[&1;&1])` THEN
      UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
      USE_THEN "iv" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MOI_S5C_IN_RF1] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* B7: a PL reflection R of the cell d1, equal to phi tau phi^-1 on j1 and   *)
(* affine with linear part of negative determinant near a flat point q.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_TAU_Q1 = prove
 (`pl_homeomorphism ((interval[--vector[&1;&1]:real^2,vector[&1;&1]]),(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ((\x:real^2. vector[x$2; x$1]:real^2),(\x:real^2. vector[x$2; x$1]:real^2)) /\ linear (\x:real^2. vector[x$2; x$1]:real^2) /\
   (!x. (\x:real^2. vector[x$2; x$1]:real^2) ((\x:real^2. vector[x$2; x$1]:real^2) x) = x) /\ (!x. norm((\x:real^2. vector[x$2; x$1]:real^2) x) = norm x) /\
   (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (\x:real^2. vector[x$2; x$1]:real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))`,
  SUBGOAL_THEN `linear (\x:real^2. vector[x$2; x$1]:real^2) /\ (!x. (\x:real^2. vector[x$2; x$1]:real^2) ((\x:real^2. vector[x$2; x$1]:real^2) x) = x) /\
                (!x. x IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) ==> (\x:real^2. vector[x$2; x$1]:real^2) x IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
                (!x. x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (\x:real^2. vector[x$2; x$1]:real^2) x IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[linear; MOI_S5C_IN_RF1; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_NEG_COMPONENT] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) = (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN EXISTS_TAC `vector[(y:real^2)$2; y$1]:real^2` THEN
      REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
        UNDISCH_TAC `(y:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
        REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) (\x:real^2. vector[x$2; x$1]:real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^2. (\x:real^2. vector[x$2; x$1]:real^2) x + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    REWRITE_TAC[MOI_S5T_Q1_CELL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[pl_homeomorphism; homeomorphism; LINEAR_CONTINUOUS_ON] THEN
  REWRITE_TAC[NORM_EQ; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S5T_REFLECTION_AT = prove
 (`!u (d1:real^3->bool) j1 d0 j0 (phi:real^2->real^3) phi' o1.
     pl_ball 3 u /\ pl_cell_with_boundary 2 d1 j1 /\ d1 SUBSET frontier u /\
     pl_cell_with_boundary 2 d0 j0 /\ d0 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),j1) (phi,phi') /\ open o1 /\ ~(o1 INTER (d1 DIFF j1) = {})
     ==> ?R R' q n r e.
           pl_homeomorphism (d1,d1) (R,R') /\
           (!c. c IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> R (phi c) = phi (vector[c$2; c$1])) /\
           q IN o1 INTER (d1 DIFF j1) /\ &0 < r /\ ball(q,r) SUBSET o1 /\ ~(n = vec 0) /\
           (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0)) /\
           ball(q,r) INTER frontier u SUBSET d1 /\
           linear e /\ (!z. n dot e z = n dot z) /\ det(matrix e) < &0 /\
           (!x y. e x = e y ==> x = y) /\
           (!x. x IN ball(q,r) INTER frontier u
                ==> R x = q + e(x - q) /\ R x IN o1 INTER d1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`; `phi:real^2->real^3`;
                 `phi':real^3->real^2`; `o1:real^3->bool`] MOI_S5T_SPECIAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^2->real^3` (X_CHOOSE_THEN `psi':real^3->real^2`
    (X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC))))) THEN
  MP_TAC MOI_S5T_TAU_Q1 THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "sp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `psi:real^2->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `(psi:real^2->real^3) (vec 0) = y0` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(l:real^2->real^3) (vec 0) + y0` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `y0:real^3`)) (concl th))) THEN
      REWRITE_TAC[CENTRE_IN_BALL] THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPEC `l:real^2->real^3` LINEAR_0) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^2,e0) SUBSET (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_NEG_COMPONENT] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`z:real^2`; `2`] COMPONENT_LE_NORM) THEN
    UNDISCH_TAC `e0 <= &1 / &2` THEN UNDISCH_TAC `norm(z:real^2) < e0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN o1 INTER (d1 DIFF j1)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,e0)) SUBSET o1 INTER (d1 DIFF j1)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^3. w IN d0` (X_CHOOSE_TAC `w:real^3`) THENL
   [MP_TAC(ISPECL [`d0:real^3->bool`; `j0:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `psi:real^2->real^3`; `vec 0:real^2`; `e0:real`;
                 `l:real^2->real^3`; `y0:real^3`; `w:real^3`] MOI_S5T_CHART_FLAT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,e0)) SUBSET o1 INTER (d1 DIFF j1)` THEN
      UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN SET_TAC[];
      UNDISCH_TAC `(w:real^3) IN d0` THEN
      UNDISCH_TAC `(d0:real^3->bool) SUBSET frontier u` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,e0)) SUBSET o1 INTER (d1 DIFF j1)` THEN
      UNDISCH_TAC `(w:real^3) IN d0` THEN
      UNDISCH_TAC `DISJOINT (d0:real^3->bool) d1` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`l:real^2->real^3`; `n:real^3`] MOI_S5T_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\ ball(y0:real^3,r2) SUBSET o1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(o1:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(y0:real^3) IN o1 INTER (d1 DIFF j1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(y0,min r1 r2) INTER frontier u
                    ==> ?v. v IN ball(vec 0:real^2,e0) /\ x = (psi:real^2->real^3) v`
  (LABEL_TAC "rep") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN ball(y0,r1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN ball(y0,min r1 r2)` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN ball(y0,r1)`)
      (ASSUME `(x:real^3) IN frontier u`)) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `e0:real`)) (concl th) &&
        can (find_term ((=) `r1:real`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(l:real^2->real^3) v + y0` THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `y0:real^3`)) (concl th) &&
      can (find_term ((=) `ball(vec 0:real^2,e0)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN ball(vec 0:real^2,e0)
                    ==> (psi':real^3->real^2) ((psi:real^2->real^3) v) = v /\
                        psi v = (l:real^2->real^3) v + y0 /\
                        psi v IN o1 INTER d1`
  (LABEL_TAC "pv") THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(v:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(vec 0:real^2,e0) SUBSET (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
        UNDISCH_TAC `(v:real^2) IN ball(vec 0,e0)` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "sp" (MP_TAC o REWRITE_RULE[ASSUME `(v:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`] o CONJUNCT1 o
        SPECL [`v:real^2`; `vec 0:real^3`]) THEN SIMP_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `y0:real^3`)) (concl th) &&
        can (find_term ((=) `ball(vec 0:real^2,e0)`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `IMAGE (psi:real^2->real^3) (ball(vec 0,e0)) SUBSET o1 INTER (d1 DIFF j1)` THEN
      UNDISCH_TAC `(v:real^2) IN ball(vec 0,e0)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^2. v IN ball(vec 0,e0) ==> vector[v$2; v$1] IN ball(vec 0:real^2,e0)`
  (LABEL_TAC "tb") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    SUBGOAL_THEN `norm(vector[(v:real^2)$2; v$1]:real^2) = norm v` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_EQ; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(psi:real^2->real^3) o (\x:real^2. vector[x$2; x$1]:real^2) o (psi':real^3->real^2)`;
    `((psi:real^2->real^3) o (\x:real^2. vector[x$2; x$1]:real^2)) o (psi':real^3->real^2)`;
    `y0:real^3`; `n:real^3`; `min r1 r2`; `e:real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(c:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` ASSUME_TAC THENL
     [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S5T_Q1_CELL)))) THEN
      UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi':real^3->real^2) ((phi:real^2->real^3) c) = c` SUBST1_TAC THENL
     [SUBGOAL_THEN `(phi:real^2->real^3) c = psi c` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `phi:real^2->real^3`)) (concl th) &&
          can (find_term ((=) `psi:real^2->real^3`)) (concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "sp" (MP_TAC o REWRITE_RULE[ASSUME `(c:real^2) IN (interval[--vector[&1;&1]:real^2,vector[&1;&1]])`] o CONJUNCT1 o
        SPECL [`c:real^2`; `vec 0:real^3`]) THEN SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `phi:real^2->real^3`)) (concl th) &&
      can (find_term ((=) `psi:real^2->real^3`)) (concl th))) THEN
    UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^3,r2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `n:real^3`)) (concl th) &&
      can (find_term ((=) `r1:real`)) (concl th) &&
      not(can (find_term ((=) `e0:real`)) (concl th)))) THEN
    UNDISCH_TAC `(x:real^3) IN ball(y0,min r1 r2)` THEN
    REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "rep" (MP_TAC o C MATCH_MP (ASSUME
      `(x:real^3) IN ball(y0,min r1 r2) INTER frontier u`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "pv" (MP_TAC o C MATCH_MP (ASSUME `(v:real^2) IN ball(vec 0,e0)`)) THEN
    SIMP_TAC[IN_INTER];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "rep" (MP_TAC o C MATCH_MP (ASSUME
      `(x:real^3) IN ball(y0,min r1 r2) INTER frontier u`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[o_THM] THEN
    USE_THEN "pv" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(v:real^2) IN ball(vec 0,e0)`)) THEN
    USE_THEN "tb" (ASSUME_TAC o C MATCH_MP (ASSUME `(v:real^2) IN ball(vec 0,e0)`)) THEN
    USE_THEN "pv" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `vector[(v:real^2)$2; v$1] IN ball(vec 0:real^2,e0)`)) THEN
    SUBGOAL_THEN `(psi':real^3->real^2) ((psi:real^2->real^3) v) = v` SUBST1_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ARITH `(a + y) - y:real^N = a`] THEN VECTOR_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* B8: interiors of cells are open in the sphere; points near a cell        *)
(* interior whose image lies on the target sphere lie on the cell; the      *)
(* orientation of a flat ball (positive side inside).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_CELL_INTERIOR_OPEN = prove
 (`!s (e:real^3->bool) i w.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 e i /\ e SUBSET s /\ w IN s /\ ~(w IN e)
     ==> open_in (subtopology euclidean s) (e DIFF i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `i:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5C_SPHERE_DISK_OPEN THEN
  MAP_EVERY EXISTS_TAC [`e:real^3->bool`; `g:real^3->real^3`; `w:real^3`] THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC] THEN
  FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th)));;

let MOI_S5T_PRE_OUT = prove
 (`!s' (e:real^3->bool) i d j (g:real^3->real^3) g' (gg:real^3->real^3) oo q sr w.
     pl_sphere 2 s' /\ pl_cell_with_boundary 2 e i /\ e SUBSET s' /\ w IN s' /\
     ~(w IN e) /\ pl_cell_with_boundary 2 d j /\ pl_homeomorphism (d,e) (g,g') /\
     open oo /\ gg continuous_on oo /\
     (!x y. x IN oo /\ y IN oo /\ gg x = gg y ==> x = y) /\
     (!x. x IN oo INTER d ==> gg x = g x) /\
     q IN d DIFF j /\ &0 < sr /\ ball(q,sr) SUBSET oo
     ==> ?rho. &0 < rho /\ rho <= sr /\
               !x. x IN ball(q,rho) /\ gg x IN s' ==> x IN d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "gp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th)) THEN
  SUBGOAL_THEN `(g':real^3->real^3) continuous_on e` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th)) THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) j = i` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5E_PLH_CELL_BOUNDARY THEN
    MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `e:real^3->bool`; `g':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN d /\ ~(q IN j)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN d DIFF j` THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "gp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(q:real^3) IN d`] o
    CONJUNCT1 o SPECL [`q:real^3`; `q:real^3`]) THEN
  SUBGOAL_THEN `(g:real^3->real^3) q IN e DIFF i` ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (g:real^3->real^3) j = i`)) THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN d` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN j` THEN UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "gp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(z:real^3) IN d`] o
      CONJUNCT1 o SPECL [`z:real^3`; `z:real^3`]) THEN
    UNDISCH_TAC `~((q:real^3) IN j)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^3) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t)
     [`(g':real^3->real^3) ((g:real^3->real^3) q) = q`;
      `(g':real^3->real^3) ((g:real^3->real^3) z) = z`;
      `(g:real^3->real^3) q = g z`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s':real^3->bool`; `e:real^3->bool`; `i:real^3->bool`; `w:real^3`]
    MOI_S5T_CELL_INTERIOR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g':real^3->real^3`; `e:real^3->bool`; `ball(q:real^3,sr)`]
    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean s') ((e DIFF i) INTER u1:real^3->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `e DIFF i:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^3->real^3) q IN u2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^3->real^3) q IN (e DIFF i) INTER u1` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g:real^3->real^3) q IN {x | x IN e /\ g' x IN ball(q,sr)}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
        UNDISCH_TAC `(g:real^3->real^3) q IN e DIFF i` THEN SET_TAC[];
        ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real^3->real^3`; `oo:real^3->bool`; `u2:real^3->bool`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(q:real^3) IN oo` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(q:real^3,sr) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gg:real^3->real^3) q = g q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gg:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `g:real^3->real^3`)) (concl th) &&
      not(can (find_term ((=) `y:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min rho sr` THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN oo /\ (gg:real^3->real^3) x IN u2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(q:real^3,rho) SUBSET {x | x IN oo /\ (gg:real^3->real^3) x IN u2}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real^3->real^3) x IN (e DIFF i) INTER u1` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g':real^3->real^3) ((gg:real^3->real^3) x) IN ball(q,sr)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real^3->real^3) x IN {x | x IN e /\ (g':real^3->real^3) x IN ball(q,sr)}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "gp" (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `(gg:real^3->real^3) x IN e`] o
    CONJUNCT2 o SPECL [`q:real^3`; `(gg:real^3->real^3) x`]) THEN
  SUBGOAL_THEN `(g':real^3->real^3) ((gg:real^3->real^3) x) IN oo` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(q:real^3,sr) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) = (g':real^3->real^3) ((gg:real^3->real^3) x)`
  (fun th -> ONCE_REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `oo:real^3->bool`)) (concl th) &&
    not(can (find_term ((=) `g:real^3->real^3`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gg:real^3->real^3) ((g':real^3->real^3) ((gg:real^3->real^3) x)) =
                (g:real^3->real^3) (g' (gg x))` SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gg:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `g:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `oo INTER d:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ASM_REWRITE_TAC[]]);;

let MOI_S5T_TRI = prove
 (`!a P Q R. (&0 < a ==> P) /\ (a < &0 ==> Q) /\ (a = &0 ==> R) /\
             ~(P /\ Q) /\ ~(P /\ R) /\ ~(Q /\ R)
             ==> (&0 < a <=> P) /\ (a < &0 <=> Q) /\ (a = &0 <=> R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `&0 < a \/ a < &0 \/ a = &0`) THENL
   [SUBGOAL_THEN `~(a < &0) /\ ~(a = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    SUBGOAL_THEN `~(&0 < a) /\ ~(a = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    SUBGOAL_THEN `~(&0 < a) /\ ~(a < &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]);;

let MOI_S5T_ORIENT_CORE = prove
 (`!u (q:real^3) n r.
     frontier u SUBSET u /\ frontier u INTER interior u = {} /\
     (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0)) /\
     (!x. x IN ball(q,r) /\ &0 < n dot (x - q) ==> x IN interior u) /\
     (!x. x IN ball(q,r) /\ n dot (x - q) < &0 ==> ~(x IN u))
     ==> !x. x IN ball(q,r)
             ==> (&0 < n dot (x - q) <=> x IN interior u) /\
                 (n dot (x - q) < &0 <=> ~(x IN u)) /\
                 (n dot (x - q) = &0 <=> x IN frontier u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "pos")
      (LABEL_TAC "neg"))))) THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5T_TRI THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN USE_THEN "fl" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,r)`)) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    UNDISCH_TAC `frontier u INTER interior u = {}:real^3->bool` THEN SET_TAC[];
    UNDISCH_TAC `frontier u SUBSET (u:real^3->bool)` THEN SET_TAC[]]);;

let MOI_S5T_FLAT_ORIENT = prove
 (`!u (q:real^3) n r.
     pl_ball 3 u /\ q IN frontier u /\ &0 < r /\
     (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0))
     ==> ?n'. (n' = n \/ n' = --n) /\
              !x. x IN ball(q,r)
                  ==> (&0 < n' dot (x - q) <=> x IN interior u) /\
                      (n' dot (x - q) < &0 <=> ~(x IN u)) /\
                      (n' dot (x - q) = &0 <=> x IN frontier u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `q:real^3`; `n:real^3`; `r:real`]
    MOI_S5T_FLAT_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `interior u = inside(frontier u:real^3->bool)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `outside(frontier u) = (:real^3) DIFF u` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN STRIP_TAC THENL
   [EXISTS_TAC `n:real^3` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5T_ORIENT_CORE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `--n:real^3` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S5T_ORIENT_CORE THEN ASM_REWRITE_TAC[DOT_LNEG] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --a <=> a < &0`; REAL_ARITH `--a < &0 <=> &0 < a`;
                REAL_NEG_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B9: sign comparisons at flat points of d0 (with gg0) and of d1 (with gg1 *)
(* composed with the 3D reflection).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_HALF_PTS = prove
 (`!(q:real^3) n r.
     ~(n = vec 0) /\ &0 < r
     ==> ?a b. a IN ball(q,r) /\ b IN ball(q,r) /\
               &0 < n dot (a - q) /\ n dot (b - q) < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(n:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `t = r / (&2 * norm(n:real^3))` THEN
  SUBGOAL_THEN `&0 < t /\ t * norm(n:real^3) < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> r / (&2 * m) * m = r / &2`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (n:real^3) dot n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`q + t % n:real^3`; `q - t % n:real^3`] THEN
  REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `q - (q + t % n):real^3 = --(t % n)`;
              VECTOR_ARITH `q - (q - t % n):real^3 = t % n`; NORM_NEG; NORM_MUL;
              VECTOR_ARITH `(q + t % n) - q:real^3 = t % n`;
              VECTOR_ARITH `(q - t % n) - q:real^3 = --(t % n)`; DOT_RNEG; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_LT_MUL] THEN
  REWRITE_TAC[REAL_ARITH `--a < &0 <=> &0 < a`] THEN ASM_SIMP_TAC[REAL_LT_MUL]);;

let MOI_S5T_CHART_C1 = prove
 (`!(d:real^3->bool) j.
     pl_cell_with_boundary 2 d j ==> ?f f'. pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),j) (f,f')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S5E_CELL_PLH) THEN
  ASM_REWRITE_TAC[MOI_S5T_Q1_CELL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `f':real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `f':real^3->real^2`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`; `d:real^3->bool`] THEN
  ASM_REWRITE_TAC[MOI_S5T_Q1_CELL] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN REWRITE_TAC[MOI_S5W_MM_POLY]);;

let MOI_S5T_LOCAL_D0 = prove
 (`!u w (d0:real^3->bool) j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0' oo
    (gg0:real^3->real^3) (ff:real^3->real^3) ff'.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0') /\
     open oo /\ ~(oo INTER (d0 DIFF j0) = {}) /\
     pl_map_on oo gg0 /\ (!x y. x IN oo /\ y IN oo /\ gg0 x = gg0 y ==> x = y) /\
     (!x. x IN oo INTER d0 ==> gg0 x = g0 x) /\ IMAGE gg0 (oo INTER u) SUBSET w /\
     pl_homeomorphism (u,w) (ff,ff') /\ (!x. x IN d0 ==> ff x = g0 x)
     ==> ?x m y mm. x IN interior u /\ moi_s35_lin_at ff x m /\
                    y IN oo /\ moi_s35_lin_at gg0 y mm /\
                    &0 < det(matrix m) * det(matrix mm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior u = inside(frontier u:real^3->bool)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior w = inside(frontier w:real^3->bool)`)) THEN
  MP_TAC(ISPECL [`d0:real^3->bool`; `j0:real^3->bool`] MOI_S5T_CHART_C1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_TAC `f':real^3->real^2`)) THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                 `d1:real^3->bool`; `j1:real^3->bool`; `f:real^2->real^3`;
                 `f':real^3->real^2`; `oo:real^3->bool`] MOI_S5T_REFLECTION_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (d0:real^3->bool) d1` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `R':real^3->real^3`
    (X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `r:real`
      (X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(q:real^3) IN d0 /\ ~(q IN j0) /\ q IN oo /\ q IN frontier u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN oo INTER (d0 DIFF j0)` THEN
    UNDISCH_TAC `(d0:real^3->bool) SUBSET frontier u` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `q:real^3`; `n:real^3`; `r:real`]
    MOI_S5T_FLAT_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tri"))) THEN
  SUBGOAL_THEN `~(n':real^3 = vec 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `?wp:real^3. wp IN frontier w /\ ~(wp IN e0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e1:real^3->bool`; `i1:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((e1:real^3->bool) DIFF i1 = {})` THEN
    UNDISCH_TAC `(e1:real^3->bool) SUBSET frontier w` THEN
    UNDISCH_TAC `DISJOINT (e0:real^3->bool) e1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg0:real^3->real^3) continuous_on oo` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier w:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
                 `d0:real^3->bool`; `j0:real^3->bool`; `g0:real^3->real^3`;
                 `g0':real^3->real^3`; `gg0:real^3->real^3`; `oo:real^3->bool`;
                 `q:real^3`; `r:real`; `wp:real^3`] MOI_S5T_PRE_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(q:real^3,rho) SUBSET ball(q,r) /\ ball(q,rho) SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(q:real^3,rho) SUBSET ball(q,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(q:real^3,r)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(q,rho)
                 ==> (&0 < n' dot (x - q) <=> x IN interior u) /\
                     (n' dot (x - q) < &0 <=> ~(x IN u)) /\
                     (n' dot (x - q) = &0 <=> x IN frontier u)` (LABEL_TAC "tr") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "tri" MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(q:real^3,rho) SUBSET ball(q,r)` THEN
    UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (gg0:real^3->real^3) {x | x IN ball(q,rho) /\ n' dot (x - q) < &0}
    SUBSET (:real^3) DIFF w` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_OUTSIDE THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `oo:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gg0:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN UNDISCH_TAC `(y:real^3) IN ball(q,rho)` THEN
      SET_TAC[];
      GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `IMAGE (gg0:real^3->real^3) (oo INTER u) SUBSET w` THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN d0` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `rho:real`)) (concl th) &&
          can (find_term ((=) `frontier w:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(d0:real^3->bool) SUBSET frontier u` THEN SET_TAC[]];
      SUBGOAL_THEN `(gg0:real^3->real^3) q = g0 q` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `oo INTER d0:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
        GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
          MOI_S5C_HEAD "pl_homeomorphism" th &&
          can (find_term ((=) `g0:real^3->real^3`)) (concl th))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o SPECL [`q:real^3`; `q:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e0:real^3->bool) SUBSET frontier w` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(q:real^3,rho) DIFF u = {x | x IN ball(q,rho) /\ n' dot (x - q) < &0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN ball(q,rho)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real^3->real^3) continuous_on u /\
                (!x y. x IN u /\ y IN u /\ ff x = ff y ==> x = y) /\
                IMAGE ff u SUBSET w /\ pl_map_on u ff` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `ff:real^3->real^3`)) (concl th))) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
       [`!x. x IN u ==> (ff':real^3->real^3) ((ff:real^3->real^3) x) = x`] THEN
      MESON_TAC[];
      UNDISCH_TAC `IMAGE (ff:real^3->real^3) u = w` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `n':real^3`; `rho:real`] MOI_S5T_HALF_PTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pa:real^3` (X_CHOOSE_THEN `pb:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`ff:real^3->real^3`; `u:real^3->bool`;
                 `ball(q:real^3,rho) INTER interior u`] MOI_S5T_LIN_AT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR];
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `pa:real^3` THEN
      REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(pa:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `m0:real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`gg0:real^3->real^3`; `oo:real^3->bool`;
                 `ball(q:real^3,rho) DIFF u`] MOI_S5T_LIN_AT_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_BALL];
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `pb:real^3` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `mm0:real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  MAP_EVERY EXISTS_TAC [`x0:real^3`; `m0:real^3->real^3`; `y0:real^3`;
                        `mm0:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(x0:real^3) IN ball(q,rho) INTER interior u` THEN SET_TAC[];
    UNDISCH_TAC `(y0:real^3) IN ball(q,rho) DIFF u` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5T_HTRICK THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `w:real^3->bool`; `ff:real^3->real^3`;
                        `gg0:real^3->real^3`; `q:real^3`; `rho:real`; `x0:real^3`;
                        `y0:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `oo:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gg0:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `y:real^3`)) (concl th) &&
      can (find_term ((=) `oo:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN
    UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN UNDISCH_TAC `(y:real^3) IN ball(q,rho)` THEN
    SET_TAC[];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN d0 /\ x IN oo` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `ball(q:real^3,r) INTER frontier u SUBSET d0` THEN
        UNDISCH_TAC `ball(q:real^3,rho) SUBSET ball(q,r)` THEN
        UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN
        UNDISCH_TAC `(x:real^3) IN frontier u` THEN SET_TAC[];
        UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN
        UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(g0:real^3->real^3) x` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ff:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `g0:real^3->real^3`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `oo INTER d0:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER]]]);;

let MOI_S5T_LOCAL_D1 = prove
 (`!u w (d1:real^3->bool) j1 e1 i1 e0 i0 (g1:real^3->real^3) g1' oo
    (gg1:real^3->real^3) (ff:real^3->real^3) ff' (rr:real^3->real^3) q n r e.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d1 j1 /\ d1 SUBSET frontier u /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d1,e1) (g1,g1') /\
     open oo /\ pl_map_on oo gg1 /\ (!x y. x IN oo /\ y IN oo /\ gg1 x = gg1 y ==> x = y) /\
     (!x. x IN oo INTER d1 ==> gg1 x = g1 x) /\ IMAGE gg1 (oo INTER u) SUBSET w /\
     pl_homeomorphism (u,w) (ff,ff') /\ (!x. x IN d1 ==> ff x = g1 (rr x)) /\
     q IN oo INTER (d1 DIFF j1) /\ &0 < r /\ ball(q,r) SUBSET oo /\ ~(n = vec 0) /\
     (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0)) /\
     ball(q,r) INTER frontier u SUBSET d1 /\
     linear e /\ (!z. n dot e z = n dot z) /\ det(matrix e) < &0 /\
     (!x y. e x = e y ==> x = y) /\
     (!x. x IN ball(q,r) INTER frontier u ==> rr x = q + e(x - q) /\ rr x IN oo INTER d1)
     ==> ?x m z mm. x IN interior u /\ moi_s35_lin_at ff x m /\
                    z IN oo /\ moi_s35_lin_at gg1 z mm /\
                    det(matrix m) * det(matrix mm) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior u = inside(frontier u:real^3->bool)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior w = inside(frontier w:real^3->bool)`)) THEN
  SUBGOAL_THEN `(q:real^3) IN d1 /\ ~(q IN j1) /\ q IN oo /\ q IN frontier u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN oo INTER (d1 DIFF j1)` THEN
    UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `q:real^3`; `n:real^3`; `r:real`]
    MOI_S5T_FLAT_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tri"))) THEN
  SUBGOAL_THEN `~(n':real^3 = vec 0) /\ (!z. n' dot (e:real^3->real^3) z = n' dot z)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `?wp:real^3. wp IN frontier w /\ ~(wp IN e1)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e0:real^3->bool`; `i0:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((e0:real^3->bool) DIFF i0 = {})` THEN
    UNDISCH_TAC `(e0:real^3->bool) SUBSET frontier w` THEN
    UNDISCH_TAC `DISJOINT (e0:real^3->bool) e1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg1:real^3->real^3) continuous_on oo` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier w:real^3->bool`; `e1:real^3->bool`; `i1:real^3->bool`;
                 `d1:real^3->bool`; `j1:real^3->bool`; `g1:real^3->real^3`;
                 `g1':real^3->real^3`; `gg1:real^3->real^3`; `oo:real^3->bool`;
                 `q:real^3`; `r:real`; `wp:real^3`] MOI_S5T_PRE_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(q:real^3,rho) SUBSET ball(q,r) /\ ball(q,rho) SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(q:real^3,rho) SUBSET ball(q,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(q:real^3,r)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(q,rho)
                 ==> (&0 < n' dot (x - q) <=> x IN interior u) /\
                     (n' dot (x - q) < &0 <=> ~(x IN u)) /\
                     (n' dot (x - q) = &0 <=> x IN frontier u)` (LABEL_TAC "tr") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "tri" MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(q:real^3,rho) SUBSET ball(q,r)` THEN
    UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (gg1:real^3->real^3) {x | x IN ball(q,rho) /\ n' dot (x - q) < &0}
    SUBSET (:real^3) DIFF w` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_OUTSIDE THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `oo:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gg1:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th) &&
        can (find_term ((=) `oo:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,rho)` THEN UNDISCH_TAC `(y:real^3) IN ball(q,rho)` THEN
      SET_TAC[];
      GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `IMAGE (gg1:real^3->real^3) (oo INTER u) SUBSET w` THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN d1` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `rho:real`)) (concl th) &&
          can (find_term ((=) `frontier w:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN SET_TAC[]];
      SUBGOAL_THEN `(gg1:real^3->real^3) q = g1 q` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `oo INTER d1:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
        GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
          MOI_S5C_HEAD "pl_homeomorphism" th &&
          can (find_term ((=) `g1:real^3->real^3`)) (concl th))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o SPECL [`q:real^3`; `q:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e1:real^3->bool) SUBSET frontier w` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:real^3->real^3` LINEAR_BOUNDED_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?rho2. &0 < rho2 /\ rho2 <= rho /\ bb * rho2 <= rho` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min rho (rho / bb)` THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_MIN_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `bb * rho / bb` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(q,rho2) ==> q + (e:real^3->real^3)(x - q) IN ball(q,rho)`
  (LABEL_TAC "rb") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL; dist;
      VECTOR_ARITH `q - (q + z):real^3 = --z`; NORM_NEG] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `bb * norm(x - q:real^3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `bb * rho2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(q:real^3,rho2) SUBSET ball(q,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `gt = \x:real^3. (gg1:real^3->real^3) (q + (e:real^3->real^3)(x - q))` THEN
  SUBGOAL_THEN `(gt:real^3->real^3) continuous_on ball(q,rho2)` ASSUME_TAC THENL
   [EXPAND_TAC "gt" THEN
    SUBGOAL_THEN `(\x:real^3. (gg1:real^3->real^3) (q + (e:real^3->real^3)(x - q))) =
                  gg1 o (\x. q + e(x - q))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SUBGOAL_THEN `(\x:real^3. (e:real^3->real^3)(x - q)) = e o (\x. x - q)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
                   CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `oo:real^3->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN USE_THEN "rb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x IN ball(q,rho2) /\ y IN ball(q,rho2) /\
                             (gt:real^3->real^3) x = gt y ==> x = y` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN EXPAND_TAC "gt" THEN STRIP_TAC THEN
    SUBGOAL_THEN `q + (e:real^3->real^3)(x - q) = q + e(y - q)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gg1:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th) &&
        can (find_term ((=) `oo:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[VECTOR_ARITH `q + a:real^3 = q + b <=> a = b`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `x - q:real^3 = y - q` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `e:real^3->real^3`)) (concl th) &&
          can (find_term ((=) `y:real^3`)) (concl th) &&
          not(can (find_term ((=) `oo:real^3->bool`)) (concl th)))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(q,rho2) INTER frontier u
                           ==> (ff:real^3->real^3) x = gt x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN ball(q,r) INTER frontier u` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(q:real^3,rho2) SUBSET ball(q,rho)` THEN
      UNDISCH_TAC `ball(q:real^3,rho) SUBSET ball(q,r)` THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,rho2)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME
      `(x:real^3) IN ball(q,r) INTER frontier u`) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `rr:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `ball(q:real^3,r) INTER frontier u`)) (concl th))) THEN
    SUBGOAL_THEN `(x:real^3) IN d1` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(q:real^3,r) INTER frontier u SUBSET d1` THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,r) INTER frontier u` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "gt" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(rr:real^3->real^3) x`)) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(g1:real^3->real^3) (rr (x:real^3))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ff:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `rr:real^3->real^3`)) (concl th) &&
        not(can (find_term ((=) `ball(q:real^3,r) INTER frontier u`)) (concl th)))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `oo INTER d1:real^3->bool`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gt:real^3->real^3) (ball(q,rho2) DIFF u) SUBSET (:real^3) DIFF w`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    EXPAND_TAC "gt" THEN
    SUBGOAL_THEN `(x:real^3) IN ball(q,rho)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(q:real^3,rho2) SUBSET ball(q,rho)` THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,rho2)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(n':real^3) dot (x - q) < &0` ASSUME_TAC THENL
     [USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (gg1:real^3->real^3) {x | x IN ball(q,rho) /\ n' dot (x - q) < &0}
                 SUBSET (:real^3) DIFF w` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "rb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[VECTOR_ARITH `(q + z) - q:real^3 = z`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `n':real^3`; `rho2:real`] MOI_S5T_HALF_PTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `pa:real^3` (X_CHOOSE_THEN `pb:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(pa:real^3) IN ball(q,rho) /\ (pb:real^3) IN ball(q,rho)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(q:real^3,rho2) SUBSET ball(q,rho)` THEN
    UNDISCH_TAC `(pa:real^3) IN ball(q,rho2)` THEN UNDISCH_TAC `(pb:real^3) IN ball(q,rho2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real^3->real^3) continuous_on u /\
                (!x y. x IN u /\ y IN u /\ ff x = ff y ==> x = y) /\
                IMAGE ff u SUBSET w /\ pl_map_on u ff` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `ff:real^3->real^3`)) (concl th))) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
       [`!x. x IN u ==> (ff':real^3->real^3) ((ff:real^3->real^3) x) = x`] THEN
      MESON_TAC[];
      UNDISCH_TAC `IMAGE (ff:real^3->real^3) u = w` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:real^3->real^3`; `u:real^3->bool`;
                 `ball(q:real^3,rho2) INTER interior u`] MOI_S5T_LIN_AT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR];
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `pa:real^3` THEN
      REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(pa:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x1:real^3` (X_CHOOSE_THEN `m1:real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `open (IMAGE (\x:real^3. q + (e:real^3->real^3)(x - q))
                       (ball(q,rho2) DIFF u))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SUBGOAL_THEN `(\x:real^3. (e:real^3->real^3)(x - q)) = e o (\x. x - q)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
                   CONTINUOUS_ON_CONST];
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_BALL];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `x - q:real^3 = y - q` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `e:real^3->real^3`)) (concl th) &&
          can (find_term ((=) `y:real^3`)) (concl th) &&
          not(can (find_term ((=) `oo:real^3->bool`)) (concl th)) &&
          not(can (find_term ((=) `rho2:real`)) (concl th)))) THEN
        UNDISCH_TAC `q + (e:real^3->real^3)(x - q) = q + e(y - q)` THEN VECTOR_ARITH_TAC;
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg1:real^3->real^3`; `oo:real^3->bool`;
                 `IMAGE (\x:real^3. q + (e:real^3->real^3)(x - q)) (ball(q,rho2) DIFF u)`]
    MOI_S5T_LIN_AT_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN USE_THEN "rb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `pb:real^3` THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME `(pb:real^3) IN ball(q,rho)`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^3` (X_CHOOSE_THEN `mm1:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC o
    REWRITE_RULE[IN_IMAGE] o check (fun th ->
      can (find_term ((=) `z1:real^3`)) (concl th) && not(is_forall(concl th)) &&
      MOI_S5C_HEAD "IN" th)) THEN
  MAP_EVERY EXISTS_TAC [`x1:real^3`; `m1:real^3->real^3`; `z1:real^3`;
                        `mm1:real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(x1:real^3) IN ball(q,rho2) INTER interior u` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `z1:real^3`)) THEN
    UNDISCH_TAC `ball(q:real^3,rho) SUBSET oo` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "rb" MATCH_MP_TAC THEN
    UNDISCH_TAC `(y1:real^3) IN ball(q,rho2) DIFF u` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_lin_at (gt:real^3->real^3) y1 ((mm1:real^3->real^3) o e)`
  ASSUME_TAC THENL
   [EXPAND_TAC "gt" THEN MATCH_MP_TAC MOI_S5T_LIN_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `z1:real^3`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(matrix(m1:real^3->real^3)) *
                     det(matrix((mm1:real^3->real^3) o e))` MP_TAC THENL
   [MATCH_MP_TAC MOI_S5T_HTRICK THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `w:real^3->bool`; `ff:real^3->real^3`;
                          `gt:real^3->real^3`; `q:real^3`; `rho2:real`; `x1:real^3`;
                          `y1:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(mm1:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_lin_at (gg1:real^3->real^3) z1 mm1` THEN
    SIMP_TAC[moi_s35_lin_at];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL] THEN
  UNDISCH_TAC `det(matrix(e:real^3->real^3)) < &0` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SPEC_TAC(`det(matrix(e:real^3->real^3))`,`c:real`) THEN
  SPEC_TAC(`det(matrix(m1:real^3->real^3)) * det(matrix(mm1:real^3->real^3))`,`a:real`) THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* B10: the reflected extension contradicts moi_s35_same_orient.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_BAD_CONTRA = prove
 (`!u w (d0:real^3->bool) j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0' g1 g1'
    o0 o1 (gg0:real^3->real^3) gg1 (ff:real^3->real^3) ff' (rr:real^3->real^3) q n r e.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0') /\ pl_homeomorphism (d1,e1) (g1,g1') /\
     open o0 /\ open o1 /\ ~(o0 INTER (d0 DIFF j0) = {}) /\
     pl_map_on o0 gg0 /\ (!x y. x IN o0 /\ y IN o0 /\ gg0 x = gg0 y ==> x = y) /\
     pl_map_on o1 gg1 /\ (!x y. x IN o1 /\ y IN o1 /\ gg1 x = gg1 y ==> x = y) /\
     (!x. x IN o0 INTER d0 ==> gg0 x = g0 x) /\
     (!x. x IN o1 INTER d1 ==> gg1 x = g1 x) /\
     IMAGE gg0 (o0 INTER u) SUBSET w /\ IMAGE gg1 (o1 INTER u) SUBSET w /\
     moi_s35_same_orient gg0 o0 gg1 o1 /\
     pl_homeomorphism (u,w) (ff,ff') /\ (!x. x IN d0 ==> ff x = g0 x) /\
     (!x. x IN d1 ==> ff x = g1 (rr x)) /\
     q IN o1 INTER (d1 DIFF j1) /\ &0 < r /\ ball(q,r) SUBSET o1 /\ ~(n = vec 0) /\
     (!x. x IN ball(q,r) ==> (x IN frontier u <=> n dot (x - q) = &0)) /\
     ball(q,r) INTER frontier u SUBSET d1 /\
     linear e /\ (!z. n dot e z = n dot z) /\ det(matrix e) < &0 /\
     (!x y. e x = e y ==> x = y) /\
     (!x. x IN ball(q,r) INTER frontier u ==> rr x = q + e(x - q) /\ rr x IN o1 INTER d1)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                 `d1:real^3->bool`; `j1:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
                 `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`;
                 `g0':real^3->real^3`; `o0:real^3->bool`; `gg0:real^3->real^3`;
                 `ff:real^3->real^3`; `ff':real^3->real^3`] MOI_S5T_LOCAL_D0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `m0:real^3->real^3`
    (X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `mm0:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`;
                 `e1:real^3->bool`; `i1:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
                 `g1:real^3->real^3`; `g1':real^3->real^3`; `o1:real^3->bool`;
                 `gg1:real^3->real^3`; `ff:real^3->real^3`; `ff':real^3->real^3`;
                 `rr:real^3->real^3`; `q:real^3`; `n:real^3`; `r:real`;
                 `e:real^3->real^3`] MOI_S5T_LOCAL_D1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3` (X_CHOOSE_THEN `m1:real^3->real^3`
    (X_CHOOSE_THEN `z1:real^3` (X_CHOOSE_THEN `mm1:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior u = inside(frontier u:real^3->bool)`)) THEN
  SUBGOAL_THEN `(ff:real^3->real^3) continuous_on u /\
                (!x y. x IN u /\ y IN u /\ ff x = ff y ==> x = y)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `ff:real^3->real^3`)) (concl th))) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x. x IN u ==> (ff':real^3->real^3) ((ff:real^3->real^3) x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(matrix(m0:real^3->real^3)) * det(matrix(m1:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LOCAL_SIGN THEN
    MAP_EVERY EXISTS_TAC [`ff:real^3->real^3`; `interior u:real^3->bool`; `x0:real^3`;
                          `x1:real^3`] THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ff:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `y:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `u:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN interior u` THEN UNDISCH_TAC `(y:real^3) IN interior u` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(matrix(mm0:real^3->real^3)) * det(matrix(mm1:real^3->real^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_same_orient gg0 o0 gg1 o1` THEN REWRITE_TAC[moi_s35_same_orient] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y0:real^3`; `z1:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`det(matrix(m0:real^3->real^3))`; `det(matrix(mm0:real^3->real^3))`;
                 `det(matrix(m1:real^3->real^3))`] MOI_S5T_SIGN3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`det(matrix(mm0:real^3->real^3))`; `det(matrix(m1:real^3->real^3))`;
                 `det(matrix(mm1:real^3->real^3))`] MOI_S5T_SIGN3) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `det(matrix(m1:real^3->real^3)) * det(matrix(mm1:real^3->real^3)) < &0` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* B11: gluing along the annulus between the two disks; TWO_DISK_EXT.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S5T_GLUE_ANNULUS = prove
 (`!u (d0:real^3->bool) j0 d1 j1 (phi:real^2->real^3) phi' (pp:real^2->real^2) pp'
    (kk:real^3->real^3) kk'.
     pl_ball 3 u /\ pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(frontier u DIFF (d0 UNION d1)) UNION j0 UNION j1) (phi,phi') /\
     j1 = IMAGE phi (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\ j0 = IMAGE phi (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
     pl_homeomorphism ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])),(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))) (pp,pp') /\ (!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> pp x = x) /\
     IMAGE pp (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
     pl_homeomorphism (d1,d1) (kk,kk') /\ (!c. c IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> phi (pp c) = kk (phi c))
     ==> ?k k'. pl_homeomorphism (frontier u,frontier u) (k,k') /\
                (!x. x IN d0 ==> k x = x) /\ (!x. x IN d1 ==> k x = kk x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j0:real^3->bool) SUBSET d0 /\ compact d0` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
      (ASSUME `pl_cell_with_boundary 2 (d0:real^3->bool) j0`)) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET d1 /\ compact d1` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
      (ASSUME `pl_cell_with_boundary 2 (d1:real^3->bool) j1`)) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (d0:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
    MAP_EVERY EXISTS_TAC [`2`; `j0:real^3->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `aa = (frontier u DIFF (d0 UNION d1)) UNION j0 UNION (j1:real^3->bool)` THEN
  FIRST_ASSUM(LABEL_TAC "fp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `closed (aa:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (phi:real^2->real^3) (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) = aa` (SUBST1_TAC o SYM) THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
        check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
          can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
      SIMP_TAC[homeomorphism];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
        check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
          can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
      SIMP_TAC[homeomorphism];
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\ (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5W_C_SUB_MM]; ALL_TAC] THEN
  SUBGOAL_THEN `d0 INTER aa = j0 /\ aa INTER d1 = j1:real^3->bool` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN
    MAP_EVERY UNDISCH_TAC [`(j0:real^3->bool) SUBSET d0`; `(j1:real^3->bool) SUBSET d1`;
                           `DISJOINT (d0:real^3->bool) d1`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d0 INTER d1 = {}:real^3->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (d0:real^3->bool) d1` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN j0 ==> ((phi:real^2->real^3) o (pp:real^2->real^2) o
                                         (phi':real^3->real^2)) x = x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th =
      `j0 = IMAGE (phi:real^2->real^3) (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` ASSUME_TAC THENL
     [UNDISCH_TAC `(relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fp" (MP_TAC o REWRITE_RULE[ASSUME `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] o CONJUNCT1 o
      SPECL [`c:real^2`; `vec 0:real^3`]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `!x. x IN (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) ==> (pp:real^2->real^2) x = x` THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^2. c IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> ((phi:real^2->real^3) o (pp:real^2->real^2) o
                  (phi':real^3->real^2)) (phi c) = phi (pp c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` ASSUME_TAC THENL
     [UNDISCH_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fp" (MP_TAC o REWRITE_RULE[ASSUME `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] o CONJUNCT1 o
      SPECL [`c:real^2`; `vec 0:real^3`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d0:real^3->bool`; `aa:real^3->bool`; `d1:real^3->bool`;
                 `d0:real^3->bool`; `aa:real^3->bool`; `d1:real^3->bool`;
                 `j0:real^3->bool`; `j1:real^3->bool`; `j0:real^3->bool`;
                 `j1:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`;
                 `((phi:real^2->real^3) o (pp:real^2->real^2)) o (phi':real^3->real^2)`;
                 `(phi:real^2->real^3) o (pp':real^2->real^2) o (phi':real^3->real^2)`;
                 `kk:real^3->real^3`; `kk':real^3->real^3`] MOI_S5E_GLUE3) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                  GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[GSYM o_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:real^3` THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
        `j1 = IMAGE (phi:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[GSYM o_ASSOC] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IMAGE_ID];
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th =
        `j1 = IMAGE (phi:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)) THEN
      REWRITE_TAC[GSYM IMAGE_o; GSYM o_ASSOC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE ((phi:real^2->real^3) o (pp:real^2->real^2)) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!f g (s:real^2->bool).
           (!x. x IN s ==> (f:real^2->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        SUBGOAL_THEN `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` ASSUME_TAC THENL
         [UNDISCH_TAC `(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) SUBSET (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))` THEN UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
          SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "fp" (MP_TAC o REWRITE_RULE[ASSUME `(c:real^2) IN (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`] o CONJUNCT1 o
          SPECL [`c:real^2`; `vec 0:real^3`]) THEN
        SIMP_TAC[];
        ASM_REWRITE_TAC[IMAGE_o]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d0 UNION aa UNION d1 = frontier u:real^3->bool` SUBST1_TAC THENL
   [EXPAND_TAC "aa" THEN
    MAP_EVERY UNDISCH_TAC [`(d0:real^3->bool) SUBSET frontier u`;
                           `(d1:real^3->bool) SUBSET frontier u`;
                           `(j0:real^3->bool) SUBSET d0`; `(j1:real^3->bool) SUBSET d1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

let MOI_S5T_RESTRICT_GEN = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s' t'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ pl_polyhedron s' /\ IMAGE f s' = t'
     ==> pl_homeomorphism (s',t') (f,g)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S5T_TAU_C1 = prove
 (`IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
    REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `vector[(y:real^2)$2; y$1]:real^2` THEN
    REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      UNDISCH_TAC `(y:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
      REAL_ARITH_TAC]]);;

let TWO_DISK_EXT = prove
 (MOI_S35_TWO_DISK_EXT,
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `w:real^3->bool`; `d0:real^3->bool`;
    `j0:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`; `e0:real^3->bool`;
    `i0:real^3->bool`; `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`;
    `g0':real^3->real^3`; `g1:real^3->real^3`; `g1':real^3->real^3`; `o0:real^3->bool`;
    `o1:real^3->bool`; `gg0:real^3->real^3`; `gg1:real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (u:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S5T_BALL_SIDES (ASSUME `pl_ball 3 (w:real^3->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior u = inside(frontier u:real^3->bool)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `interior w = inside(frontier w:real^3->bool)`)) THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET d1` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
      (ASSUME `pl_cell_with_boundary 2 (d1:real^3->bool) j1`)) THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `frontier w:real^3->bool`; `d0:real^3->bool`;
    `j0:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`; `e0:real^3->bool`;
    `i0:real^3->bool`; `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`;
    `g0':real^3->real^3`] MOI_S5E_SPHERE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(LABEL_TAC "hp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `h:real^3->real^3`)) (concl th))) THEN
  FIRST_ASSUM(LABEL_TAC "g1p" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `g1:real^3->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `pl_homeomorphism (e1,d1) ((h':real^3->real^3),h)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_RESTRICT_GEN THEN
    MAP_EVERY EXISTS_TAC [`frontier w:real^3->bool`; `frontier u:real^3->bool`] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC [`2`; `i1:real^3->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (h:real^3->real^3) d1 = e1`)) THEN
      REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) d1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!f g (s:real^3->bool).
           (!x. x IN s ==> (f:real^3->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
         [UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN
          UNDISCH_TAC `(x:real^3) IN d1` THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "hp" (MP_TAC o REWRITE_RULE[ASSUME `(x:real^3) IN frontier u`] o
          CONJUNCT1 o SPECL [`x:real^3`; `x:real^3`]) THEN SIMP_TAC[];
        REWRITE_TAC[IMAGE_ID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (d1,d1) ((h':real^3->real^3) o (g1:real^3->real^3),
                                         (g1':real^3->real^3) o (h:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `e1:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rho = (h':real^3->real^3) o (g1:real^3->real^3)` THEN
  ABBREV_TAC `rho' = (g1':real^3->real^3) o (h:real^3->real^3)` THEN
  SUBGOAL_THEN `!x. x IN d1 ==> (h:real^3->real^3) ((rho:real^3->real^3) x) = g1 x`
  (LABEL_TAC "hrho") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "rho" THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "g1p" (MP_TAC o REWRITE_RULE[ASSUME `(x:real^3) IN d1`] o CONJUNCT1 o
      SPECL [`x:real^3`; `x:real^3`]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g1:real^3->real^3) x IN frontier w` ASSUME_TAC THENL
     [UNDISCH_TAC `(e1:real^3->bool) SUBSET frontier w` THEN
      UNDISCH_TAC `(g1:real^3->real^3) x IN e1` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "hp" (MP_TAC o REWRITE_RULE[ASSUME `(g1:real^3->real^3) x IN frontier w`] o
      CONJUNCT2 o SPECL [`x:real^3`; `(g1:real^3->real^3) x`]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (rho:real^3->real^3) j1 = j1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5E_PLH_CELL_BOUNDARY THEN
    MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d1:real^3->bool`; `rho':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                 `d1:real^3->bool`; `j1:real^3->bool`] MOI_S5E_SPHERE_ANNULUS) THEN
  ASM_REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^3` (X_CHOOSE_THEN `phi':real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
      (ASSUME_TAC o SYM))))) THEN
  FIRST_ASSUM(LABEL_TAC "fp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      MOI_S5C_HEAD "pl_homeomorphism" th &&
      can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
  ABBREV_TAC `aa = (frontier u DIFF (d0 UNION d1)) UNION j0 UNION (j1:real^3->bool)` THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET aa` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),j1) ((phi:real^2->real^3),phi')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_RESTRICT_GEN THEN
    MAP_EVERY EXISTS_TAC [`(interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1]))`; `aa:real^3->bool`] THEN
    ASM_REWRITE_TAC[MOI_S5W_C_SUB_MM; MOI_S5W_MM_POLY];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (j1:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
    MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN EXISTS_TAC `d1:real^3->bool` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j1,j1) ((rho:real^3->real^3),rho')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5T_RESTRICT_GEN THEN
    MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d1:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism ((relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])),(relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))
      ((phi':real^3->real^2) o (rho:real^3->real^3) o (phi:real^2->real^3),
       ((phi':real^3->real^2) o (rho':real^3->real^3)) o (phi:real^2->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j1:real^3->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j1:real^3->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `gam = (phi':real^3->real^2) o (rho:real^3->real^3) o (phi:real^2->real^3)` THEN
  ABBREV_TAC `gam' = ((phi':real^3->real^2) o (rho':real^3->real^3)) o
                     (phi:real^2->real^3)` THEN
  SUBGOAL_THEN `!c. c IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) ==> (phi:real^2->real^3) ((gam:real^2->real^2) c) =
                                  (rho:real^3->real^3) (phi c)` (LABEL_TAC "pg") THENL
   [X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN EXPAND_TAC "gam" THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(rho:real^3->real^3) ((phi:real^2->real^3) c) IN aa` ASSUME_TAC THENL
     [UNDISCH_TAC `(j1:real^3->bool) SUBSET aa` THEN
      UNDISCH_TAC `IMAGE (rho:real^3->real^3) j1 = j1` THEN
      UNDISCH_TAC `IMAGE (phi:real^2->real^3) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = j1` THEN
      UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fp" (MP_TAC o REWRITE_RULE[ASSUME
      `(rho:real^3->real^3) ((phi:real^2->real^3) c) IN aa`] o CONJUNCT2 o
      SPECL [`vec 0:real^2`; `(rho:real^3->real^3) ((phi:real^2->real^3) c)`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gam:real^2->real^2) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])) = (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> MOI_S5C_HEAD "pl_homeomorphism" th &&
        can (find_term ((=) `gam:real^2->real^2`)) (concl th))) THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^2->real^2`; `gam':real^2->real^2`] MOI_S5W_DICHOTOMY_EXT) THEN
  ASM_REWRITE_TAC[moi_s5w_ext] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `pp:real^2->real^2`
    (X_CHOOSE_THEN `pp':real^2->real^2` STRIP_ASSUME_TAC))) THENL
   [MP_TAC(ISPECL [`u:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                   `d1:real^3->bool`; `j1:real^3->bool`; `phi:real^2->real^3`;
                   `phi':real^3->real^2`; `pp:real^2->real^2`; `pp':real^2->real^2`;
                   `rho:real^3->real^3`; `rho':real^3->real^3`] MOI_S5T_GLUE_ANNULUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (gam:real^2->real^2) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN
        CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
        MATCH_MP_TAC(SET_RULE `!f g (s:real^2->bool).
           (!x. x IN s ==> (f:real^2->real^2) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(pp:real^2->real^2) c = gam c` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `pp:real^2->real^2`)) (concl th) &&
            can (find_term ((=) `gam:real^2->real^2`)) (concl th))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          USE_THEN "pg" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->real^3` (X_CHOOSE_THEN `k':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`;
                   `(h:real^3->real^3) o (k:real^3->real^3)`;
                   `(k':real^3->real^3) o (h':real^3->real^3)`] MOI_SCD_COR_EXTEND_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `frontier u:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
       [UNDISCH_TAC `(d0:real^3->bool) SUBSET frontier u` THEN
        UNDISCH_TAC `(x:real^3) IN d0` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM];
      SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
       [UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN
        UNDISCH_TAC `(x:real^3) IN d1` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM] THEN USE_THEN "hrho" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MP_TAC(ISPECL [`u:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`;
                   `d0:real^3->bool`; `j0:real^3->bool`; `phi:real^2->real^3`;
                   `phi':real^3->real^2`; `o1:real^3->bool`] MOI_S5T_REFLECTION_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `R':real^3->real^3`
      (X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `r:real`
        (X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC)))))) THEN
    FIRST_ASSUM(LABEL_TAC "Rp" o MATCH_MP MOI_S5W_HOMEO_PTS o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        MOI_S5C_HEAD "pl_homeomorphism" th &&
        can (find_term ((=) `R:real^3->real^3`)) (concl th))) THEN
    MP_TAC(ISPECL [`u:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
                   `d1:real^3->bool`; `j1:real^3->bool`; `phi:real^2->real^3`;
                   `phi':real^3->real^2`; `pp:real^2->real^2`; `pp':real^2->real^2`;
                   `(rho:real^3->real^3) o (R:real^3->real^3)`;
                   `(R':real^3->real^3) o (rho':real^3->real^3)`] MOI_S5T_GLUE_ANNULUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `IMAGE (gam:real^2->real^2) (IMAGE (\x:real^2. vector[x$2; x$1]:real^2) (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])))` THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM IMAGE_o] THEN
          MATCH_MP_TAC(SET_RULE `!f g (s:real^2->bool).
             (!x. x IN s ==> (f:real^2->real^2) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
          X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `pp:real^2->real^2`)) (concl th) &&
            can (find_term ((=) `gam:real^2->real^2`)) (concl th))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[MOI_S5T_TAU_C1] THEN FIRST_ASSUM ACCEPT_TAC];
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d1:real^3->bool` THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        SUBGOAL_THEN `vector[(c:real^2)$2; c$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` ASSUME_TAC THENL
         [UNDISCH_TAC `(c:real^2) IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))` THEN REWRITE_TAC[MOI_S5C_IN_RF1; VECTOR_2] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(pp:real^2->real^2) c = (gam:real^2->real^2) (vector[c$2; c$1])`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `pp:real^2->real^2`)) (concl th) &&
            can (find_term ((=) `gam:real^2->real^2`)) (concl th))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        USE_THEN "pg" (fun th -> REWRITE_TAC[MATCH_MP th
          (ASSUME `vector[(c:real^2)$2; c$1] IN (relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`)]) THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `R:real^3->real^3`)) (concl th) &&
          can (find_term ((=) `phi:real^2->real^3`)) (concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->real^3` (X_CHOOSE_THEN `k':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`;
                   `(h:real^3->real^3) o (k:real^3->real^3)`;
                   `(k':real^3->real^3) o (h':real^3->real^3)`] MOI_SCD_COR_EXTEND_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `frontier u:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:real^3->real^3` (X_CHOOSE_THEN `ff':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC MOI_S5T_BAD_CONTRA THEN
    MAP_EVERY EXISTS_TAC
     [`u:real^3->bool`; `w:real^3->bool`; `d0:real^3->bool`; `j0:real^3->bool`;
      `d1:real^3->bool`; `j1:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
      `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`;
      `g1:real^3->real^3`; `g1':real^3->real^3`; `o0:real^3->bool`; `o1:real^3->bool`;
      `gg0:real^3->real^3`; `gg1:real^3->real^3`; `ff:real^3->real^3`;
      `ff':real^3->real^3`; `R:real^3->real^3`; `q:real^3`; `n:real^3`; `r:real`;
      `e:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
       [UNDISCH_TAC `(d0:real^3->bool) SUBSET frontier u` THEN
        UNDISCH_TAC `(x:real^3) IN d0` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM];
      SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
       [UNDISCH_TAC `(d1:real^3->bool) SUBSET frontier u` THEN
        UNDISCH_TAC `(x:real^3) IN d1` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM] THEN USE_THEN "hrho" MATCH_MP_TAC THEN
      USE_THEN "Rp" (MP_TAC o REWRITE_RULE[ASSUME `(x:real^3) IN d1`] o CONJUNCT1 o
        SPECL [`x:real^3`; `x:real^3`]) THEN SIMP_TAC[]]]);;

