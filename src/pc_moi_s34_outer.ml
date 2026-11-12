needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_sch3_s2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s34_outer: the outer source cells of the Sec 34 cell diagram at   *)
(* the boundary of kk (Moise, Geometric Topology in Dimensions 2 and 3,     *)
(* GTM 47, Sec 34, p.244-245; the cells of K UNION N outside |kk|), i.e.   *)
(* clauses 7-8 of moi_s34_scell_facts, collected as moi_s4a_outer in        *)
(* pc_moi_s34_scella.ml.  Main theorems:                                     *)
(*   OUTER_CELLS  !tt kk. moi_s34_tube tt kk ==> moi_s4a_outer tt kk        *)
(*   SCELL_A      = MOI_S34_SCELL_A (from MOI_S4A_SCELL_A_FROM_OUTER)       *)
(* Route.  Fix a boundary vertex v of kk and the level homeomorphism h of   *)
(* the closed star of v in the first barycentric subdivision t1 of tt       *)
(* (MOI_FTA_THETA): h maps the vertex ball C_v onto the region where an     *)
(* affine level function is at least 1/2, simplexwise, and the boundary     *)
(* sphere S of C_v onto a surface met once by each ray from v.             *)
(* Clause 8: the rim of the splitting disk of a boundary edge e = [v,w] is  *)
(* mapped onto the half-scaled copy (centre the midpoint b of e) of the     *)
(* link circle K of b in the link of v; K meets |kk| in an arc whose ends  *)
(* are the barycentres of the two boundary triangles at e, so its closed   *)
(* complement is an arc with the same ends.                                 *)
(* Clause 7: the trace c of h(S) on the cone over the link circle J of v   *)
(* in the boundary surface is a PL circle (radial recognition in the plane  *)
(* through a cone chart); the cone from v over c with the outer halves of   *)
(* the splitting disks of the boundary edges glued on is a PL disk whose   *)
(* boundary is h of the stated boundary B of the outer patch P, so B is a  *)
(* PL circle; B splits the PL 2-sphere S into two disks (SPHERE_SPLIT moved *)
(* into real^N) and P is the one off |kk|.                                   *)
(* First, generic tools (spheres and circles in real^N).                     *)
(* ========================================================================= *)

(* OCaml helper for assumption selection: does a theorem mention the named *)
(* constant?                                                                 *)

let moi_s4o_has_const name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* The boundary of a PL (n+1)-cell is a PL n-sphere; PL spheres are        *)
(* compact polyhedra.                                                       *)

let MOI_S4O_CELL_SPHERE = prove
 (`!n (c:real^N->bool) b.
     pl_cell_with_boundary (n + 1) c b ==> pl_sphere n b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_sphere] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `c:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `k:real^N->bool` CLOSURE_SUBSET) THEN
    SUBGOAL_THEN `closure(k:real^N->bool) = k` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED]; SET_TAC[]];
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

let MOI_S4O_SPHERE_POLY = prove
 (`!n s:real^N->bool. pl_sphere n s ==> pl_polyhedron s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `s:real^N->bool`)) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

(* SPHERE_SPLIT (pc_moi_sch3_s2, real^3) moved into real^N along a PL     *)
(* homeomorphism of the sphere with the boundary of a 3-simplex of real^3. *)

let MOI_S4O_SPHERE_SPLIT = prove
 (`!s j:real^N->bool.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET s
     ==> ?d1 d2. pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
                 d1 UNION d2 = s /\ d1 INTER d2 = j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_sphere])
    STRIP_ASSUME_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `vec 0:real^3` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k3:real^3->bool`; `k:real^N->bool`; `&3:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `G = (f:real^N->real^N) o (p:real^3->real^N)` THEN
  ABBREV_TAC `G' = (q:real^N->real^3) o (g:real^N->real^N)` THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier k3,s:real^N->bool) ((G:real^3->real^N),(G':real^N->real^3))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "G'"] THEN
    MATCH_MP_TAC(ISPECL [`relative_frontier k3:real^3->bool`;
       `relative_frontier k:real^N->bool`; `s:real^N->bool`;
       `p:real^3->real^N`; `q:real^N->real^3`; `f:real^N->real^N`;
       `g:real^N->real^N`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (j:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4O_SPHERE_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j:real^N->bool,IMAGE (G':real^N->real^3) j) (G',(G:real^3->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`s:real^N->bool`; `relative_frontier k3:real^3->bool`;
       `G':real^N->real^3`; `G:real^3->real^N`; `j:real^N->bool`]
       MOI_FMB_PLH_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> can (find_term ((=) `relative_frontier (k3:real^3->bool)`))
                         (concl th) &&
                     can (find_term ((=) `G:real^3->real^N`)) (concl th) &&
                     can (find_term ((=) `s:real^N->bool`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (G':real^N->real^3) j SUBSET relative_frontier k3`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (G':real^N->real^3) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`j:real^N->bool`; `IMAGE (G':real^N->real^3) j`;
       `G':real^N->real^3`; `G:real^3->real^N`; `1`] MOI_FM3_PL_SPHERE_TRANSFER) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k3:real^3->bool`;
                 `IMAGE (G':real^N->real^3) j`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[ARITH_RULE `2 + 1 = 3`]
      (SPEC `2` PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_SIMPLEX) THEN
    DISCH_THEN(MP_TAC o SPEC `&3:int`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^3->bool. pl_cell_with_boundary 2 e (IMAGE (G':real^N->real^3) (j:real^N->bool)) /\
                     e SUBSET relative_frontier k3
                     ==> pl_cell_with_boundary 2 (IMAGE (G:real^3->real^N) e) j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j = IMAGE (G:real^3->real^N) (IMAGE (G':real^N->real^3) (j:real^N->bool))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(GSYM MOI_FTA_IMAGE_ID_ON) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k3:real^3->bool`; `s:real^N->bool`;
                          `G':real^N->real^3`] THEN
    ASM_SIMP_TAC[MOI_SS2_FSA_OF_CELL];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (G:real^3->real^N) e1`;
                        `IMAGE (G:real^3->real^N) e2`] THEN
  SUBGOAL_THEN `(e1:real^3->bool) SUBSET relative_frontier k3 /\
                e2 SUBSET relative_frontier k3` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM IMAGE_UNION];
    MP_TAC(ISPECL [`G:real^3->real^N`; `G':real^N->real^3`;
                   `relative_frontier k3:real^3->bool`;
                   `e1:real^3->bool`; `e2:real^3->bool`] MOI_SS2_INJ_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC MOI_FTA_IMAGE_ID_ON THEN ASM SET_TAC[]]);;
(* MOI_FTA_RAY_COUNT (pc_moi_fnd_tubea) generalized from real^3 to real^M  *)
(* (same proof).                                                             *)

let MOI_S4O_RAY_COUNT = prove
 (`!(S:real^M->bool) (C:real^N->bool) L X (p:real^N->real^M) q b v.
        convex S /\ compact S /\ b IN relative_interior S /\
        affine hull S = (:real^M) /\
        IMAGE p C = S /\ (!x. x IN C ==> q(p x) = x) /\
        X SUBSET C /\ IMAGE p L = relative_frontier S /\
        (!y r. y IN L /\ &0 <= r /\ r <= &1
               ==> v + r % (y - v) IN C /\
                   p(v + r % (y - v)) = b + r % (p y - b)) /\
        (!y. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X)
        ==> !u. ~(u = vec 0) ==> ?!r. &0 < r /\ b + r % u IN IMAGE p X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `b:real^M`; `u:real^M`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y:real^N. y IN L /\ (p:real^N->real^M) y = b + dd % u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `b + dd % u IN relative_frontier (S:real^M->bool)` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [SYM (check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `relative_frontier (S:real^M->bool)`) th)]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->real^M) y - b = dd % u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "rad" o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `C:real^N->bool`)) (concl th) &&
    can (find_term ((=) `b:real^M`)) (concl th))) THEN
  SUBGOAL_THEN
   `!r. &0 < r /\ r <= dd
        ==> v + (r / dd) % (y - v) IN C /\
            b + r % u = (p:real^N->real^M)(v + (r / dd) % (y - v))`
  (LABEL_TAC "mid") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= r / dd /\ r / dd <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "rad" (MP_TAC o SPECL [`y:real^N`; `r / dd`]) THEN
    REWRITE_TAC[ASSUME `(y:real^N) IN L`; ASSUME `&0 <= r / dd`;
                ASSUME `r / dd <= &1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 < r /\ b + r % u IN IMAGE (p:real^N->real^M) X
        ==> r <= dd /\ v + (r / dd) % (y - v) IN X`
  (LABEL_TAC "back") THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `r <= dd` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`S:real^M->bool`; `b:real^M`; `u:real^M`; `dd:real`;
                     `r:real`] MOI_FTA_RAY_BEYOND) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `b + r % u:real^M`)) THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM(check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `S:real^M->bool`) th)]) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
      REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "mid" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `x:real^N = v + (r / dd) % (y - v)` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(x:real^N) IN C` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(q:real^M->real^N) (p (x:real^N)) = x /\
      q (p (v + (r / dd) % (y - v))) = v + (r / dd) % (y - v)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `b + r % u = (p:real^N->real^M) x` THEN
    UNDISCH_TAC `b + r % u = (p:real^N->real^M) (v + r / dd % (y - v))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `X:real^N->bool`)) (concl th) &&
    not (can (find_term ((=) `C:real^N->bool`)) (concl th)))) THEN
  REWRITE_TAC[ASSUME `(y:real^N) IN L`; EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    MP_TAC)) THEN
  DISCH_THEN(fun uniq ->
    REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `s0 * dd:real` THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      USE_THEN "mid" (MP_TAC o SPEC `s0 * dd:real`) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL] THEN
        REWRITE_TAC[REAL_ARITH `s * d <= d <=> &0 <= (&1 - s) * d`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < d ==> (s * d) / d = s`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "back" (MP_TAC o SPEC `r:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(SPEC `r / dd` uniq) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]));;

(* A restatement of MOI_S5C_CONVEX_CONE_RF (pc_moi_s35_minc.ml, not in     *)
(* the load closure of this file).                                         *)

let MOI_S4O_CONVEX_CONE_RF = prove
 (`!t (b:real^N).
     convex t /\ compact t /\ b IN relative_interior t /\ ~(t = {b})
     ==> ~(b IN relative_frontier t) /\
         (!x y. x IN relative_frontier t /\ y IN relative_frontier t /\
                y IN segment[b,x] ==> y = x) /\
         UNIONS {segment[b,x] | x IN relative_frontier t} = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_CON_RF_SEGMENT];
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `segment[b:real^N,x] SUBSET t` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; relative_frontier;
                      IN_DIFF; COMPACT_IMP_CLOSED; CLOSURE_CLOSED];
        ASM SET_TAC[]];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `b:real^N`; `y:real^N`]
        SEGMENT_TO_RELATIVE_FRONTIER) THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN MESON_TAC[]]]);;

(* Radial recognition of PL circles: a compact polyhedron in the cone from *)
(* v over a radially simple PL circle J, avoiding v and met exactly once   *)
(* by each segment from v to J, is a PL circle (cone chart onto a triangle *)
(* of real^2 and MOI_CMB_STAR_SHAPED_PL_SPHERE_0 there).                    *)

let MOI_S4O_RADIAL_CIRCLE = prove
 (`!(J:real^N->bool) v X.
     pl_sphere 1 J /\ ~(v IN J) /\
     (!x y. x IN J /\ y IN J /\ y IN segment[v,x] ==> y = x) /\
     pl_polyhedron X /\ ~(v IN X) /\
     X SUBSET UNIONS {segment[v,y] | y IN J} /\
     (!y. y IN J ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN X)
     ==> pl_sphere 1 X`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_sphere])
    STRIP_ASSUME_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `vec 0:real^2` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  REWRITE_TAC[DIMINDEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `T2:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`T2:real^2->bool`; `k:real^N->bool`; `&2:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^N` (X_CHOOSE_THEN `q:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `G = (f:real^N->real^N) o (p:real^2->real^N)` THEN
  ABBREV_TAC `G' = (q:real^N->real^2) o (g:real^N->real^N)` THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier T2,J:real^N->bool)
                  ((G:real^2->real^N),(G':real^N->real^2))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "G'"] THEN
    MATCH_MP_TAC(ISPECL [`relative_frontier T2:real^2->bool`;
       `relative_frontier k:real^N->bool`; `J:real^N->bool`;
       `p:real^2->real^N`; `q:real^N->real^2`; `f:real^N->real^N`;
       `g:real^N->real^N`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(T2:real^2->bool) /\ compact T2 /\
                vec 0 IN relative_interior T2 /\ ~(T2 = {vec 0}) /\
                affine hull T2 = (:real^2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `vec 0 IN interior {vec 0:real^2}` THEN
      REWRITE_TAC[INTERIOR_SING; NOT_IN_EMPTY];
      MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T2:real^2->bool`; `vec 0:real^2`] MOI_S4O_CONVEX_CONE_RF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron(relative_frontier T2:real^2->bool) /\
                ~(relative_frontier T2:real^2->bool = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      DISCH_TAC THEN
      UNDISCH_TAC `UNIONS {segment[vec 0:real^2,x] | x IN relative_frontier T2} = T2` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `UNIONS {segment[vec 0:real^2,x] | x IN ({}:real^2->bool)} = {}`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `vec 0 IN interior (T2:real^2->bool)` THEN
      MP_TAC(ISPEC `T2:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier T2:real^2->bool`; `J:real^N->bool`;
                 `vec 0:real^2`; `v:real^N`; `G:real^2->real^N`;
                 `G':real^N->real^2`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Phi = moi_con_conemap (relative_frontier T2) (vec 0:real^2) (v:real^N) G` THEN
  ABBREV_TAC `Phi' = moi_con_conemap (J:real^N->bool) v (vec 0:real^2) G'` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!y r. y IN J /\ &0 <= r /\ r <= &1
          ==> v + r % (y - v) IN UNIONS {segment[v:real^N,y] | y IN J} /\
              (Phi':real^N->real^2) (v + r % (y - v)) = vec 0 + r % (Phi' y - vec 0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_CON_IN_CONE] THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `r:real`] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Phi'" THEN
      MP_TAC(ISPECL [`J:real^N->bool`; `v:real^N`; `vec 0:real^2`;
                     `G':real^N->real^2`; `y:real^N`; `r:real`]
        MOI_CON_CONEMAP_EQ) THEN
      MP_TAC(ISPECL [`J:real^N->bool`; `v:real^N`; `vec 0:real^2`;
                     `G':real^N->real^2`; `y:real^N`] MOI_CON_CONEMAP_ON_BASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `C = UNIONS {segment[v:real^N,y] | y IN J}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> can (find_term ((=) `Phi:real^2->real^N`)) (concl th) &&
                     is_comb(concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (find_term ((=) `Phi:real^2->real^N`)) (concl th) &&
                     is_comb(concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphism")) THEN
  SUBGOAL_THEN `IMAGE (Phi':real^N->real^2) J = relative_frontier T2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J:real^N->bool`; `v:real^N`; `vec 0:real^2`;
                   `G':real^N->real^2`] MOI_CON_CONEMAP_ON_BASE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
      check (fun th -> can (find_term ((=) `G':real^N->real^2`)) (concl th) &&
                       can (find_term ((=) `J:real^N->bool`)) (concl th) &&
                       is_comb(concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism")) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T2:real^2->bool`; `C:real^N->bool`; `J:real^N->bool`;
                 `X:real^N->bool`; `Phi':real^N->real^2`; `Phi:real^2->real^N`;
                 `vec 0:real^2`; `v:real^N`] MOI_S4O_RAY_COUNT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (IMAGE (Phi':real^N->real^2) X,X)
                  ((Phi:real^2->real^N),(Phi':real^N->real^2))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    MATCH_MP_TAC(ISPECL [`C:real^N->bool`; `T2:real^2->bool`;
       `Phi':real^N->real^2`; `Phi:real^2->real^N`; `X:real^N->bool`]
       MOI_FMB_PLH_RESTRICT) THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`IMAGE (Phi':real^N->real^2) X`; `X:real^N->bool`;
     `Phi:real^2->real^N`; `Phi':real^N->real^2`; `1`]
     MOI_FM3_PL_SPHERE_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `IMAGE (Phi':real^N->real^2) X` MOI_CMB_STAR_SHAPED_PL_SPHERE_0) THEN
    REWRITE_TAC[DIMINDEX_2; ARITH_RULE `2 - 1 = 1`] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `C:real^N->bool` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(v:real^N IN X)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(v:real^N) = Phi (vec 0:real^2) /\ x = Phi (Phi' x)`
      MP_TAC THENL
       [CONJ_TAC THENL
         [EXPAND_TAC "Phi" THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN ASM_REWRITE_TAC[];
          CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
        ASM_MESON_TAC[]];
      X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^2` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `IMAGE (Phi':real^N->real^2) X`)) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID]];
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_SIMPLEX) THEN
    DISCH_THEN(MP_TAC o SPEC `&2:int`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* Cones over PL arcs: the cone from w over a PL 1-cell a with ends p, q   *)
(* (radially simple from w) is a PL 2-cell bounded by a and the segments   *)
(* [w,p], [w,q] (cone chart from the standard triangle).                   *)

let MOI_S4O_RF_SEGMENT = prove
 (`!a b:real^N. ~(a = b) ==> relative_frontier(segment[a,b]) = {a,b}`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[]);;

let MOI_S4O_STD_EDGE = prove
 (`2 <= dimindex(:N)
   ==> ~(basis 1:real^N = basis 2) /\
       ~(vec 0 IN segment[basis 1:real^N,basis 2]) /\
       (!x y. x IN segment[basis 1:real^N,basis 2] /\
              y IN segment[basis 1,basis 2] /\ y IN segment[vec 0,x] ==> y = x) /\
       UNIONS {segment[vec 0:real^N,x] | x IN segment[basis 1,basis 2]} =
       convex hull {vec 0,basis 1,basis 2}`,
  DISCH_TAC THEN
  SUBGOAL_THEN `!z:real^N. z IN segment[basis 1,basis 2] ==> z$1 + z$2 = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$1`) THEN
    SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN segment[vec 0,x]` THEN
    REWRITE_TAC[IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u = &1` (fun th -> ASM_REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING;
    MP_TAC(ISPECL [`{basis 1:real^N,basis 2}`; `vec 0:real^N`]
      CONVEX_HULL_INSERT_SEGMENTS) THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; GSYM SEGMENT_CONVEX_HULL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

let MOI_S4O_IMAGE_SEGMENT_CONE = prove
 (`!(phi:real^M->real^N) a x c y.
     (!r. &0 <= r /\ r <= &1 ==> phi(a + r % (x - a)) = c + r % (y - c))
     ==> IMAGE phi (segment[a,x]) = segment[c,y]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `a + u % (x - a):real^M = (&1 - u) % a + u % x`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(&1 - u) % a + u % x:real^M` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `a + u % (x - a):real^M = (&1 - u) % a + u % x`] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S4O_PAIR_EQ = prove
 (`!a b c d:A. {a,b} = {c,d} ==> (a = c /\ b = d) \/ (a = d /\ b = c)`,
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let MOI_S4O_CONE_ARC = prove
 (`!(a:real^N->bool) p q w.
     2 <= dimindex(:N) /\ pl_cell_with_boundary 1 a {p,q} /\ ~(w IN a) /\
     (!x y. x IN a /\ y IN a /\ y IN segment[w,x] ==> y = x)
     ==> pl_cell_with_boundary 2 (UNIONS {segment[w,x] | x IN a})
           (a UNION segment[w,p] UNION segment[w,q])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4O_STD_EDGE) THEN
  MP_TAC(ISPECL [`segment[basis 1:real^N,basis 2]`; `k:real^N->bool`; `&1:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`basis 1:real^N`; `basis 2:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N->real^N` (X_CHOOSE_THEN `Q:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (segment[basis 1:real^N,basis 2],a)
                  ((f:real^N->real^N) o (P:real^N->real^N),
                   (Q:real^N->real^N) o (g:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`segment[basis 1:real^N,basis 2]`; `k:real^N->bool`;
       `a:real^N->bool`; `P:real^N->real^N`; `Q:real^N->real^N`;
       `f:real^N->real^N`; `g:real^N->real^N`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{((f:real^N->real^N) o (P:real^N->real^N)) (basis 1),
                 (f o P) (basis 2)} = {p:real^N,q}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `{p:real^N,q}`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `relative_frontier (k:real^N->bool)`)) (concl th) &&
      can (find_term ((=) `P:real^N->real^N`)) (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `relative_frontier (k:real^N->bool)`)) THEN
    ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT] THEN
    REWRITE_TAC[IMAGE_CLAUSES; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[basis 1:real^N,basis 2]`; `a:real^N->bool`;
                 `vec 0:real^N`; `w:real^N`;
                 `(f:real^N->real^N) o (P:real^N->real^N)`;
                 `(Q:real^N->real^N) o (g:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
    SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {vec 0:real^N,basis 1,basis 2}`;
    `moi_con_conemap (segment[basis 1:real^N,basis 2]) (vec 0) (w:real^N)
       ((f:real^N->real^N) o (P:real^N->real^N))`;
    `moi_con_conemap (a:real^N->bool) w (vec 0:real^N)
       ((Q:real^N->real^N) o (g:real^N->real^N))`] THEN
  ASM_SIMP_TAC[MOI_SS2_STD_TRIANGLE] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; MOI_SS2_STD_NONCOLLINEAR] THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  ABBREV_TAC `Phi = moi_con_conemap (segment[basis 1:real^N,basis 2]) (vec 0) (w:real^N)
       ((f:real^N->real^N) o (P:real^N->real^N))` THEN
  SUBGOAL_THEN
   `!z:real^N. z IN segment[basis 1,basis 2]
               ==> IMAGE (Phi:real^N->real^N) (segment[vec 0,z]) =
                   segment[w,((f:real^N->real^N) o (P:real^N->real^N)) z]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4O_IMAGE_SEGMENT_CONE THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "Phi" THEN
    MP_TAC(ISPECL [`segment[basis 1:real^N,basis 2]`; `vec 0:real^N`; `w:real^N`;
                   `(f:real^N->real^N) o (P:real^N->real^N)`; `z:real^N`;
                   `r:real`] MOI_CON_CONEMAP_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^N->real^N) (segment[basis 1,basis 2]) = a`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `(f:real^N->real^N) o (P:real^N->real^N)`)) (concl th) &&
      can (find_term ((=) `a:real^N->bool`)) (concl th) &&
      is_comb(concl th) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism")) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
      `IMAGE ((f:real^N->real^N) o (P:real^N->real^N)) (segment[basis 1,basis 2])` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> (f:real^N->real^N) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ISPECL [`basis 2:real^N`; `vec 0:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
  SUBGOAL_THEN `(basis 1:real^N) IN segment[basis 1,basis 2] /\
                (basis 2:real^N) IN segment[basis 1,basis 2]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MOI_S4O_PAIR_EQ o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `{p:real^N,q}`)) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* PL circles as simple closed PL paths; PL arcs as PL 1-cells; the closed  *)
(* complement of an arc in a PL circle is an arc with the same ends (the   *)
(* splitting is detected by the two components of the circle minus the     *)
(* two ends).                                                                *)

let MOI_S4O_CIRCLE_LOOP = prove
 (`!K:real^N->bool.
     pl_sphere 1 K
     ==> ?gam. simple_path gam /\ pathfinish gam = pathstart gam /\
               pl_map_on (interval[vec 0,vec 1]) gam /\ path_image gam = K`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_SIMP_TAC[GSYM RELATIVE_FRONTIER_OF_TRIANGLE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `k:real^N->bool`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `(f:real^N->real^N) o polygonal_path[a:real^N;b;c;a]` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[pathstart; pathfinish; o_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `relative_frontier(convex hull {a:real^N,b,c})` THEN
    ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH; GSYM path_image; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE]]);;

let MOI_S4O_ARC_CELL = prove
 (`!a:real^1->real^N.
     arc a /\ pl_map_on (interval[vec 0,vec 1]) a
     ==> pl_cell_with_boundary 1 (path_image a) {pathstart a,pathfinish a}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(vec 0:real^N = basis 1)` ASSUME_TAC THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN MATCH_MP_TAC BASIS_NONZERO THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[vec 0:real^1,vec 1] = segment[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_1; DROP_VEC; REAL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[vec 0:real^N,basis 1]`;
                 `interval[vec 0:real^1,vec 1]`; `&1:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `basis 1:real^N`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `vec 1:real^1`] THEN
      REWRITE_TAC[VEC_EQ; ARITH_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^1` (X_CHOOSE_THEN `q:real^1->real^N`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`segment[vec 0:real^N,basis 1]`;
                        `(a:real^1->real^N) o (p:real^N->real^1)`;
                        `(q:real^1->real^N) o (h:real^N->real^1)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `basis 1:real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`segment[vec 0:real^N,basis 1]`;
       `interval[vec 0:real^1,vec 1]`; `path_image(a:real^1->real^N)`;
       `p:real^N->real^1`; `q:real^1->real^N`; `a:real^1->real^N`;
       `h:real^N->real^1`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `relative_frontier (segment[vec 0:real^N,basis 1])`))
        (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    REWRITE_TAC[IMAGE_o] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `p:real^N->real^1`)) (lhs(concl th)) &&
      is_comb(lhs(concl th)) &&
      fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE")) THEN
    ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT; VEC_EQ; ARITH_EQ] THEN
    REWRITE_TAC[IMAGE_CLAUSES; pathstart; pathfinish]]);;

let MOI_S4O_CIRCLE_ARC = prove
 (`!(K:real^N->bool) A B p q.
     pl_sphere 1 K /\ A UNION B = K /\ closed A /\ closed B /\
     A INTER B = {p,q} /\ ~(p = q) /\ ~(A SUBSET {p,q}) /\ ~(B SUBSET {p,q})
     ==> pl_cell_with_boundary 1 B {p,q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^N) IN K /\ q IN K` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      (gam:real^1->real^N) s = p /\ gam t = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^N) IN K` THEN UNDISCH_TAC `(q:real^N) IN K` THEN
    REWRITE_TAC[SYM(ASSUME `path_image (gam:real^1->real^N) = K`)] THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a1 = subpath s t (gam:real^1->real^N)` THEN
  SUBGOAL_THEN `arc(a1:real^1->real^N) /\ pl_map_on (interval[vec 0,vec 1]) a1 /\
                pathstart a1 = p /\ pathfinish a1 = q /\ path_image a1 SUBSET K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_SUBPATH THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[PATHSTART_SUBPATH];
      ASM_REWRITE_TAC[PATHFINISH_SUBPATH];
      REWRITE_TAC[SYM(ASSUME `path_image (gam:real^1->real^N) = K`)] THEN
      MATCH_MP_TAC PATH_IMAGE_SUBPATH_SUBSET THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simple_path]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^N`; `a1:real^1->real^N`] MOI_PL2_ARC_IN_LOOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `connected(path_image (a1:real^1->real^N) DIFF {p,q}) /\
    connected(path_image (a2:real^1->real^N) DIFF {p,q})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `a1:real^1->real^N` CONNECTED_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH];
      MP_TAC(ISPEC `a2:real^1->real^N` CONNECTED_SIMPLE_PATH_ENDLESS) THEN
      ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN REWRITE_TAC[INSERT_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U:real^N->bool. connected U /\ U SUBSET K /\ U INTER {p,q} = {}
                     ==> A INTER U = {} \/ B INTER U = {}`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`A:real^N->bool`; `B:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `path_image (a1:real^1->real^N) DIFF {p,q}`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `path_image (a2:real^1->real^N) DIFF {p,q}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^N) IN path_image a1 /\ q IN path_image a1 /\
                p IN path_image a2 /\ q IN path_image a2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `B:real^N->bool = path_image a1 \/ B = path_image a2`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{p:real^N,q} = {pathstart a1,pathfinish a1}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC MOI_S4O_ARC_CELL THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{p:real^N,q} = {pathstart a2,pathfinish a2}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[INSERT_AC]; MATCH_MP_TAC MOI_S4O_ARC_CELL THEN ASM_REWRITE_TAC[]]]);;

(* A closed piece p of a PL 2-sphere s whose frontier in s lies in a PL     *)
(* circle j inside p, with points off j and missing a point of s, is one   *)
(* of the two disks into which j splits s.                                  *)

let MOI_S4O_SPHERE_PIECE = prove
 (`!(s:real^N->bool) j p.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET p /\ p SUBSET s /\ closed p /\
     closure(s DIFF p) INTER p SUBSET j /\ ~(p SUBSET j) /\ ~(s SUBSET p)
     ==> pl_cell_with_boundary 2 p j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `j:real^N->bool`] MOI_S4O_SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^N->bool` (X_CHOOSE_THEN `d2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d1:real^N->bool`; `j:real^N->bool`] MOI_SS2_CELL_FACTS) THEN
  MP_TAC(ISPECL [`d2:real^N->bool`; `j:real^N->bool`] MOI_SS2_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!U:real^N->bool. connected U /\ U SUBSET s /\ U INTER j = {}
                     ==> p INTER U = {} \/ closure(s DIFF p) INTER U = {}`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^N->bool`; `closure(s DIFF p:real^N->bool)`]) THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN
    MP_TAC(ISPEC `s DIFF p:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `d1 DIFF j:real^N->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d2 DIFF j:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `s DIFF p:real^N->bool` CLOSURE_SUBSET) THEN DISCH_TAC THEN
  SUBGOAL_THEN `p:real^N->bool = d1 \/ p = d2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* Gluing finitely many disjoint PL disks Q i onto a PL disk d0, each along *)
(* an arc of the boundary of d0 that is also an arc of its own boundary.    *)

let MOI_S4O_FSA_SUB = prove
 (`!(d:real^N->bool) j. moi_fsa_disk d j ==> j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_disk; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^N`
    (X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^2->bool)` MP_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    SUBGOAL_THEN `closure(k:real^2->bool) = k` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED]; SET_TAC[]];
    ASM SET_TAC[]]);;

let MOI_S4O_GLUE_MANY = prove
 (`!(d0:real^N->bool) j0 (Q:B->real^N->bool) be ga ix.
     FINITE ix
     ==> moi_fsa_disk d0 j0 /\
         (!i. i IN ix
              ==> moi_fsa_disk (Q i) (be i UNION path_image (ga i)) /\
                  arc (ga i) /\ pl_map_on (interval[vec 0,vec 1]) (ga i) /\
                  path_image (ga i) SUBSET j0 /\
                  Q i INTER d0 = path_image (ga i) /\
                  be i INTER path_image (ga i) =
                  {pathstart (ga i),pathfinish (ga i)}) /\
         (!i i'. i IN ix /\ i' IN ix /\ ~(i = i') ==> Q i INTER Q i' = {})
         ==> moi_fsa_disk (d0 UNION UNIONS (IMAGE Q ix))
               ((j0 DIFF UNIONS (IMAGE (\i. path_image (ga i) DIFF
                                             {pathstart (ga i),pathfinish (ga i)}) ix))
                UNION UNIONS (IMAGE be ix))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`ix:B->bool`,`ix:B->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY; DIFF_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `s:B->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cells")
    (LABEL_TAC "disj"))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:B` THEN DISCH_TAC THEN USE_THEN "cells" (MP_TAC o SPEC `i:B`) THEN
      REWRITE_TAC[IN_INSERT; ASSUME `(i:B) IN s`];
      REPEAT STRIP_TAC THEN USE_THEN "disj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    DISCH_TAC] THEN
  USE_THEN "cells" (MP_TAC o SPEC `a:B`) THEN REWRITE_TAC[IN_INSERT] THEN
  STRIP_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
  ABBREV_TAC `D' = (d0:real^N->bool) UNION UNIONS (IMAGE Q (s:B->bool))` THEN
  ABBREV_TAC `O' = UNIONS (IMAGE (\i. path_image ((ga:B->real^1->real^N) i) DIFF
                     {pathstart (ga i),pathfinish (ga i)}) (s:B->bool))` THEN
  ABBREV_TAC `B' = UNIONS (IMAGE (be:B->real^N->bool) s)` THEN
  SUBGOAL_THEN `!i:B. i IN s ==> (Q:B->real^N->bool) i INTER Q a = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "disj" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INSERT; ASSUME `(i:B) IN s`] THEN
    UNDISCH_TAC `(i:B) IN s` THEN UNDISCH_TAC `~((a:B) IN s)` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:B. i IN s ==> path_image ((ga:B->real^1->real^N) i) SUBSET Q i /\
                                 (be:B->real^N->bool) i SUBSET Q i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:B` THEN DISCH_TAC THEN
    USE_THEN "cells" (MP_TAC o SPEC `i:B`) THEN
    REWRITE_TAC[IN_INSERT; ASSUME `(i:B) IN s`] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4O_FSA_SUB) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image ((ga:B->real^1->real^N) a) SUBSET Q a /\
                (be:B->real^N->bool) a SUBSET Q a`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4O_FSA_SUB) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D':real^N->bool) INTER Q (a:B) = path_image (ga a:real^1->real^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "D'" THEN
    SUBGOAL_THEN `UNIONS (IMAGE (Q:B->real^N->bool) s) INTER Q a = {}` MP_TAC THENL
     [REWRITE_TAC[SET_RULE `UNIONS (IMAGE (f:B->real^N->bool) s) INTER t = {} <=>
                            !i. i IN s ==> f i INTER t = {}`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(Q:B->real^N->bool) a INTER d0 = path_image (ga a:real^1->real^N)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O':real^N->bool) INTER Q (a:B) = {} /\ (B':real^N->bool) INTER Q a = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O'"; "B'"] THEN
    REWRITE_TAC[SET_RULE `UNIONS (IMAGE (f:B->real^N->bool) s) INTER t = {} <=>
                          !i. i IN s ==> f i INTER t = {}`] THEN
    CONJ_TAC THEN X_GEN_TAC `i:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:B` o check (fun th ->
      can (find_term ((=) `be:B->real^N->bool`)) (concl th) &&
      is_forall(concl th) && not (can (find_term ((=) `a:B`)) (concl th)) &&
      not (can (find_term ((=) `D':real^N->bool`)) (concl th)) &&
      not (can (find_term ((=) `j0:real^N->bool`)) (concl th)))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:B` o check (fun th ->
      can (find_term ((=) `a:B`)) (concl th) && is_forall(concl th) &&
      not (can (find_term ((=) `be:B->real^N->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D':real^N->bool`; `(j0:real^N->bool) DIFF O' UNION B'`;
                 `(Q:B->real^N->bool) a`;
                 `(be:B->real^N->bool) a UNION path_image (ga a:real^1->real^N)`;
                 `(ga:B->real^1->real^N) a`] MOI_FSA_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(O':real^N->bool) INTER Q (a:B) = {}` THEN
      UNDISCH_TAC `path_image ((ga:B->real^1->real^N) a) SUBSET j0` THEN
      UNDISCH_TAC `path_image ((ga:B->real^1->real^N) a) SUBSET Q a` THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(d:real^N->bool) = d' /\ (j:real^N->bool) = j'
                       ==> moi_fsa_disk d j ==> moi_fsa_disk d' j'`) THEN
  CONJ_TAC THENL
   [EXPAND_TAC "D'" THEN SET_TAC[];
    UNDISCH_TAC `(O':real^N->bool) INTER Q (a:B) = {}` THEN
    UNDISCH_TAC `(B':real^N->bool) INTER Q (a:B) = {}` THEN
    UNDISCH_TAC `(be:B->real^N->bool) a INTER path_image (ga a:real^1->real^N) =
                 {pathstart (ga a),pathfinish (ga a)}` THEN
    UNDISCH_TAC `path_image ((ga:B->real^1->real^N) a) SUBSET Q a` THEN
    UNDISCH_TAC `(be:B->real^N->bool) a SUBSET Q a` THEN
    SET_TAC[]]);;


(* ========================================================================= *)
(* The complexes near a vertex v of kk: dimensions, the two                 *)
(* tetrahedra of tt at a triangle at v (the link of v in tt is a PL         *)
(* 2-sphere), purity of kk at v, boundary triangles, and the two boundary   *)
(* triangles at a boundary edge (the link of v in the boundary surface is a *)
(* PL circle).                                                              *)
(* ========================================================================= *)

let MOI_S4O_TUBE_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> lf_simplicial_complex tt /\ lf_simplicial_complex kk /\
         simplicial_subcomplex kk tt /\ kk SUBSET tt /\
         combinatorial_manifold_with_boundary 3 kk /\
         graph_in_complex tt (skeleton 1 kk) /\ {v} IN skeleton 1 kk /\
         {v} IN tt /\ pl_sphere 2 (UNIONS (simplicial_link tt v)) /\
         (!s. s IN kk ==> aff_dim s <= &3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN skeleton 1 kk` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
    [combinatorial_manifold_with_boundary]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex] o
    check (fun th -> concl th = `simplicial_subcomplex (kk:(real^N->bool)->bool) tt`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `tt:(real^N->bool)->bool`)) (concl th) &&
      moi_s4o_has_const "pl_sphere" th)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CM_WB_DIM THEN ASM_REWRITE_TAC[]]);;

let MOI_S4O_TT_DIM = prove
 (`!(tt:(real^N->bool)->bool) kk v s.
     moi_s34_tube tt kk /\ {v} IN kk /\ s IN tt /\ v IN s ==> aff_dim s <= &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_DIM_LE_2) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_S4O_TT_TRI2 = prove
 (`!(tt:(real^N->bool)->bool) kk v s.
     moi_s34_tube tt kk /\ {v} IN kk /\ s IN tt /\ v IN s /\ aff_dim s = &2
     ==> CARD {r | r IN tt /\ aff_dim r = &3 /\ s SUBSET r} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `&2:int`; `&3:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_SCF_SURF_EDGE THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_SCF_LINK_SPHERE] THEN ASM_INT_ARITH_TAC);;

let MOI_S4O_KK_PURE = prove
 (`!(tt:(real^N->bool)->bool) kk v s.
     moi_s34_tube tt kk /\ {v} IN kk /\ s IN kk /\ v IN s /\ aff_dim s = &2
     ==> ?r. r IN kk /\ aff_dim r = &3 /\ s SUBSET r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim (convex hull {v:real^N}) = &2` THEN
    REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. t IN simplicial_link kk (v:real^N) /\ aff_dim t = &2 /\ e SUBSET t`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o CONJUNCT2 o GEN_REWRITE_RULE I
      [combinatorial_manifold_with_boundary]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MATCH_MP_TAC MOI_SCF_SURF_PURE THEN
      ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_SCF_LINK_SPHERE];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
        (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
      MATCH_MP_TAC MOI_FM3_DISK_PURE THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `g:real^N->real^N`; `f:real^N->real^N`] THEN
      ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT t)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let MOI_S4O_BTRI = prove
 (`!(tt:(real^N->bool)->bool) kk v s.
     moi_s34_tube tt kk /\ {v} IN kk /\ s IN kk /\ v IN s /\ aff_dim s = &2
     ==> (CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1 <=>
          ?r. r IN tt /\ ~(r IN kk) /\ aff_dim r = &3 /\ s SUBSET r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_TT_TRI2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_KK_PURE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = {r:real^N->bool | r IN tt /\ aff_dim r = &3 /\ s SUBSET r}` THEN
  ABBREV_TAC `B = {r:real^N->bool | r IN kk /\ aff_dim r = &3 /\ s SUBSET r}` THEN
  SUBGOAL_THEN `B SUBSET (A:(real^N->bool)->bool) /\ r0 IN B /\ FINITE A`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?r:real^N->bool. r IN tt /\ ~(r IN kk) /\ aff_dim r = &3 /\ s SUBSET r) <=>
                ~(B:(real^N->bool)->bool = A)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (B:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `CARD (B:(real^N->bool)->bool) < CARD (A:(real^N->bool)->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `~(CARD (B:(real^N->bool)->bool) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MOI_S4O_IN_BOUNDARY = prove
 (`!(kk:(real^N->bool)->bool) q.
     lf_simplicial_complex kk /\ q IN kk /\ ~(q = {})
     ==> (q SUBSET complex_boundary kk <=>
          ?s. s IN kk /\ aff_dim s = &2 /\
              CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1 /\
              q SUBSET s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^N. x IN relative_interior q` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_FM3_LF_SIMPLEX;
                    SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN complex_boundary kk` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`kk:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[complex_boundary] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let MOI_S4O_TRI_BOUNDARY = prove
 (`!(kk:(real^N->bool)->bool) s.
     lf_simplicial_complex kk /\ s IN kk /\ aff_dim s = &2
     ==> (s SUBSET complex_boundary kk <=>
          CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4O_IN_BOUNDARY] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s:real^N->bool = s'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_S4O_BEDGE_TWO = prove
 (`!(tt:(real^N->bool)->bool) kk v g.
     moi_s34_tube tt kk /\ {v} IN kk /\ g IN kk /\ v IN g /\ aff_dim g = &1 /\
     g SUBSET complex_boundary kk
     ==> CARD {s | s IN kk /\ aff_dim s = &2 /\ g SUBSET s /\
                   s SUBSET complex_boundary kk} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `B = boundary_complex (kk:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN B <=> r IN kk /\ r SUBSET complex_boundary kk`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[boundary_complex; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) IN B /\ {v:real^N} IN B` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `g:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{s:real^N->bool | s IN kk /\ aff_dim s = &2 /\
                  convex hull (v INSERT e) SUBSET s /\ s SUBSET complex_boundary kk} =
                {r | r IN B /\ aff_dim r = &2 /\ convex hull (v INSERT e) SUBSET r}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `&1:int`; `&2:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `aff_dim(e:real^N->bool) = &0` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. e = {w}` (X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[AFF_DIM_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o CONJUNCT2 o
    GEN_REWRITE_RULE I [combinatorial_manifold] o
    check (fun th -> concl th = `combinatorial_manifold 2 (B:(real^N->bool)->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_FSA_LK_DEG2 THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPEC `simplicial_link B (v:real^N)` COMPLEX_EULER_VALUES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`B:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `convex hull ((v:real^N) INSERT t)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&3:int`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chains: the link of v in t1, the star of the midpoint b of an edge g of  *)
(* tt at v in that link, and the link of b there.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4O_LINK_CHAIN = prove
 (`!(tt:(real^N->bool)->bool) v q.
     lf_simplicial_complex tt /\ {v} IN tt
     ==> (q IN simplicial_link (barycentric_subdivision tt) v <=>
          ?c. moi_bar_chain tt c /\ (!s. s IN c ==> v IN s /\ ~(s = {v})) /\
              q = convex hull (IMAGE simplex_barycentre c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION] o
      check (fun th -> concl th = `(t:real^N->bool) IN barycentric_subdivision tt`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c':(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_VERTEX_IN_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c':(real^N->bool)->bool`;
                   `q:real^N->bool`] MOI_FTA_BS_SUBSET_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((v:real^N) IN q)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]];
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain tt ({v:real^N} INSERT c)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `v:real^N`]
        MOI_FTA_VERTEX_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({v:real^N} INSERT c))` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{v:real^N} INSERT c` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[IN_INSERT; MOI_FTA_BARY_SING];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[]]]]);;

let MOI_S4O_SEG_FACE_V = prove
 (`!(v:real^N) w s.
     ~(v = w) /\ s face_of segment[v,w] /\ v IN s ==> s = {v} \/ s = segment[v,w]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET {v,w}` THEN
  REWRITE_TAC[SET_RULE `c SUBSET {a:real^N,b} <=>
                        c = {} \/ c = {a} \/ c = {b} \/ c = {a,b}`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONVEX_HULL_EMPTY; CONVEX_HULL_SING; NOT_IN_EMPTY;
                              IN_SING]) THEN
  ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN ASM_MESON_TAC[]);;

let MOI_S4O_STARB_CHAIN = prove
 (`!(tt:(real^N->bool)->bool) v w q.
     lf_simplicial_complex tt /\ {v} IN tt /\ segment[v,w] IN tt /\ ~(v = w)
     ==> (q IN simplicial_link (barycentric_subdivision tt) v /\ midpoint(v,w) IN q <=>
          ?c. moi_bar_chain tt c /\ segment[v,w] IN c /\
              (!s. s IN c ==> segment[v,w] SUBSET s) /\
              q = convex hull (IMAGE simplex_barycentre c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[v:real^N,w] = {})` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ_EMPTY]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4O_LINK_CHAIN] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                   `segment[v:real^N,w]`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `segment[v:real^N,w]`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^N`; `w:real^N`; `s:real^N->bool`] MOI_S4O_SEG_FACE_V) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[moi_bar_chain; SUBSET];
        ASM_MESON_TAC[]];
      ASM_MESON_TAC[SUBSET_REFL]];
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
        DISCH_THEN SUBST_ALL_TAC THEN
        SUBGOAL_THEN `(w:real^N) IN {v}` MP_TAC THENL
         [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ASM_REWRITE_TAC[IN_SING]] THEN
        ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S4O_LINKB_CHAIN = prove
 (`!(tt:(real^N->bool)->bool) v w q.
     lf_simplicial_complex tt /\ {v} IN tt /\ segment[v,w] IN tt /\ ~(v = w)
     ==> (q IN simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                 (midpoint(v,w)) <=>
          ?c. moi_bar_chain tt c /\
              (!s. s IN c ==> segment[v,w] SUBSET s /\ ~(s = segment[v,w])) /\
              q = convex hull (IMAGE simplex_barycentre c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[v:real^N,w] = {})` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ_EMPTY]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                   `t:real^N->bool`] MOI_S4O_STARB_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `q IN simplicial_link (barycentric_subdivision tt) (v:real^N)` THEN
    ASM_SIMP_TAC[MOI_S4O_LINK_CHAIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:(real^N->bool)->bool) SUBSET c'` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(midpoint(v:real^N,w) IN q)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain tt (segment[v:real^N,w] INSERT c)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [simplicial_link] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_S4O_LINK_CHAIN] THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
        DISCH_THEN SUBST_ALL_TAC THEN
        SUBGOAL_THEN `(w:real^N) IN {v}` MP_TAC THENL
         [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ASM_REWRITE_TAC[IN_SING]] THEN
        ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                     `segment[v:real^N,w]`] MOI_FTA_BARY_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                                (segment[v:real^N,w] INSERT c))` THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
           `convex hull (IMAGE simplex_barycentre (segment[v:real^N,w] INSERT c))`]
           MOI_S4O_STARB_CHAIN) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        EXISTS_TAC `segment[v:real^N,w] INSERT c` THEN
        ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[]]]]);;


(* ========================================================================= *)
(* The level picture at a vertex v of kk (MOI_FTA_THETA): basic             *)
(* facts, the level function on link simplices, cone coordinates from the  *)
(* midpoint of an edge of kk at v, and the walls of the vertex ball.        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The level picture at a vertex v of kk: a PL homeomorphism h of the       *)
(* closed star of v in t1 fixing its faces, with affine level functions on  *)
(* its simplices (MOI_FTA_THETA, for the graph skeleton 1 kk).              *)
(* ------------------------------------------------------------------------- *)

let moi_s4o_lev = new_definition
 `moi_s4o_lev (tt:(real^N->bool)->bool) kk (v:real^N) (h:real^N->real^N) k <=>
    pl_homeomorphism (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s},
                      UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}) (h,k) /\
    (!s. s IN moi_fta_cstar (barycentric_subdivision tt) v ==> IMAGE h s = s) /\
    (!m. m IN barycentric_subdivision tt /\ v IN m
         ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                 (!a. a extreme_point_of m
                      ==> f a = if a IN UNIONS (skeleton 1 kk) then &1 else &0) /\
                 f v = &1 /\
                 (!x. x IN IMAGE h (moi_s34_vb tt kk v) /\ x IN m <=>
                      x IN m /\ &1 / &2 <= f x) /\
                 (!x. x IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                      x IN m <=>
                      x IN m /\ f x = &1 / &2))`;;

let MOI_S4O_LEV_EXISTS = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk ==> ?h k. moi_s4o_lev tt kk v h k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_THETA) THEN
  ASM_REWRITE_TAC[moi_s4o_lev; moi_s34_vb; moi_s34_bd]);;

let MOI_S4O_IMAGE_FIX = prove
 (`!(f:A->A) s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;

let MOI_S4O_LEV_BASIC = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> homeomorphism (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s},
                        UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}) (h,k) /\
         compact (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}) /\
         (!x. x IN UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}
              ==> h x IN UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} /\
                  k (h x) = x /\ h (k x) = x) /\
         moi_s34_vb tt kk v SUBSET
           UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} /\
         (!X. X SUBSET UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}
              ==> IMAGE h (closure X) = closure (IMAGE h X)) /\
         (!fs. fs SUBSET moi_fta_cstar (barycentric_subdivision tt) v
              ==> IMAGE h (UNIONS fs) = UNIONS fs) /\
         IMAGE h (UNIONS (simplicial_link (barycentric_subdivision tt) v)) =
         UNIONS (simplicial_link (barycentric_subdivision tt) v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4o_lev] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!fs. fs SUBSET moi_fta_cstar (barycentric_subdivision tt) (v:real^N)
                    ==> IMAGE (h:real^N->real^N) (UNIONS fs) = UNIONS fs`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOI_S4O_IMAGE_FIX THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      moi_s4o_has_const "moi_fta_cstar" th &&
      can (find_term ((=) `h:real^N->real^N`)) (concl th))) THEN
    UNDISCH_TAC `(r:real^N->bool) IN fs` THEN
    UNDISCH_TAC `fs SUBSET moi_fta_cstar (barycentric_subdivision tt) (v:real^N)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(St:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `St:real^N->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_fta_cstar"))
        (lhs(concl th)))) THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision tt` MP_TAC THENL
     [UNDISCH_TAC `(r:real^N->bool) IN moi_fta_cstar (barycentric_subdivision tt) v` THEN
      UNDISCH_TAC `moi_fta_cstar (barycentric_subdivision tt) (v:real^N) SUBSET
                   barycentric_subdivision tt` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_FDN_LF_SIMPLEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN St` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^N) St = St` THEN SET_TAC[];
    REWRITE_TAC[SYM(ASSUME `UNIONS {s | s IN barycentric_subdivision tt /\
                                        (v:real^N) IN s} = St`)] THEN
    REWRITE_TAC[moi_s34_vb; derived_dual_cell; INTER_SUBSET];
    X_GEN_TAC `X:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `St:real^N->bool`;
                   `St:real^N->bool`; `X:real^N->bool`] HOMEOMORPHISM_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `closure X SUBSET (St:real^N->bool) /\
                  closure (IMAGE (h:real^N->real^N) X) SUBSET St`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[SET_RULE `(s:real^N->bool) SUBSET t ==> t INTER s = s`]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_LINK_POLY) THEN
    ASM_SIMP_TAC[]]);;

let MOI_S4O_BARY_IN_GRAPH = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN tt /\ ~(s = {})
     ==> (simplex_barycentre s IN UNIONS (skeleton 1 kk) <=> s IN skeleton 1 kk)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4A_TUBE) THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]);;

let MOI_S4O_LEV_LINK = prove
 (`!(tt:(real^N->bool)->bool) kk v h k c.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     moi_bar_chain tt c /\ (!s. s IN c ==> v IN s /\ ~(s = {v}))
     ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
             f v = &1 /\
             (!s. s IN c ==> f (simplex_barycentre s) =
                             if s IN skeleton 1 kk then &1 else &0) /\
             (!x. x IN convex hull (IMAGE simplex_barycentre c)
                  ==> (x IN IMAGE h (moi_s34_vb tt kk v) <=> &1 / &2 <= f x) /\
                      (x IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
                       f x = &1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain tt ({v:real^N} INSERT c)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `convex hull (IMAGE simplex_barycentre
      ({v:real^N} INSERT c))` o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [moi_s4o_lev]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{v:real^N} INSERT c` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[IN_INSERT; MOI_FTA_BARY_SING]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt /\ ~(s = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_S4O_BARY_IN_GRAPH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `{v:real^N} INSERT c`;
                   `simplex_barycentre (s:real^N->bool)`] MOI_FTA_BS_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_INSERT];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre ({v} INSERT c))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `x IN s ==> s SUBSET t ==> (x:real^N) IN t`)) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_bd" th)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "real_le" th &&
        moi_s4o_has_const "moi_s34_vb" th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_S4O_LEV_CONE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w y t.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk /\
     y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v,w))) /\
     &0 <= t /\ t <= &1
     ==> midpoint(v,w) + t % (y - midpoint(v,w)) IN
           UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                       midpoint(v,w) IN q} /\
         (midpoint(v,w) + t % (y - midpoint(v,w)) IN IMAGE h (moi_s34_vb tt kk v) <=>
          t <= &1 / &2) /\
         (midpoint(v,w) + t % (y - midpoint(v,w)) IN
            IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
          t = &1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN skeleton 1 kk` ASSUME_TAC THENL
   [REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`; `w:real^N`; `h:real^N->real^N`; `y:real^N`]
    MOI_FTA_DL_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s4o_lev tt kk (v:real^N) h k` THEN
    REWRITE_TAC[moi_s4o_lev; moi_s34_vb; moi_s34_bd] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2 o CONJUNCT2);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s34_vb; GSYM moi_s34_bd] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN `f:real^N->real`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  SUBGOAL_THEN `b + t % (y - b) = (&1 - t) % b + t % (y:real^N)` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % b + t % (y:real^N) IN q` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->bool) IN barycentric_subdivision tt` MP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FDN_LF_SIMPLEX) THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `q:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_S4O_LINK_IN_STAR = prove
 (`!(c:(real^N->bool)->bool) v.
     UNIONS (simplicial_link c v) SUBSET UNIONS {s | s IN c /\ v IN s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]);;

let MOI_S4O_LEV_WALLS = prove
 (`!(tt:(real^N->bool)->bool) kk v h k x.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     x IN IMAGE h (moi_s34_vb tt kk v) /\
     x IN UNIONS (simplicial_link (barycentric_subdivision tt) v)
     ==> ?w. ~(w = v) /\ segment[v,w] IN kk /\
             x IN UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                              midpoint(v,w) IN q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_LINK_IN_STAR) THEN DISCH_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE] o check (fun th ->
    concl th = `(x:real^N) IN IMAGE (h:real^N->real^N)
                 (moi_s34_vb (tt:(real^N->bool)->bool) kk v)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x0:real^N) IN L` ASSUME_TAC THENL
   [UNDISCH_TAC `(h:real^N->real^N) x0 IN L` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^N) L = L` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x0:real^N) = x1` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(x0:real^N) IN St /\ x1 IN St` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(k:real^N->real^N) ((h:real^N->real^N) x0) = x0 /\
                          k (h x1) = x1 /\ h x1 = h x0 ==> x0 = x1`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_WALLS_EQ) THEN
  ASM_REWRITE_TAC[GSYM moi_s34_vb] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^N` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `segment[v:real^N,w] IN skeleton 1 kk` THEN
    SIMP_TAC[skeleton; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`; `w:real^N`; `h:real^N->real^N`; `k:real^N->real^N`]
    MOI_FTA_DISK_THETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `moi_s4o_lev tt kk (v:real^N) h k` THEN
      REWRITE_TAC[moi_s4o_lev] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM moi_s34_vb] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) x0 IN
                IMAGE h (moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER
                         moi_s34_vb tt kk w)` MP_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `(x0:real^N) IN D` THEN
    UNDISCH_TAC `D = moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_vb tt kk w` THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S4O_LEV_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w w'.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ ~(w' = v) /\ ~(w = w') /\
     segment[v,w] IN kk /\ segment[v,w'] IN kk
     ==> IMAGE h (moi_s34_vb tt kk v) INTER
         UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} INTER
         UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w') IN q} = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt /\ segment[v,w'] IN tt /\
                ~(v = w) /\ ~(v = w')` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `q1:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `q2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`; `q1:real^N->bool`]
    MOI_S4O_STARB_CHAIN) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w':real^N`; `q2:real^N->bool`]
    MOI_S4O_STARB_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain tt (c1 INTER c2:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `c1:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c1 INTER c2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c1:(real^N->bool)->bool`;
                   `c2:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`;
                `c1 INTER c2:(real^N->bool)->bool`] MOI_S4O_LEV_LINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET s` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(w:real^N) IN {v}` MP_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ASM_REWRITE_TAC[IN_SING]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. s IN c1 INTER c2 ==> ~((s:real^N->bool) IN skeleton 1 kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s = segment[v:real^N,w] /\ s = segment[v,w']` MP_TAC THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_SIMP_TAC[] THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THENL
       [MP_TAC(ISPECL [`segment[v:real^N,w]`; `s:real^N->bool`] AFF_DIM_SUBSET);
        MP_TAC(ISPECL [`segment[v:real^N,w']`; `s:real^N->bool`] AFF_DIM_SUBSET)] THEN
      ASM_SIMP_TAC[] THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
      ASM_INT_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (MESON[] `(a:real^N->bool) = b /\ a = c ==> b = c`)) THEN
      REWRITE_TAC[CONJUNCT1 SEGMENT_EQ] THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`; `&1 / &2`;
                 `IMAGE simplex_barycentre (c1 INTER c2:(real^N->bool)->bool)`]
    MOI_S4A_STRICT_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
    is_forall(concl th) && moi_s4o_has_const "moi_s34_bd" th &&
    moi_s4o_has_const "convex" th)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S4O_LEV_RAYS = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> (!y. y IN UNIONS (simplicial_link (barycentric_subdivision tt) v)
              ==> ?!r. &0 < r /\ r <= &1 /\
                       v + r % (y - v) IN
                       IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                       (IMAGE h (moi_s34_vb tt kk v) INTER
                        UNIONS (simplicial_link (barycentric_subdivision tt) v))) /\
         ~(v IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                (IMAGE h (moi_s34_vb tt kk v) INTER
                 UNIONS (simplicial_link (barycentric_subdivision tt) v))) /\
         (!x y. x IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                     (IMAGE h (moi_s34_vb tt kk v) INTER
                      UNIONS (simplicial_link (barycentric_subdivision tt) v)) /\
                y IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                     (IMAGE h (moi_s34_vb tt kk v) INTER
                      UNIONS (simplicial_link (barycentric_subdivision tt) v)) /\
                y IN segment[v,x] ==> y = x) /\
         UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} =
         UNIONS {segment[v,y] | y |
                 y IN UNIONS (simplicial_link (barycentric_subdivision tt) v)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  SUBGOAL_THEN `~(v:real^N IN L) /\
                (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
                ~(L:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
      MOI_STA_LINK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} =
                UNIONS {segment[v,y] | y | y IN L}`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_FTA_STAR_EQ_CONE THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`;
                 `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v)`;
                 `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`]
    MOI_FTA_CONE_FROM_RAYS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v) SUBSET
                  UNIONS {segment[v,y] | y | (y:real^N) IN L}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `L:real^N->bool`)) (rhs(concl th)))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?q. q IN simplicial_link (barycentric_subdivision tt) (v:real^N) /\
                      (y:real^N) IN q` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN L` THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`;
                   `q:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `moi_s4o_lev tt kk (v:real^N) h k` THEN REWRITE_TAC[moi_s4o_lev] THEN
    DISCH_THEN(MP_TAC o SPEC `convex hull ((v:real^N) INSERT q)` o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT q)`; `f:real^N->real`] THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Fullness of subcomplexes in t1 along rays, and the link circle            *)
(* K of the midpoint of an edge of kk at v: its part in |kk| meets the      *)
(* closure of the rest exactly at the barycentres of the boundary          *)
(* triangles at the edge.                                                   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Fullness: a simplex of t1 meets the polyhedron of a subcomplex of tt in  *)
(* the face spanned by the members of its chain lying in the subcomplex.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4O_HULL_SUB = prove
 (`!(tt:(real^N->bool)->bool) sub c.
     lf_simplicial_complex tt /\ simplicial_subcomplex sub tt /\ moi_bar_chain tt c
     ==> convex hull (IMAGE simplex_barycentre c) INTER UNIONS sub =
         convex hull (IMAGE simplex_barycentre (c INTER sub))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FTA_HULL_SUBCOMPLEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_CASES_TAC `c INTER sub:(real^N->bool)->bool = {}` THENL
       [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS (c INTER sub:(real^N->bool)->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]]]]);;

let MOI_S4O_RAY_SUB = prove
 (`!(tt:(real^N->bool)->bool) sub c b y t.
     lf_simplicial_complex tt /\ simplicial_subcomplex sub tt /\ moi_bar_chain tt c /\
     b IN convex hull (IMAGE simplex_barycentre c) /\ b IN UNIONS sub /\
     y IN convex hull (IMAGE simplex_barycentre c) /\ &0 < t /\ t <= &1
     ==> (b + t % (y - b) IN UNIONS sub <=> y IN UNIONS sub)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `H = convex hull (IMAGE simplex_barycentre (c:(real^N->bool)->bool))` THEN
  ABBREV_TAC `F0 = convex hull (IMAGE simplex_barycentre
                     (c INTER sub:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(H:real^N->bool) INTER UNIONS sub = F0 /\ F0 face_of H /\ convex H`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "F0"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_HULL_SUB THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[CONVEX_CONVEX_HULL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b + t % (y - b) = (&1 - t) % b + t % (y:real^N)` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % b + t % (y:real^N) IN H` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z IN H ==> (z IN UNIONS sub <=> z IN F0)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(b:real^N) IN F0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `t = &1` THENL
     [UNDISCH_TAC `(&1 - t) % b + t % (y:real^N) IN F0` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO;
        VECTOR_MUL_LID; VECTOR_ADD_LID];
      ALL_TAC] THEN
    ASM_CASES_TAC `y:real^N = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [face_of]) THEN
    DISCH_THEN(MP_TAC o SPECL [`b:real^N`; `y:real^N`;
                               `(&1 - t) % b + t % (y:real^N)`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `H:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let MOI_S4O_STAR_SUB = prove
 (`!(tt:(real^N->bool)->bool) sub v.
     lf_simplicial_complex tt /\ simplicial_subcomplex sub tt /\ {v} IN tt
     ==> UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} INTER UNIONS sub =
         UNIONS {r | r IN moi_fta_cstar (barycentric_subdivision tt) v /\
                     r SUBSET UNIONS sub} /\
         closed (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} INTER
                 UNIONS sub)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision tt:(real^N->bool)->bool) /\
                {v:real^N} IN barycentric_subdivision tt`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
    REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; MOI_FTA_BARY_SING] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_CSTAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION] o
        check (fun th -> concl th =
          `(m:real^N->bool) IN barycentric_subdivision (tt:(real^N->bool)->bool)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                     (c INTER sub:(real^N->bool)->bool))` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[moi_fta_cstar; IN_ELIM_THM] THEN EXISTS_TAC `m:real^N->bool` THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `m:real^N->bool`)) THEN
        MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sub:(real^N->bool)->bool`;
                       `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sub:(real^N->bool)->bool`;
                       `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS (moi_fta_cstar (barycentric_subdivision tt) (v:real^N))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]; ASM_REWRITE_TAC[SUBSET_REFL]];
        REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_fta_cstar (barycentric_subdivision tt) (v:real^N)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision tt` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `r:real^N->bool`]
        MOI_FDN_LF_SIMPLEX) THEN
      ASM_SIMP_TAC[]]]);;

let MOI_S4O_NEST_DIM = prove
 (`!(c:(real^N->bool)->bool) s t.
     lf_simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t /\ ~(s = t)
     ==> aff_dim s < aff_dim t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_LT_LE] THEN
  ASM_SIMP_TAC[AFF_DIM_SUBSET] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(s:real^N->bool = t)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S4O_SUPER_DIM = prove
 (`!(tt:(real^N->bool)->bool) kk v w s.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN tt /\
     s IN tt /\ segment[v,w] SUBSET s /\ ~(s = segment[v,w])
     ==> aff_dim s = &2 \/ aff_dim s = &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_TT_DIM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `segment[v:real^N,w]`; `s:real^N->bool`]
    MOI_S4O_NEST_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S4O_TUBE_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[]; ASM_INT_ARITH_TAC]);;

let MOI_S4O_KK_PURE_GEN = prove
 (`!(tt:(real^N->bool)->bool) kk v s.
     moi_s34_tube tt kk /\ {v} IN kk /\ s IN kk /\ v IN s /\ ~(s = {v})
     ==> ?r. r IN kk /\ aff_dim r = &3 /\ s SUBSET r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(convex hull {v:real^N} = {v})` THEN
    REWRITE_TAC[CONVEX_HULL_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. t IN simplicial_link kk (v:real^N) /\ aff_dim t = &2 /\ e SUBSET t`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o CONJUNCT2 o GEN_REWRITE_RULE I
      [combinatorial_manifold_with_boundary]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MATCH_MP_TAC MOI_SCF_SURF_PURE THEN
      ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_SCF_LINK_SPHERE];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
        (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
      MATCH_MP_TAC MOI_FM3_DISK_PURE THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `g:real^N->real^N`; `f:real^N->real^N`] THEN
      ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT t)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let MOI_S4O_K_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> FINITE (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                 (midpoint(v,w))) /\
         lf_simplicial_complex (simplicial_link (barycentric_subdivision tt) v) /\
         {midpoint(v,w)} IN simplicial_link (barycentric_subdivision tt) v /\
         segment[v,w] IN skeleton 1 kk /\
         compact (UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (midpoint(v,w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN skeleton 1 kk` ASSUME_TAC THENL
   [REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`; `w:real^N`] MOI_FTA_MID_IN_LINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (simplicial_link (barycentric_subdivision tt)
                                                      (v:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_LINK_LF) THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link (barycentric_subdivision tt) (v:real^N)`;
                 `midpoint(v:real^N,w)`] MOI_FTA_LINK_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT]);;

let MOI_S4O_K_FRONT = prove
 (`!(tt:(real^N->bool)->bool) kk v w x.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     x IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v,w))) /\
     x IN UNIONS kk /\
     x IN closure (UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                           (midpoint(v,w))) DIFF UNIONS kk)
     ==> ?s. s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
             CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1 /\
             x = simplex_barycentre s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt /\ ~(v = w)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v:real^N,w))` THEN
  SUBGOAL_THEN `?q. q IN Q /\ ~(q SUBSET UNIONS kk) /\ (x:real^N) IN q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closure (UNIONS Q DIFF UNIONS kk) SUBSET
                  UNIONS {q:real^N->bool | q IN Q /\ ~(q SUBSET UNIONS kk)}`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^N` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `Q:(real^N->bool)->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
          SUBGOAL_THEN `(q:real^N->bool) IN simplicial_link (barycentric_subdivision tt) v`
          ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
          MP_TAC(ISPECL [`simplicial_link (barycentric_subdivision tt) (v:real^N)`;
                         `q:real^N->bool`] MOI_FDN_LF_SIMPLEX) THEN
          ASM_SIMP_TAC[]]];
      UNDISCH_TAC `(x:real^N) IN closure (UNIONS Q DIFF UNIONS kk)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`; `q:real^N->bool`]
    MOI_S4O_LINKB_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `q:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s2:real^N->bool. s2 IN c /\ ~(s2 IN kk)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[] `~(!s2:real^N->bool. s2 IN c ==> s2 IN kk)
                          ==> ?s2. s2 IN c /\ ~(s2 IN kk)`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(convex hull (IMAGE simplex_barycentre c) SUBSET
                   UNIONS (kk:(real^N->bool)->bool))` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `c INTER kk:(real^N->bool)->bool = c` (fun th -> ASM_MESON_TAC[th;
      INTER_SUBSET]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN c INTER kk` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN c INTER kk
                     ==> s SUBSET s2 /\ ~(s = s2) /\ aff_dim s = &2 /\ aff_dim s2 = &3`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real^N->bool` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s':real^N->bool) IN tt /\ s2 IN tt` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `(s':real^N->bool) SUBSET s2 /\ ~(s' = s2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`s':real^N->bool`; `s2:real^N->bool`] o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((s2:real^N->bool) IN kk)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MATCH_MP_TAC(CONJUNCT2 (REWRITE_RULE[simplicial_subcomplex]
        (ASSUME `simplicial_subcomplex (kk:(real^N->bool)->bool) tt`))) THEN
      EXISTS_TAC `s':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `s':real^N->bool`] MOI_S4O_SUPER_DIM) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `s2:real^N->bool`] MOI_S4O_SUPER_DIM) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `s':real^N->bool`; `s2:real^N->bool`]
      MOI_S4O_NEST_DIM) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[INT_ARITH
      `a:int < b /\ (a = &2 \/ a = &3) /\ (b = &2 \/ b = &3) ==> a = &2 /\ b = &3`];
    ALL_TAC] THEN
  SUBGOAL_THEN `c INTER kk:(real^N->bool)->bool = {s}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
    X_GEN_TAC `s':real^N->bool` THEN
    EQ_TAC THENL [ALL_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(s':real^N->bool) IN tt /\ s IN tt /\ s' IN c /\ s IN c`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INTER; MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s':real^N->bool`; `s:real^N->bool`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ALL_TAC; CONV_TAC SYM_CONV] THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN DISCH_TAC THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN kk /\ s IN c` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_BTRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `s2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]);;

let MOI_S4O_STAR_FINITE_TT = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> FINITE {r | r IN tt /\ v IN r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING]);;

let MOI_S4O_K_IN = prove
 (`!(tt:(real^N->bool)->bool) kk v w c.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     moi_bar_chain tt c /\ (!s. s IN c ==> segment[v,w] SUBSET s /\ ~(s = segment[v,w]))
     ==> convex hull (IMAGE simplex_barycentre c) SUBSET
         UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                 (midpoint(v,w)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                 `convex hull (IMAGE simplex_barycentre (c:(real^N->bool)->bool))`]
    MOI_S4O_LINKB_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4O_K_BTRI = prove
 (`!(tt:(real^N->bool)->bool) kk v w s.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
     CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1
     ==> simplex_barycentre s IN
           UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                   (midpoint(v,w))) /\
         simplex_barycentre s IN UNIONS kk /\
         simplex_barycentre s IN
           closure (UNIONS (simplicial_link (simplicial_link
                     (barycentric_subdivision tt) v) (midpoint(v,w))) DIFF UNIONS kk) /\
         (?r. r IN kk /\ aff_dim r = &3 /\ s SUBSET r /\
              simplex_barycentre r IN
                UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                        (midpoint(v,w)))) /\
         (?r. r IN tt /\ ~(r IN kk) /\ aff_dim r = &3 /\ s SUBSET r /\
              simplex_barycentre r IN
                UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                        (midpoint(v,w))) /\
              ~(simplex_barycentre r IN UNIONS kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (midpoint(v:real^N,w)))` THEN
  SUBGOAL_THEN `aff_dim(segment[v:real^N,w]) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt /\ ~(s = segment[v,w]) /\ ~(s = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`];
      ASM_MESON_TAC[AFF_DIM_EMPTY; INT_ARITH `~(-- &1:int = &2)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN tt /\ s SUBSET r
                  ==> segment[v,w] SUBSET r /\ ~(r = segment[v,w])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(s:real^N->bool = segment[v,w])` THEN REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN tt /\ s SUBSET r /\ ~(r = {})
                  ==> simplex_barycentre r IN K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K" THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `{r:real^N->bool}`] MOI_S4O_K_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; SING_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_BTRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN kk /\ aff_dim r = &3 /\ s SUBSET r`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE {r:real^N->bool | r IN kk /\ aff_dim r = &3 /\ s SUBSET r}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN
        EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?a. {r:real^N->bool | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = {a}`
    MP_TAC THENL [ASM_MESON_TAC[MOI_FM3_CARD_EQ_1]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r':real^N->bool = {}) /\ ~(r:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC[AFF_DIM_EMPTY; INT_ARITH `~(-- &1:int = &3)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN tt` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre (r':real^N->bool) IN UNIONS kk)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((r':real^N->bool) IN kk)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^N->bool) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `r':real^N->bool` THEN ASM_SIMP_TAC[]]] THEN
  SUBGOAL_THEN `moi_bar_chain tt {s:real^N->bool,r'}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre {s:real^N->bool,r'}) =
                segment[simplex_barycentre s,simplex_barycentre r']`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[simplex_barycentre s,simplex_barycentre r'] SUBSET (K:real^N->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "K" THEN
    MATCH_MP_TAC MOI_S4O_K_IN THEN EXISTS_TAC `kk:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre (s:real^N->bool) = simplex_barycentre r')`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[SUBSET_CLOSURE; SUBSET]
    `!t. (x:real^N) IN closure t /\ t SUBSET u ==> x IN closure u`) THEN
  EXISTS_TAC `segment(simplex_barycentre s,simplex_barycentre (r':real^N->bool))` THEN
  ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(z:real^N) IN segment(simplex_barycentre s,simplex_barycentre r')` THEN
  ASM_REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % a + u % b:real^N = a + u % (b - a)`] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `{s:real^N->bool,r'}`; `simplex_barycentre (s:real^N->bool)`;
                 `simplex_barycentre (r':real^N->bool)`; `u:real`] MOI_S4O_RAY_SUB) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      UNDISCH_TAC `&0 < u` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `u < &1` THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

let moi_s4o_rewr_assum p = FIRST_ASSUM(fun th -> if p th then REWRITE_TAC[th] else NO_TAC);;
let moi_s4o_lhs_is tm th = is_eq(concl th) && lhs(concl th) = tm;;
let moi_s4o_rhs_is tm th = is_eq(concl th) && rhs(concl th) = tm;;

let MOI_S4O_DIM_NONEMPTY = prove
 (`!(s:real^N->bool) n. aff_dim s = &n ==> ~(s = {})`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC);;

let MOI_S4O_CARD2 = prove
 (`!s:A->bool. FINITE s /\ CARD s = 2 ==> ?a b. ~(a = b) /\ s = {a,b}`,
  GEN_TAC THEN REWRITE_TAC[GSYM HAS_SIZE] THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `u:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((a:A) IN t)` THEN ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]);;

let MOI_S4O_KOUT_ARC = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     segment[v,w] SUBSET complex_boundary kk
     ==> pl_cell_with_boundary 1
           (closure (UNIONS (simplicial_link (simplicial_link
                     (barycentric_subdivision tt) v) (midpoint(v,w))) DIFF UNIONS kk))
           {simplex_barycentre s | s | s IN kk /\ aff_dim s = &2 /\
                                       segment[v,w] SUBSET s /\
                                       s SUBSET complex_boundary kk}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (midpoint(v:real^N,w)))` THEN
  ABBREV_TAC `TS = {s:real^N->bool | s IN kk /\ aff_dim s = &2 /\
                                     segment[v,w] SUBSET s /\
                                     s SUBSET complex_boundary kk}` THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN TS <=>
                  s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                  CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN EXPAND_TAC "TS" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[MOI_S4O_TRI_BOUNDARY; ASSUME `lf_simplicial_complex(kk:(real^N->bool)->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s1 s2:real^N->bool. ~(s1 = s2) /\ TS = {s1,s2}` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CARD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN
        EXISTS_TAC `kk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "TS" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
      EXPAND_TAC "TS" THEN MATCH_MP_TAC MOI_S4O_BEDGE_TWO THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `v:real^N`] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[]; INT_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{simplex_barycentre s | s | s IN kk /\ aff_dim s = &2 /\
                  segment[v,w] SUBSET s /\ s SUBSET complex_boundary kk} =
                {simplex_barycentre (s1:real^N->bool),simplex_barycentre s2}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SIMPLE_IMAGE_GEN] THEN
    moi_s4o_rewr_assum (moi_s4o_rhs_is `TS:(real^N->bool)->bool`) THEN
    moi_s4o_rewr_assum (moi_s4o_lhs_is `TS:(real^N->bool)->bool`) THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((s1:real^N->bool) IN kk /\ aff_dim s1 = &2 /\ segment[v,w] SUBSET s1 /\
     CARD {r | r IN kk /\ aff_dim r = &3 /\ s1 SUBSET r} = 1) /\
    ((s2:real^N->bool) IN kk /\ aff_dim s2 = &2 /\ segment[v,w] SUBSET s2 /\
     CARD {r | r IN kk /\ aff_dim r = &3 /\ s2 SUBSET r} = 1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) &&
         can (find_term ((=) `TS:(real^N->bool)->bool`)) (concl th)
      then MP_TAC(CONJ (SPEC `s1:real^N->bool` th) (SPEC `s2:real^N->bool` th))
      else NO_TAC) THEN
    REWRITE_TAC[ASSUME `TS:(real^N->bool)->bool = {s1,s2}`; IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`; `s1:real^N->bool`] MOI_S4O_K_BTRI) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`; `s2:real^N->bool`] MOI_S4O_K_BTRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `T1:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `T2:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN tt /\ s2 IN tt /\ T1 IN tt`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `kk SUBSET (tt:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(s1:real^N->bool) IN kk` THEN UNDISCH_TAC `(s2:real^N->bool) IN kk` THEN
    UNDISCH_TAC `(T1:real^N->bool) IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1:real^N->bool = {}) /\ ~(s2:real^N->bool = {}) /\
                ~(T1:real^N->bool = {}) /\ ~(T2:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4O_DIM_NONEMPTY THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t:real^N->bool. s IN tt /\ t IN tt /\ ~(s = {}) /\ ~(t = {}) /\
                  ~(s = t) ==> ~(simplex_barycentre s = simplex_barycentre t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~(s:real^N->bool = t)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_BARY_INJ THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC [`K:real^N->bool`; `K INTER UNIONS (kk:(real^N->bool)->bool)`] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    MP_TAC(ISPEC `K DIFF UNIONS (kk:(real^N->bool)->bool)` CLOSURE_SUBSET) THEN
    SUBGOAL_THEN `closure (K DIFF UNIONS (kk:(real^N->bool)->bool)) SUBSET K` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
      SET_TAC[]];
    SUBGOAL_THEN `(K:real^N->bool) SUBSET
                  UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
      REWRITE_TAC[MOI_S4O_LINK_IN_STAR] THEN EXPAND_TAC "K" THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET] THEN
      MESON_TAC[MOI_FM3_LINK_IN];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4O_STAR_SUB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `K INTER UNIONS kk =
                  K INTER (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} INTER
                           UNIONS (kk:(real^N->bool)->bool))` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    REWRITE_TAC[CLOSED_CLOSURE];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`; `x:real^N`] MOI_S4O_K_FRONT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(s:real^N->bool) = s1 \/ s = s2` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          if is_forall(concl th) &&
             can (find_term ((=) `TS:(real^N->bool)->bool`)) (concl th)
          then MP_TAC(SPEC `s:real^N->bool` th) else NO_TAC) THEN
        REWRITE_TAC[ASSUME `TS:(real^N->bool)->bool = {s1,s2}`; IN_INSERT;
                    NOT_IN_EMPTY] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_INSERT];
        ASM_REWRITE_TAC[IN_INSERT]];
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER] THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `simplex_barycentre (T1:real^N->bool) IN UNIONS kk` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `T1:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(simplex_barycentre (T1:real^N->bool) = simplex_barycentre s1) /\
                  ~(simplex_barycentre (T1:real^N->bool) = simplex_barycentre s2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[INT_ARITH `~(&3:int = &2)`];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre (T1:real^N->bool)`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY];
    REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre (T2:real^N->bool)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(MESON[CLOSURE_SUBSET; SUBSET] `(x:real^N) IN s ==> x IN closure s`) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(simplex_barycentre (T2:real^N->bool) IN UNIONS kk)` THEN
      ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* The splitting disk of an edge of kk at v in the level picture            *)
(* (a cone from the edge midpoint b over the half-scaled link circle K),    *)
(* and helpers for clause 8: cells and polyhedra, faces of a simplex, the  *)
(* homothety y |-> midpoint(b,y), preservation of subcomplexes.             *)
(* ========================================================================= *)

let MOI_S4O_LEV_DISK = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk
     ==> UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} =
         UNIONS {segment[midpoint(v,w),y] | y |
                 y IN UNIONS (simplicial_link (simplicial_link
                        (barycentric_subdivision tt) v) (midpoint(v,w)))} /\
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) =
         IMAGE h (moi_s34_vb tt kk v) INTER
         UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} /\
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) =
         UNIONS {segment[midpoint(v,w),midpoint(midpoint(v,w),y)] | y |
                 y IN UNIONS (simplicial_link (simplicial_link
                        (barycentric_subdivision tt) v) (midpoint(v,w)))} /\
         IMAGE h ((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                  moi_s34_bd tt kk) =
         IMAGE (\y. midpoint(midpoint(v,w),y))
               (UNIONS (simplicial_link (simplicial_link
                        (barycentric_subdivision tt) v) (midpoint(v,w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (b:real^N))` THEN
  ABBREV_TAC `SB = UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                               (b:real^N) IN q}` THEN
  SUBGOAL_THEN `~(K:real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC MOI_FTA_PL_SPHERE_NONEMPTY THEN
    EXISTS_TAC `1` THEN MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `SB = UNIONS {segment[b:real^N,y] | y | y IN K}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["SB"; "K"] THEN MATCH_MP_TAC MOI_FTA_STAR_EQ_CONE THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) =
                IMAGE h (moi_s34_vb tt kk v) INTER SB` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["SB"; "b"] THEN REWRITE_TAC[moi_s34_vb] THEN
    MATCH_MP_TAC MOI_FTA_DISK_THETA THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `moi_s4o_lev tt kk (v:real^N) h k` THEN
      REWRITE_TAC[moi_s4o_lev] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN SB ==> ?y t. y IN K /\ &0 <= t /\ t <= &1 /\ x = b + t % (y - b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_IN_CONE) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN K /\ &0 <= t /\ t <= &1
          ==> (b:real^N) + t % (y - b) IN SB /\
              (b + t % (y - b) IN IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v) <=>
               t <= &1 / &2) /\
              (b + t % (y - b) IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
               t = &1 / &2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["SB"; "b"] THEN
    MATCH_MP_TAC MOI_S4O_LEV_CONE THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th) && not(is_eq(concl th)) &&
        can (find_term ((=) `t:real`)) (concl th) &&
        not (moi_s4o_has_const "moi_s34_vb" th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `t:real`] o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_vb" th &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[b:real^N,midpoint(b,y)]` THEN CONJ_TAC THENL
       [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE (h:real^N->real^N)
                    (moi_s34_vb (tt:(real^N->bool)->bool) kk v)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[IN_SEGMENT; midpoint] THEN EXISTS_TAC `&2 * t` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `S0:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN segment[b,midpoint(b,y)]` THEN
      REWRITE_TAC[IN_SEGMENT; midpoint] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `u / &2`] o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_vb" th &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^N) + u / &2 % (y - b) = x` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(x:real^N) IN SB` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]];
    SUBGOAL_THEN
     `IMAGE (h:real^N->real^N) ((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                                moi_s34_bd tt kk) =
      IMAGE h (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
      IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SET_RULE
        `((a:real^N->bool) INTER b) INTER c = (a INTER b) INTER (a INTER c)`] THEN
      MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
      EXISTS_TAC `k:real^N->real^N` THEN
      EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `moi_s34_vb tt kk v SUBSET
                   UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN EQ_TAC THENL
     [STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th) && not(is_eq(concl th)) &&
        can (find_term ((=) `t:real`)) (concl th) &&
        not (moi_s4o_has_const "moi_s34_vb" th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `t:real`] o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_vb" th &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `(x:real^N) IN IMAGE (h:real^N->real^N)
                   (moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [IN_IMAGE]) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `&1 / &2`] o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_vb" th &&
        can (find_term ((=) `SB:real^N->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^N) + &1 / &2 % (y - b) = x` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN IMAGE (h:real^N->real^N)
                      (moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_bd tt kk)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN IMAGE (h:real^N->real^N)
                      (moi_s34_vb (tt:(real^N->bool)->bool) kk v INTER moi_s34_bd tt kk)` THEN
        SET_TAC[];
        UNDISCH_TAC `(x:real^N) IN SB` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]]]);;

let MOI_S4O_CELL_POLY = prove
 (`!n (c:real^N->bool) b. pl_cell_with_boundary n c b ==> pl_polyhedron c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `c:real^N->bool`)) THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_S4O_FACES_SUB = prove
 (`!(tt:(real^N->bool)->bool) s.
     lf_simplicial_complex tt /\ s IN tt
     ==> simplicial_subcomplex {f | f face_of s} tt /\ UNIONS {f | f face_of s} = s`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE]; MESON_TAC[FACE_OF_TRANS]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_IMP_SUBSET];
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN u ==> s SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC FACE_OF_REFL THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]]);;

let MOI_S4O_CLOSURE_MIDPOINT = prove
 (`!(b:real^N) X.
     closure (IMAGE (\y. midpoint(b,y)) X) = IMAGE (\y. midpoint(b,y)) (closure X)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\y:real^N. midpoint(b,y)) =
                (\x. inv(&2) % b + x) o (\x. inv(&2) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; CLOSURE_TRANSLATION; CLOSURE_SCALING]);;

let MOI_S4O_MIDPOINT_PLH = prove
 (`!(b:real^N) X.
     pl_polyhedron X
     ==> pl_homeomorphism (X,IMAGE (\y. midpoint(b,y)) X)
                          ((\y. midpoint(b,y)),(\z. &2 % z - b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. inv(&2) % x`; `\x:real^N. &2 % x`;
                 `inv(&2) % b:real^N`] MOI_SS2_AFFINE_PLH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `X:real^N->bool` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    MOI_FMB_PLH_RESTRICT)) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  SUBGOAL_THEN `(\x:real^N. inv(&2) % b + inv(&2) % x) = (\y. midpoint(b,y)) /\
                (\y:real^N. &2 % (y - inv(&2) % b)) = (\z. &2 % z - b)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; midpoint] THEN CONJ_TAC THEN GEN_TAC THEN
  VECTOR_ARITH_TAC);;

let MOI_S4O_EDGE_FORM = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> ?v w. ~(v = w) /\ g = segment[v,w] /\ {v} IN kk /\ {w} IN kk /\
               segment[v,w] IN kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4A_KK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> moi_s4o_has_const "CARD" th &&
      is_eq(concl th))) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^N->bool` MOI_S4O_CARD2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `w:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `{v:real^N,w}`; `v:real^N`] MOI_S4A_VTX_KK);
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `{v:real^N,w}`; `w:real^N`] MOI_S4A_VTX_KK)] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[]);;

let MOI_S4O_LEV_PRES_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk v h k sub X.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     simplicial_subcomplex sub tt /\
     X SUBSET UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}
     ==> IMAGE h (X INTER UNIONS sub) = IMAGE h X INTER UNIONS sub /\
         IMAGE h (X DIFF UNIONS sub) = IMAGE h X DIFF UNIONS sub`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (St INTER UNIONS sub) = St INTER UNIONS sub`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sub:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4O_STAR_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        moi_s4o_has_const "moi_fta_cstar" th then MATCH_MP_TAC th else NO_TAC) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) X SUBSET St` ASSUME_TAC THENL
   [UNDISCH_TAC `(X:real^N->bool) SUBSET St` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `St:real^N->bool`;
                 `X:real^N->bool`; `St INTER UNIONS (sub:(real^N->bool)->bool)`]
    MOI_SS2_INJ_IMAGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^N->bool) INTER UNIONS sub = X INTER (St INTER UNIONS sub) /\
                X DIFF UNIONS sub = X DIFF (St INTER UNIONS sub)`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(X:real^N->bool) SUBSET St` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ASSUME `IMAGE (h:real^N->real^N) (St INTER UNIONS sub) =
                      St INTER UNIONS sub`] THEN
  UNDISCH_TAC `IMAGE (h:real^N->real^N) X SUBSET St` THEN SET_TAC[]);;

let MOI_S4O_MIDPOINT_RAY = prove
 (`!b y:real^N. midpoint(b,y) = b + &1 / &2 % (y - b)`,
  REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC);;

let MOI_S4O_HOM_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk v w sub y.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     simplicial_subcomplex sub tt /\ midpoint(v,w) IN UNIONS sub /\
     y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v,w)))
     ==> (midpoint(midpoint(v,w),y) IN UNIONS sub <=> y IN UNIONS sub)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `y IN UNIONS (simplicial_link (simplicial_link
                 (barycentric_subdivision tt) v) (midpoint(v:real^N,w)))` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN o check (fun th ->
    concl th = `(t:real^N->bool) IN simplicial_link (barycentric_subdivision tt) v`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION] o check (fun th ->
    concl th = `(t:real^N->bool) IN barycentric_subdivision (tt:(real^N->bool)->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MOI_S4O_MIDPOINT_RAY] THEN
  MATCH_MP_TAC MOI_S4O_RAY_SUB THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) face_of t` THEN
  UNDISCH_TAC `(y:real^N) IN r` THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]);;

let MOI_S4O_K_IN_TRI = prove
 (`!(tt:(real^N->bool)->bool) kk v w s.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     s IN tt /\ aff_dim s = &2 /\ segment[v,w] SUBSET s
     ==> UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                 (midpoint(v,w))) INTER s =
         {simplex_barycentre s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(w:real^N = v)` THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt /\ ~(s = {}) /\
                ~(s = segment[v,w]) /\ aff_dim(segment[v:real^N,w]) = &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(segment[v:real^N,w]) = &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `kk SUBSET (tt:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `segment[v:real^N,w] IN kk` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4O_DIM_NONEMPTY THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim(segment[v:real^N,w]) = &1` THEN
      UNDISCH_TAC `aff_dim(segment[v:real^N,w]) = &2` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_SING; IN_UNIONS] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`; `q:real^N->bool`]
      MOI_S4O_LINKB_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `q:real^N->bool`)) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                   `s:real^N->bool`; `y:real^N`] MOI_FTA_HULL_INTER_SIMPLEX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET {a:real^N} ==> y IN s ==> y = a`) THEN
    SUBGOAL_THEN `c INTER {u:real^N->bool | u face_of s} SUBSET {s}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(u:real^N->bool) IN tt /\ u SUBSET s` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_FACE; FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `segment[v:real^N,w]`; `u:real^N->bool`]
        MOI_S4O_NEST_DIM) THEN
      MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_SIMP_TAC[] THEN ASM_INT_ARITH_TAC;
      DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre {s:real^N->bool})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; SUBSET_REFL]]];
    REWRITE_TAC[SING_SUBSET; IN_INTER] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`; `{s:real^N->bool}`] MOI_S4O_K_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[];
          GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; SING_SUBSET]];
      MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
      ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]]]);;


let MOI_S4O_IMAGE_SING_INV = prove
 (`!(h:real^N->real^N) k X St p.
     X SUBSET St /\ (!x. x IN St ==> k (h x) = x) /\ IMAGE h X = {p}
     ==> X = {k p}`,
  SET_TAC[]);;

let MOI_S4O_UNIONS_SING = prove
 (`!(Q:(real^N->bool)->bool) (g:(real^N->bool)->real^N->bool)
    (f:(real^N->bool)->real^N).
     (!s. Q s ==> g s = {f s}) ==> UNIONS {g s | Q s} = {f s | Q s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  ASM_MESON_TAC[IN_SING]);;

let MOI_S4O_CLAUSE8 = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
     ==> pl_cell_with_boundary 1
           (closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk))
           (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                    s SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4O_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `moi_s34_sd tt kk (segment[v:real^N,w]) =
                moi_s34_vb tt kk v INTER moi_s34_vb tt kk w`
  SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_LEV_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(w:real^N = v)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`] MOI_S4O_LEV_DISK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_KOUT_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (b:real^N))` THEN
  ABBREV_TAC `R = (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                  moi_s34_bd tt (kk:(real^N->bool)->bool)` THEN
  ABBREV_TAC `hom = \y:real^N. midpoint(b,y)` THEN
  SUBGOAL_THEN `(R:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) (closure (R DIFF UNIONS kk)) =
                IMAGE hom (closure (K DIFF UNIONS kk))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(R:real^N->bool) DIFF UNIONS kk SUBSET St` ASSUME_TAC THENL
     [UNDISCH_TAC `(R:real^N->bool) SUBSET St` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `h:real^N->real^N`; `k:real^N->real^N`;
                   `kk:(real^N->bool)->bool`; `R:real^N->bool`] MOI_S4O_LEV_PRES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (hom:real^N->real^N) K DIFF UNIONS kk =
                  IMAGE hom (K DIFF UNIONS kk)` SUBST1_TAC THENL
     [SUBGOAL_THEN `(b:real^N) IN UNIONS kk` ASSUME_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SYM(ASSUME `midpoint(v:real^N,w) = b`); MIDPOINT_IN_SEGMENT];
        ALL_TAC] THEN
      SUBGOAL_THEN `!y:real^N. y IN K ==> (hom y IN UNIONS kk <=> y IN UNIONS kk)`
      MP_TAC THENL
       [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `v:real^N`; `w:real^N`; `kk:(real^N->bool)->bool`;
                       `y:real^N`] MOI_S4O_HOM_SUB) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)];
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)] THEN
    REWRITE_TAC[MOI_S4O_CLOSURE_MIDPOINT];
    ALL_TAC] THEN
  ABBREV_TAC `Kout = closure ((K:real^N->bool) DIFF UNIONS kk)` THEN
  ABBREV_TAC `al = closure ((R:real^N->bool) DIFF UNIONS kk)` THEN
  ABBREV_TAC `P = {simplex_barycentre s | s IN kk /\ aff_dim s = &2 /\
                   segment [v:real^N,w] SUBSET s /\ s SUBSET complex_boundary kk}` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (IMAGE (hom:real^N->real^N) Kout) (IMAGE (hom:real^N->real^N) P)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CELL_PLH THEN
    EXISTS_TAC `\z:real^N. &2 % z - b` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)] THEN
    MATCH_MP_TAC MOI_S4O_MIDPOINT_PLH THEN
    MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`1`; `P:real^N->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `al SUBSET (St:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [UNDISCH_TAC `(R:real^N->bool) SUBSET St` THEN SET_TAC[];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) (IMAGE h al) = al` ASSUME_TAC THENL
   [UNDISCH_TAC `al SUBSET (St:real^N->bool)` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (St,St) ((k:real^N->real^N),h)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    MP_TAC(ASSUME `moi_s4o_lev tt kk (v:real^N) h k`) THEN
    REWRITE_TAC[moi_s4o_lev] THEN
    REWRITE_TAC[ASSUME `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} =
                        St`] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (IMAGE (h:real^N->real^N) al,al) (k,h)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`St:real^N->bool`; `St:real^N->bool`; `k:real^N->real^N`;
                   `h:real^N->real^N`; `IMAGE (h:real^N->real^N) al`]
      MOI_FMB_PLH_RESTRICT) THEN
    REWRITE_TAC[ASSUME `IMAGE (k:real^N->real^N) (IMAGE h al) = al`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `al SUBSET (St:real^N->bool)` THEN
      UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
      SET_TAC[];
      REWRITE_TAC[ASSUME `IMAGE (h:real^N->real^N) al = IMAGE (hom:real^N->real^N) Kout`] THEN
      MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC [`1`; `IMAGE (hom:real^N->real^N) P`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 al (IMAGE (k:real^N->real^N) (IMAGE (hom:real^N->real^N) P))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `IMAGE (h:real^N->real^N) al`; `IMAGE (hom:real^N->real^N) P`;
                   `k:real^N->real^N`; `h:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
    REWRITE_TAC[ASSUME `IMAGE (k:real^N->real^N) (IMAGE h al) = al`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `IMAGE (h:real^N->real^N) al = IMAGE (hom:real^N->real^N) Kout`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s
                ==> s INTER R = {(k:real^N->real^N) (hom (simplex_barycentre s))}`
  (LABEL_TAC "rim") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
     [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:real^N) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `segment[v:real^N,w] SUBSET s` THEN
      REWRITE_TAC[SYM(ASSUME `midpoint(v:real^N,w) = b`)] THEN
      MP_TAC(ISPECL [`v:real^N`; `w:real^N`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `h:real^N->real^N`; `k:real^N->real^N`;
                   `{f:real^N->bool | f face_of s}`; `R:real^N->bool`]
      MOI_S4O_LEV_PRES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS {f:real^N->bool | f face_of s} = s`] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `!y:real^N. y IN K ==> (hom y IN s <=> y IN s)` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `v:real^N`; `w:real^N`; `{f:real^N->bool | f face_of s}`;
                     `y:real^N`] MOI_S4O_HOM_SUB) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `w:real^N`; `s:real^N->bool`] MOI_S4O_K_IN_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) (R INTER s) =
                  {hom (simplex_barycentre (s:real^N->bool))}` ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `IMAGE (h:real^N->real^N) (R INTER s) = IMAGE h R INTER s`] THEN
      REWRITE_TAC[ASSUME `IMAGE (h:real^N->real^N) R = IMAGE (hom:real^N->real^N) K`] THEN
      SUBGOAL_THEN `IMAGE (hom:real^N->real^N) K INTER s = IMAGE hom (K INTER s)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `!y:real^N. y IN K ==> (hom y IN s <=> y IN s)` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[ASSUME `K INTER s = {simplex_barycentre (s:real^N->bool)}`] THEN
      REWRITE_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC MOI_S4O_IMAGE_SING_INV THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `St:real^N->bool`] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(R:real^N->bool) SUBSET St` THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ASSUME `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x`) THEN
      MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s INTER R | s IN moi_s34_simp kk (&2) /\ segment [v,w] SUBSET s /\
                                    s SUBSET complex_boundary kk} =
                IMAGE (k:real^N->real^N) (IMAGE (hom:real^N->real^N) P)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\s:real^N->bool. s IN moi_s34_simp kk (&2) /\
                      segment [v:real^N,w] SUBSET s /\ s SUBSET complex_boundary kk`;
                   `\s:real^N->bool. s INTER (R:real^N->bool)`;
                   `\s:real^N->bool. (k:real^N->real^N) (hom (simplex_barycentre s))`]
      MOI_S4O_UNIONS_SING) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      USE_THEN "rim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* Clause 7 tools: the star misses far simplices, the boundary              *)
(* complex, the link circle J1 of v in the boundary surface, rays from v,   *)
(* and the PL 2-sphere Z UNION (Y INTER L1) bounding h(C_v).               *)
(* ========================================================================= *)

(* The closed star of a vertex v in the first derived complex misses every *)
(* simplex of tt not containing v.                                          *)

let MOI_S4O_ST_MISS = prove
 (`!(tt:(real^N->bool)->bool) v s.
     lf_simplicial_complex tt /\ {v} IN tt /\ s IN tt /\ ~(v IN s)
     ==> UNIONS {m | m IN barycentric_subdivision tt /\ v IN m} INTER s = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FTA_IN_STAR1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:(real^N->bool)->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `{f:real^N->bool | f face_of s}`;
                 `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c INTER {f:real^N->bool | f face_of s} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_CHAIN_VERTEX_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `f:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN ASM SET_TAC[]);;

(* The boundary complex of kk as a subcomplex of tt. *)

let MOI_S4O_BC_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> simplicial_subcomplex (boundary_complex kk) tt /\
         UNIONS (boundary_complex kk) = complex_boundary kk /\
         boundary_complex kk SUBSET kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_subcomplex (boundary_complex kk) (kk:(real^N->bool)->bool)` THEN
  UNDISCH_TAC `simplicial_subcomplex (kk:(real^N->bool)->bool) tt` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN MESON_TAC[SUBSET_TRANS]);;

(* The link circle J1 of a boundary vertex v in the boundary surface: the  *)
(* trace of complex_boundary kk on the link of v in the first derived     *)
(* complex is the link of v in the boundary complex of bs kk, a PL circle. *)

let MOI_S4O_J1 = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk
     ==> UNIONS (simplicial_link (barycentric_subdivision tt) v) INTER
         complex_boundary kk =
         UNIONS (simplicial_link (boundary_complex (barycentric_subdivision kk)) v) /\
         pl_sphere 1 (UNIONS (simplicial_link (barycentric_subdivision tt) v) INTER
                      complex_boundary kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4O_BC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `kk:(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision kk:(real^N->bool)->bool`
    BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision kk:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision kk` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{v:real^N}}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; MOI_FTA_HULL_SING_CHAIN;
                 MOI_FTA_BARY_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN boundary_complex (barycentric_subdivision kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link (barycentric_subdivision tt) v) INTER
    complex_boundary kk =
    UNIONS (simplicial_link (boundary_complex (barycentric_subdivision kk))
                            (v:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS (simplicial_link
                     (barycentric_subdivision tt) v)` THEN
      GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `q:real^N->bool`]
        MOI_S4O_LINK_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `q:real^N->bool`)) THEN
      SUBGOAL_THEN `(y:real^N) IN UNIONS kk` ASSUME_TAC THENL
       [MP_TAC(ISPEC `kk:(real^N->bool)->bool` MOI_FMB_CB_SUBSET) THEN
        UNDISCH_TAC `(y:real^N) IN complex_boundary kk` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FTA_HULL_SUBCOMPLEX THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre (c INTER kk)) IN
                    simplicial_link (barycentric_subdivision kk) (v:real^N)`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`;
                       `convex hull (IMAGE simplex_barycentre
                          (c INTER kk:(real^N->bool)->bool))`] MOI_S4O_LINK_CHAIN) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        EXISTS_TAC `c INTER kk:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `moi_bar_chain tt (c:(real^N->bool)->bool)` THEN
          REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
          ASM_SIMP_TAC[FINITE_INTER; INTER_SUBSET; IN_INTER];
          UNDISCH_TAC `!s:real^N->bool. s IN c ==> v IN s /\ ~(s = {v})` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN UNIONS (simplicial_link (barycentric_subdivision kk) v)`
      ASSUME_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                      (c INTER kk:(real^N->bool)->bool))` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `v + &1 / &2 % (y - v) IN complex_boundary (kk:(real^N->bool)->bool)`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `boundary_complex kk:(real^N->bool)->bool`;
                       `{v:real^N} INSERT c`; `v:real^N`; `y:real^N`; `&1 / &2`]
          MOI_S4O_RAY_SUB) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
          REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN REPEAT CONJ_TAC THENL
           [UNDISCH_TAC `moi_bar_chain tt (c:(real^N->bool)->bool)` THEN
            REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            CONJ_TAC THENL [MESON_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
            UNDISCH_TAC `!s:real^N->bool. s IN c ==> v IN s /\ ~(s = {v})` THEN
            UNDISCH_TAC `!s t:real^N->bool. s IN c /\ t IN c
                          ==> s SUBSET t \/ t SUBSET s` THEN
            MESON_TAC[SING_SUBSET; SUBSET_REFL];
            MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
            UNDISCH_TAC `(y:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
            MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> (x:real^N) IN t`) THEN
            MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision kk:(real^N->bool)->bool`; `v:real^N`]
        MOI_FM3_BC_LINK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision kk:(real^N->bool)->bool`; `v:real^N`;
                     `y:real^N`; `&1 / &2`] MOI_FMB_CB_CONE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN
      GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `q IN simplicial_link (boundary_complex (barycentric_subdivision kk))
                     (v:real^N)` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM; boundary_complex] THEN STRIP_TAC THEN
      UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision kk)
                     (barycentric_subdivision (tt:(real^N->bool)->bool))` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q:real^N->bool` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [ASM SET_TAC[];
          EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `combinatorial_manifold 2
                 (boundary_complex (barycentric_subdivision kk:(real^N->bool)->bool))` THEN
  REWRITE_TAC[combinatorial_manifold] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Each point y of the link of v in the first derived complex lies with v   *)
(* in one simplex of the closed star.                                       *)

let MOI_S4O_LINK_SIMPLEX = prove
 (`!(tt:(real^N->bool)->bool) v y.
     lf_simplicial_complex tt /\ {v} IN tt /\
     y IN UNIONS (simplicial_link (barycentric_subdivision tt) v)
     ==> ?c. moi_bar_chain tt c /\ {v} IN c /\
             v IN convex hull (IMAGE simplex_barycentre c) /\
             y IN convex hull (IMAGE simplex_barycentre c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS (simplicial_link (barycentric_subdivision tt) v)` THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `q:real^N->bool`]
    MOI_S4O_LINK_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `q:real^N->bool`)) THEN
  EXISTS_TAC `{v:real^N} INSERT c` THEN
  REWRITE_TAC[IN_INSERT; IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_bar_chain tt (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
    UNDISCH_TAC `!s:real^N->bool. s IN c ==> v IN s /\ ~(s = {v})` THEN
    UNDISCH_TAC `!s t:real^N->bool. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s` THEN
    MESON_TAC[SING_SUBSET; SUBSET_REFL];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    UNDISCH_TAC `(y:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> (x:real^N) IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* Subcomplexes through v are cones from v on the closed star. *)

let MOI_S4O_RAY_SUBC = prove
 (`!(tt:(real^N->bool)->bool) sub v y r.
     lf_simplicial_complex tt /\ {v} IN tt /\ simplicial_subcomplex sub tt /\
     v IN UNIONS sub /\
     y IN UNIONS (simplicial_link (barycentric_subdivision tt) v) /\
     &0 < r /\ r <= &1
     ==> (v + r % (y - v) IN UNIONS sub <=> y IN UNIONS sub)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
    MOI_S4O_LINK_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S4O_RAY_SUB THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* A finite set of simplices of a complex has a polyhedral union. *)

let MOI_S4O_UNIONS_POLY = prove
 (`!(c:(real^N->bool)->bool) f.
     lf_simplicial_complex c /\ FINITE f /\ f SUBSET c ==> pl_polyhedron (UNIONS f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

(* The h-image of the boundary sphere of C_v: Z UNION (Y INTER L1). *)

let MOI_S4O_SH_SPHERE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> pl_sphere 2 (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                      (IMAGE h (moi_s34_vb tt kk v) INTER
                       UNIONS (simplicial_link (barycentric_subdivision tt) v)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_CELL3) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_WALLS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM moi_s34_vb; GSYM moi_s34_bd] THEN DISCH_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  SUBGOAL_THEN `pl_homeomorphism (St,St) ((h:real^N->real^N),k)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_s4o_lev tt kk (v:real^N) h k`) THEN
    REWRITE_TAC[moi_s4o_lev] THEN
    REWRITE_TAC[ASSUME `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} =
                        St`] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN EXPAND_TAC "St" THEN REWRITE_TAC[MOI_S4O_LINK_IN_STAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`St:real^N->bool`; `St:real^N->bool`; `h:real^N->real^N`;
                 `k:real^N->real^N`; `moi_s34_vb tt kk (v:real^N)`]
    MOI_FMB_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`3`; `(moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                                (moi_s34_vb tt kk v INTER (L:real^N->bool))`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`3`; `moi_s34_vb tt kk (v:real^N)`;
                 `(moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                  (moi_s34_vb tt kk v INTER (L:real^N->bool))`;
                 `h:real^N->real^N`; `k:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[ARITH_RULE `2 + 1 = 3`]
    (SPEC `2` MOI_S4O_CELL_SPHERE))) THEN
  MATCH_MP_TAC(MESON[] `s = t ==> pl_sphere 2 s ==> pl_sphere 2 (t:real^N->bool)`) THEN
  REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `St:real^N->bool`;
                 `moi_s34_vb tt kk (v:real^N)`; `L:real^N->bool`]
    MOI_FTA_IMAGE_INTER_INJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The circle c, continued. *)

(* A point v + s(y - v) of a ray from v lies on segment[v,y]. *)

let MOI_S4O_RAY_IN_SEG = prove
 (`!(v:real^N) y s. &0 <= s /\ s <= &1 ==> v + s % (y - v) IN segment[v,y]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* The trace c of the sphere Z UNION (Y INTER L1) on complex_boundary kk is *)
(* a PL circle (radial recognition over the link circle J1).                *)

let MOI_S4O_C_CIRCLE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     moi_s4o_lev tt kk v h k
     ==> pl_sphere 1 ((IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                       (IMAGE h (moi_s34_vb tt kk v) INTER
                        UNIONS (simplicial_link (barycentric_subdivision tt) v))) INTER
                      complex_boundary kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4O_BC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_SH_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_J1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  ABBREV_TAC `Sh = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                   UNION (IMAGE h (moi_s34_vb tt kk v) INTER L)` THEN
  SUBGOAL_THEN `(Sh:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "Sh" THEN
    SUBGOAL_THEN `(L:real^N->bool) SUBSET St` MP_TAC THENL
     [EXPAND_TAC "L" THEN EXPAND_TAC "St" THEN REWRITE_TAC[MOI_S4O_LINK_IN_STAR];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_RADIAL_CIRCLE THEN
  MAP_EVERY EXISTS_TAC [`L INTER complex_boundary (kk:(real^N->bool)->bool)`;
                        `v:real^N`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `!x y:real^N. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x` THEN
    REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `Sh INTER complex_boundary kk =
                  (Sh:real^N->bool) INTER (St INTER UNIONS (boundary_complex kk))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `UNIONS (boundary_complex kk) =
                          complex_boundary (kk:(real^N->bool)->bool)`] THEN
      UNDISCH_TAC `(Sh:real^N->bool) SUBSET St` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `2` THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `boundary_complex kk:(real^N->bool)->bool`;
                   `v:real^N`] MOI_S4O_STAR_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} =
                        St`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC MOI_S4O_UNIONS_POLY THEN
    EXISTS_TAC `barycentric_subdivision tt:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_fta_cstar (barycentric_subdivision tt) (v:real^N)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      UNDISCH_TAC `moi_fta_cstar (barycentric_subdivision tt) (v:real^N) SUBSET
                   barycentric_subdivision tt` THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS {segment[v,y] | y | y IN L}` MP_TAC THENL
     [REWRITE_TAC[ASSUME `UNIONS {segment[v,y] | y | (y:real^N) IN L} = St`] THEN
      UNDISCH_TAC `(x:real^N) IN Sh` THEN UNDISCH_TAC `(Sh:real^N->bool) SUBSET St` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_IN_CONE) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(s = &0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((v:real^N) IN Sh)` THEN
      UNDISCH_TAC `v + &0 % (y - v) IN (Sh:real^N->bool)` THEN
      REWRITE_TAC[VECTOR_ARITH `v + &0 % (y - v):real^N = v`] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN complex_boundary kk` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `boundary_complex kk:(real^N->bool)->bool`;
                     `v:real^N`; `y:real^N`; `s:real`] MOI_S4O_RAY_SUBC) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `~(s = &0)` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[ASSUME `UNIONS (boundary_complex kk) =
                          complex_boundary (kk:(real^N->bool)->bool)`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `segment[v:real^N,y]` THEN CONJ_TAC THENL
     [EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC MOI_S4O_RAY_IN_SEG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. &0 < r /\ r <= &1
                    ==> v + r % (y - v) IN complex_boundary (kk:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `boundary_complex kk:(real^N->bool)->bool`;
                   `v:real^N`; `y:real^N`; `r:real`] MOI_S4O_RAY_SUBC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS (boundary_complex kk) =
                        complex_boundary (kk:(real^N->bool)->bool)`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `!r. &0 < r /\ r <= &1
                   ==> v + r % (y - v) IN complex_boundary (kk:(real^N->bool)->bool)` THEN
  UNDISCH_TAC `!y:real^N. y IN L ==> ?!r. &0 < r /\ r <= &1 /\ v + r % (y - v) IN Sh` THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  REWRITE_TAC[ASSUME `(y:real^N) IN L`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Corners at the boundary edges: segments, cone traces, rim arcs          *)
(* and levels along segments from the edge midpoints.                     *)
(* ========================================================================= *)

(* Two segments from b meeting off b: one end lies on the other segment. *)

let MOI_S4O_SEG_MEET = prove
 (`!b y1 y2 x:real^N.
     x IN segment[b,y1] /\ x IN segment[b,y2] /\ ~(x = b)
     ==> y1 IN segment[b,y2] \/ y2 IN segment[b,y1]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u2:real` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(u1 = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x:real^N = b)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `x:real^N = (&1 - &0) % b + &0 % y1` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u2 = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x:real^N = b)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `x:real^N = (&1 - &0) % b + &0 % y2` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u1 % (y1 - b) = u2 % (y2 - b:real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `x:real^N = (&1 - u1) % b + u1 % y1` THEN
    UNDISCH_TAC `x:real^N = (&1 - u2) % b + u2 % y2` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `u1 <= u2 \/ u2 <= u1`) THENL
   [DISJ2_TAC THEN EXISTS_TAC `u1 / u2` THEN
    SUBGOAL_THEN `&0 < u2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `u2 % y2 = u2 % ((&1 - u1 / u2) % b + u1 / u2 % y1:real^N)` MP_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL; REAL_MUL_RID] THEN
      UNDISCH_TAC `u1 % (y1 - b) = u2 % (y2 - b:real^N)` THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]];
    DISJ1_TAC THEN EXISTS_TAC `u2 / u1` THEN
    SUBGOAL_THEN `&0 < u1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `u1 % y1 = u1 % ((&1 - u2 / u1) % b + u2 / u1 % y2:real^N)` MP_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL; REAL_MUL_RID] THEN
      UNDISCH_TAC `u1 % (y1 - b) = u2 % (y2 - b:real^N)` THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]]);;

(* The trace of a cone from v over X on a radial set L through X. *)

let MOI_S4O_CONE_TRACE = prove
 (`!(v:real^N) L X.
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     X SUBSET UNIONS {segment[v,y] | y | y IN L}
     ==> UNIONS {segment[v,x] | x | x IN X} INTER L SUBSET X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `?y:real^N. y IN L /\ x IN segment[v,y]` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `X SUBSET UNIONS {segment[v,y] | y | (y:real^N) IN L}` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN segment[v,y]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`segment[v:real^N,y]`; `v:real^N`; `x:real^N`]
      SEGMENT_SUBSET_CONVEX) THEN
    ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:real^N = y` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = y` ASSUME_TAC THENL
   [MATCH_MP_TAC BETWEEN_ANTISYM THEN EXISTS_TAC `v:real^N` THEN
    ONCE_REWRITE_TAC[BETWEEN_SYM] THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
    ASM_MESON_TAC[]]);;

(* The rim of the splitting disk of a boundary edge, outside |kk|: a PL arc *)
(* (the scaled copy of the arc of MOI_S4O_KOUT_ARC).                        *)

let MOI_S4O_RIM_ARC = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     segment[v,w] SUBSET complex_boundary kk
     ==> pl_cell_with_boundary 1
           (IMAGE (\y. midpoint(midpoint(v,w),y))
              (closure (UNIONS (simplicial_link (simplicial_link
                 (barycentric_subdivision tt) v) (midpoint(v,w))) DIFF UNIONS kk)))
           (IMAGE (\y. midpoint(midpoint(v,w),y))
              {simplex_barycentre s | s | s IN kk /\ aff_dim s = &2 /\
                                          segment[v,w] SUBSET s /\
                                          s SUBSET complex_boundary kk})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_KOUT_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FTA_CELL_PLH THEN
  EXISTS_TAC `\z:real^N. &2 % z - midpoint(v,w)` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_MIDPOINT_PLH THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S4O_CELL_POLY));;

(* Levels along a segment from b = midpoint(v,w) to a point y of K_w. *)

let MOI_S4O_SEG_LEVEL = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w y.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk /\
     y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v,w)))
     ==> IMAGE h (moi_s34_vb tt kk v) INTER segment[midpoint(v,w),y] =
         segment[midpoint(v,w),midpoint(midpoint(v,w),y)] /\
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
         segment[midpoint(v,w),y] = {midpoint(midpoint(v,w),y)} /\
         segment[midpoint(v,w),y] SUBSET
         UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> midpoint(v,w) + t % (y - midpoint(v,w)) IN
              UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                          midpoint(v:real^N,w) IN q} /\
            (midpoint(v,w) + t % (y - midpoint(v,w)) IN IMAGE h (moi_s34_vb tt kk v) <=>
             t <= &1 / &2) /\
            (midpoint(v,w) + t % (y - midpoint(v,w)) IN
               IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
             t = &1 / &2)`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4O_LEV_CONE THEN
    EXISTS_TAC `k:real^N->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `S = UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                              (b:real^N) IN q}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN segment[b,y] <=>
                           ?t. &0 <= t /\ t <= &1 /\ x = b + t % (y - b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`b:real^N`; `y:real^N`; `&1`; `x:real^N`]
      MOI_FTA_SEG_RAY) THEN
    REWRITE_TAC[REAL_MUL_RID; VECTOR_ARITH `b + &1 % (y - b):real^N = y`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN segment[b,midpoint(b,y)] <=>
                           ?t. &0 <= t /\ t <= &1 / &2 /\ x = b + t % (y - b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_S4O_MIDPOINT_RAY] THEN
    MP_TAC(ISPECL [`b:real^N`; `y:real^N`; `&1 / &2`; `x:real^N`]
      MOI_FTA_SEG_RAY) THEN
    DISCH_THEN SUBST1_TAC THEN EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `u * &1 / &2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&2 * t` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [ALL_TAC; EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN X_GEN_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `(x:real^N) IN Z` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S4O_MIDPOINT_RAY];
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2` o check (fun th -> is_forall(concl th) &&
        is_imp(snd(dest_forall(concl th))))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM MOI_S4O_MIDPOINT_RAY] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1 / &2` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[MOI_S4O_MIDPOINT_RAY]];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC]);;

(* A nonempty set all of whose elements equal a is {a}. *)

let MOI_S4O_SING_OF_ALL = prove
 (`!(s:A->bool) a. ~(s = {}) /\ (!x. x IN s ==> x = a) ==> s = {a}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[]);;

(* The trace of the boundary surface on the star of b = midpoint(v,w) in    *)
(* the link of v: the segments from b to the barycentres of the boundary   *)
(* triangles at the edge [v,w].                                             *)

let MOI_S4O_STB_CB_A = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} INTER complex_boundary kk SUBSET
         UNIONS {segment[midpoint(v,w),simplex_barycentre s] | s |
                 s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                 s SUBSET complex_boundary kk}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4O_BC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`; `q:real^N->bool`]
    MOI_S4O_STARB_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `q:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `boundary_complex kk:(real^N->bool)->bool`;
                 `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                               (c INTER boundary_complex kk))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN c INTER boundary_complex kk /\ ~(s = segment[v,w])
                     ==> s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                         s SUBSET complex_boundary kk`
  (LABEL_TAC "dimfact") THENL
   [X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN kk /\ s SUBSET complex_boundary kk`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) IN boundary_complex kk` THEN
      REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!s:real^N->bool. s IN c ==> segment[v,w] SUBSET s`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `w:real^N`; `s:real^N->bool`] MOI_S4O_SUPER_DIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[moi_bar_chain] THEN UNDISCH_TAC `(s:real^N->bool) IN c` THEN
      SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_IN_BOUNDARY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &3` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `s':real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s:real^N->bool. (s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                      s SUBSET complex_boundary kk) /\
                     c INTER boundary_complex kk SUBSET {segment[v,w],s}`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?s:real^N->bool. s IN c INTER boundary_complex kk /\
                                    ~(s = segment[v,w])` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN CONJ_TAC THENL
       [USE_THEN "dimfact" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `s':real^N->bool = segment[v,w]` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(s:real^N->bool) = &2 /\ aff_dim(s':real^N->bool) = &2`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "dimfact" (MP_TAC o SPEC `s:real^N->bool`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
          USE_THEN "dimfact" (MP_TAC o SPEC `s':real^N->bool`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) IN c /\ (s':real^N->bool) IN c` STRIP_ASSUME_TAC
      THENL
       [UNDISCH_TAC `(s:real^N->bool) IN c INTER boundary_complex kk` THEN
        UNDISCH_TAC `(s':real^N->bool) IN c INTER boundary_complex kk` THEN
        REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) IN tt /\ (s':real^N->bool) IN tt`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
        REWRITE_TAC[moi_bar_chain] THEN UNDISCH_TAC `(s:real^N->bool) IN c` THEN
        UNDISCH_TAC `(s':real^N->bool) IN c` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET s' \/ s' SUBSET s` MP_TAC THENL
       [MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
        REWRITE_TAC[moi_bar_chain] THEN
        DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o
          CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [MATCH_MP_TAC(MESON[] `(~(s = s') ==> F) ==> s':real^N->bool = s`) THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`; `s':real^N->bool`]
          MOI_S4O_NEST_DIM) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        MATCH_MP_TAC(MESON[] `(~(s' = s) ==> F) ==> s':real^N->bool = s`) THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s':real^N->bool`; `s:real^N->bool`]
          MOI_S4O_NEST_DIM) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `c INTER boundary_complex kk = {segment[v:real^N,w]}` ASSUME_TAC
      THENL
       [MATCH_MP_TAC MOI_S4O_SING_OF_ALL THEN
        CONJ_TAC THENL
         [DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^N) IN convex hull
            (IMAGE simplex_barycentre (c INTER boundary_complex kk))` THEN
            REWRITE_TAC[th; IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]);
          X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
            is_forall(concl th) && is_neg(snd(dest_forall(concl th))))) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `segment[v:real^N,w] SUBSET complex_boundary kk` ASSUME_TAC THENL
       [SUBGOAL_THEN `segment[v:real^N,w] IN boundary_complex kk` MP_TAC THENL
         [UNDISCH_TAC `c INTER boundary_complex kk = {segment[v:real^N,w]}` THEN
          SET_TAC[];
          REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `segment[v:real^N,w]`]
        MOI_S4O_IN_BOUNDARY) THEN
      ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`]
          MOI_S4O_TRI_BOUNDARY) THEN ASM_REWRITE_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `segment[midpoint(v:real^N,w),simplex_barycentre s]` THEN
  CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                               (c INTER boundary_complex kk))` THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> (x:real^N) IN t`) THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
  REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
  UNDISCH_TAC `c INTER boundary_complex kk SUBSET {segment[v:real^N,w],s}` THEN
  SET_TAC[]);;

let MOI_S4O_STB_CB_B = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> UNIONS {segment[midpoint(v,w),simplex_barycentre s] | s |
                 s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                 s SUBSET complex_boundary kk} SUBSET
         UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} INTER complex_boundary kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4O_BC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain tt {segment[v:real^N,w],s}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT; FINITE_EMPTY;
                IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[SEGMENT_EQ_EMPTY] THEN MESON_TAC[];
        DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
        REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(t:real^N->bool) IN u ==> t SUBSET UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
      `segment[midpoint(v:real^N,w),simplex_barycentre s]`] MOI_S4O_STARB_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `{segment[v:real^N,w],s}` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SEGMENT; SEGMENT_CONVEX_HULL]];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `segment[v:real^N,w] SUBSET s` THEN
      MP_TAC(ISPECL [`v:real^N`; `w:real^N`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`;
                            `{segment[v:real^N,w],s}`] THEN
      ASM_REWRITE_TAC[IN_INSERT]]]);;

let MOI_S4O_STB_CB = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                     midpoint(v,w) IN q} INTER complex_boundary kk =
         UNIONS {segment[midpoint(v,w),simplex_barycentre s] | s |
                 s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                 s SUBSET complex_boundary kk}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[MOI_S4O_STB_CB_A; MOI_S4O_STB_CB_B]);;

(* The boundary of a PL cell lies in the cell. *)

let MOI_S4O_CELL_BSUB = prove
 (`!n (c:real^N->bool) b. pl_cell_with_boundary n c b ==> b SUBSET c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `c:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[relative_frontier] THEN
  SUBGOAL_THEN `closed (k:real^N->bool)`
    (fun th -> REWRITE_TAC[MATCH_MP CLOSURE_CLOSED th]) THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT; COMPACT_IMP_CLOSED];
    SET_TAC[]]);;

(* Names for the rim of the outer splitting disk of an edge [v,w] in the   *)
(* h-picture, for the corner (the cone from midpoint(v,w) over the rim) and *)
(* for the star of midpoint(v,w) in the link of v.                          *)

let moi_s4o_rim = new_definition
 `moi_s4o_rim (tt:(real^N->bool)->bool) kk (v:real^N) w =
    IMAGE (\y. midpoint(midpoint(v,w),y))
      (closure (UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                        (midpoint(v,w))) DIFF UNIONS kk))`;;

let moi_s4o_corner = new_definition
 `moi_s4o_corner (tt:(real^N->bool)->bool) kk (v:real^N) w =
    UNIONS {segment[midpoint(v,w),x] | x | x IN moi_s4o_rim tt kk v w}`;;

let moi_s4o_stb = new_definition
 `moi_s4o_stb (tt:(real^N->bool)->bool) (v:real^N) w =
    UNIONS {q | q IN simplicial_link (barycentric_subdivision tt) v /\
                midpoint(v,w) IN q}`;;

(* At an interior edge the star of the midpoint misses the boundary. *)

let MOI_S4O_STB_CB_INT = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     ~(segment[v,w] SUBSET complex_boundary kk)
     ==> moi_s4o_stb tt v w INTER complex_boundary kk = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4o_stb] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_STB_CB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EMPTY_UNIONS; IN_ELIM_THM] THEN ASM SET_TAC[]);;

(* The two boundary triangles at a boundary edge [v,w], their barycentres   *)
(* on the link circle K_w.                                                  *)

let MOI_S4O_BTRI_PAIR = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     segment[v,w] SUBSET complex_boundary kk
     ==> ?s1 s2. ~(s1 = s2) /\
                 {s | s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                      s SUBSET complex_boundary kk} = {s1,s2} /\
                 ~(simplex_barycentre s1 = simplex_barycentre s2) /\
                 simplex_barycentre s1 IN
                   UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                           (midpoint(v,w))) /\
                 simplex_barycentre s2 IN
                   UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                           (midpoint(v,w))) /\
                 s1 IN kk /\ aff_dim s1 = &2 /\ segment[v,w] SUBSET s1 /\
                 s1 SUBSET complex_boundary kk /\
                 s2 IN kk /\ aff_dim s2 = &2 /\ segment[v,w] SUBSET s2 /\
                 s2 SUBSET complex_boundary kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `segment[v:real^N,w]`] MOI_S4O_BEDGE_TWO) THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT; AFF_DIM_SEGMENT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {s:real^N->bool | s IN kk /\ aff_dim s = &2 /\
                                         segment[v,w] SUBSET s /\
                                         s SUBSET complex_boundary kk}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN EXISTS_TAC `kk:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
        UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
        UNDISCH_TAC `segment[v:real^N,w] SUBSET s` THEN
        MP_TAC(ISPECL [`v:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{s:real^N->bool | s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                                  s SUBSET complex_boundary kk}` MOI_S4O_CARD2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                                 s SUBSET complex_boundary kk <=> s = s1 \/ s = s2`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `{s1:real^N->bool,s2}`)) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1 IN kk /\ aff_dim s1 = &2 /\ segment[v,w] SUBSET s1 /\
                 s1 SUBSET complex_boundary kk) /\
                (s2 IN kk /\ aff_dim s2 = &2 /\ segment[v:real^N,w] SUBSET s2 /\
                 s2 SUBSET complex_boundary kk)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                                 s SUBSET complex_boundary kk
                                 ==> simplex_barycentre s IN
                   UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                           (midpoint(v,w)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `s:real^N->bool`] MOI_S4O_K_BTRI) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_TRI_BOUNDARY) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_SIMP_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(s1:real^N->bool = s2)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTA_BARY_INJ THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(s1:real^N->bool) IN kk` THEN SET_TAC[];
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(s2:real^N->bool) IN kk` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S4O_DIM_NONEMPTY THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4O_DIM_NONEMPTY THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[]]);;

(* A comprehension over a two-element alternative. *)

let MOI_S4O_GSPEC_PAIR = prove
 (`!(f:(real^N->bool)->B) a b. {f s | s | s = a \/ s = b} = {f a, f b}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `a:real^N->bool`; EXISTS_TAC `b:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The corner at a boundary edge [v,w] in the h-picture: the cone from     *)
(* b = midpoint(v,w) over the rim arc, a PL disk whose boundary is the rim *)
(* and the two half segments of the boundary link circle at b.             *)

let MOI_S4O_CORNER = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk /\ segment[v,w] SUBSET complex_boundary kk
     ==> ?p q. ~(p = q) /\ ~(p = midpoint(v,w)) /\ ~(q = midpoint(v,w)) /\
               pl_cell_with_boundary 1 (moi_s4o_rim tt kk v w) {p,q} /\
               pl_cell_with_boundary 2 (moi_s4o_corner tt kk v w)
                 (moi_s4o_rim tt kk v w UNION segment[midpoint(v,w),p] UNION
                  segment[midpoint(v,w),q]) /\
               moi_s4o_corner tt kk v w SUBSET
                 IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w /\
               moi_s4o_corner tt kk v w INTER complex_boundary kk =
                 segment[midpoint(v,w),p] UNION segment[midpoint(v,w),q] /\
               IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w INTER
                 complex_boundary kk =
                 segment[midpoint(v,w),p] UNION segment[midpoint(v,w),q] /\
               IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                 (segment[midpoint(v,w),p] UNION segment[midpoint(v,w),q]) = {p,q} /\
               moi_s4o_rim tt kk v w SUBSET
                 IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
               segment[p,midpoint(v,w)] INTER segment[midpoint(v,w),q] SUBSET
                 {midpoint(v,w)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_BTRI_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN kk /\ aff_dim s = &2 /\ segment[v,w] SUBSET s /\
                                 s SUBSET complex_boundary kk <=> s = s1 \/ s = s2`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `{s1:real^N->bool,s2}`)) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                     (midpoint(v,w)))
        ==> IMAGE h (moi_s34_vb tt kk v) INTER segment[midpoint(v,w),y] =
            segment[midpoint(v,w),midpoint(midpoint(v,w),y)] /\
            IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
            segment[midpoint(v,w),y] = {midpoint(midpoint(v:real^N,w),y)} /\
            segment[midpoint(v,w),y] SUBSET moi_s4o_stb tt v w`
  (LABEL_TAC "seg") THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s4o_stb] THEN
    MATCH_MP_TAC MOI_S4O_SEG_LEVEL THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_STB_CB) THEN
  ASM_REWRITE_TAC[GSYM moi_s4o_stb] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_RIM_ARC) THEN
  ASM_REWRITE_TAC[GSYM moi_s4o_rim] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`simplicial_link (barycentric_subdivision tt) (v:real^N)`;
                 `midpoint(v:real^N,w)`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (b:real^N))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `S = moi_s4o_stb tt (v:real^N) w` THEN
  ABBREV_TAC `rim = moi_s4o_rim tt kk (v:real^N) w` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_S4O_GSPEC_PAIR; IMAGE_CLAUSES; UNIONS_2]) THEN
  REWRITE_TAC[MOI_S4O_GSPEC_PAIR; UNIONS_2] THEN
  SUBGOAL_THEN `IMAGE (\y:real^N. midpoint(b,y)) (closure (K DIFF UNIONS kk)) = rim`
  ASSUME_TAC THENL
   [EXPAND_TAC "rim" THEN REWRITE_TAC[moi_s4o_rim] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure ((K:real^N->bool) DIFF UNIONS kk) SUBSET K` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN rim ==> ?y. y IN K /\ x = midpoint(b,y)`
  (LABEL_TAC "inrim") THENL
   [GEN_TAC THEN
    REWRITE_TAC[SYM(ASSUME `IMAGE (\y:real^N. midpoint(b,y))
                              (closure (K DIFF UNIONS kk)) = rim`); IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN closure (K DIFF UNIONS kk)` THEN
    UNDISCH_TAC `closure ((K:real^N->bool) DIFF UNIONS kk) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN K ==> midpoint(b,y) IN Z /\
                                      segment[b,midpoint(b,y)] SUBSET Y INTER S /\
                                      segment[b,midpoint(b,y)] SUBSET segment[b,y]`
  (LABEL_TAC "mid") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "seg" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `segment[b,midpoint(b,y)] SUBSET segment[b:real^N,y]` ASSUME_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `Z INTER segment[b,y] = {midpoint(b:real^N,y)}` THEN SET_TAC[];
      UNDISCH_TAC `Y INTER segment[b,y] = segment[b:real^N,midpoint(b,y)]` THEN
      UNDISCH_TAC `segment[b:real^N,y] SUBSET S` THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rim:real^N->bool) SUBSET Z` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(fun th -> USE_THEN "inrim" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "mid" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPEC `simplex_barycentre s1:real^N`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPEC `simplex_barycentre s2:real^N`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `p = midpoint(b:real^N,simplex_barycentre s1)` THEN
  ABBREV_TAC `q = midpoint(b:real^N,simplex_barycentre s2)` THEN
  SUBGOAL_THEN `segment[b,p] SUBSET segment[b:real^N,simplex_barycentre s1] /\
                segment[b,q] SUBSET segment[b:real^N,simplex_barycentre s2]`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN EXPAND_TAC "q" THEN CONJ_TAC THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^N = q)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN EXPAND_TAC "q" THEN
    ASM_REWRITE_TAC[MOI_FTA_MIDPOINT_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^N = b) /\ ~(q = b)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN EXPAND_TAC "q" THEN REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN
    MP_TAC(ASSUME `~(b:real^N IN K)`) THEN
    MP_TAC(ASSUME `simplex_barycentre s1 IN (K:real^N->bool)`) THEN
    MP_TAC(ASSUME `simplex_barycentre s2 IN (K:real^N->bool)`) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p IN (Z:real^N->bool) /\ q IN Z` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `Z INTER segment[b,simplex_barycentre s1] = {p:real^N}`) THEN
    MP_TAC(ASSUME `Z INTER segment[b,simplex_barycentre s2] = {q:real^N}`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b IN (Z:real^N->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(b:real^N) IN Z INTER segment[b,simplex_barycentre s1]` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT];
      REWRITE_TAC[ASSUME `Z INTER segment[b,simplex_barycentre s1] = {p:real^N}`;
                  IN_SING] THEN
      DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN rim /\ q IN rim` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `rim:real^N->bool`; `{p:real^N,q}`] MOI_S4O_CELL_BSUB) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4o_corner tt kk v w = UNIONS {segment[b,x] | x | (x:real^N) IN rim}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_s4o_corner] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {segment[b,x] | x | (x:real^N) IN rim} SUBSET Y INTER S`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "inrim" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "mid" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y INTER (segment[b,simplex_barycentre s1] UNION
                         segment[b,simplex_barycentre s2]) =
                segment[b:real^N,p] UNION segment[b,q]` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[ASSUME `Y INTER segment[b,simplex_barycentre s1] = segment[b:real^N,p]`;
                ASSUME `Y INTER segment[b,simplex_barycentre s2] = segment[b:real^N,q]`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_S4O_CONE_ARC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `s1:real^N->bool` AFF_DIM_LE_UNIV) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_LE];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(rim:real^N->bool) SUBSET Z` THEN
      UNDISCH_TAC `~(b IN (Z:real^N->bool))` THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `x':real^N`] THEN STRIP_TAC THEN
      USE_THEN "inrim" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      USE_THEN "seg" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      USE_THEN "mid" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `(x':real^N) IN Z INTER segment[b,y]` MP_TAC THENL
       [UNDISCH_TAC `(x':real^N) IN rim` THEN UNDISCH_TAC `(rim:real^N->bool) SUBSET Z` THEN
        UNDISCH_TAC `(x':real^N) IN segment[b,midpoint(b,y)]` THEN
        UNDISCH_TAC `segment[b,midpoint(b,y)] SUBSET segment[b:real^N,y]` THEN SET_TAC[];
        REWRITE_TAC[ASSUME `Z INTER segment[b,y] = {midpoint(b:real^N,y)}`; IN_SING]]];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `UNIONS {segment[b,x] | x | (x:real^N) IN rim} SUBSET Y INTER S`) THEN
      MP_TAC(ASSUME `S INTER complex_boundary kk =
                     segment[b,simplex_barycentre s1] UNION
                     segment[b:real^N,simplex_barycentre s2]`) THEN
      MP_TAC(ASSUME `Y INTER (segment[b,simplex_barycentre s1] UNION
                              segment[b,simplex_barycentre s2]) =
                     segment[b:real^N,p] UNION segment[b,q]`) THEN
      SET_TAC[];
      REWRITE_TAC[UNION_SUBSET; SUBSET_INTER] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(t:real^N->bool) IN u ==> t SUBSET UNIONS u`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[];
        MP_TAC(ASSUME `segment[b,p] SUBSET segment[b:real^N,simplex_barycentre s1]`) THEN
        MP_TAC(ASSUME `S INTER complex_boundary kk =
                       segment[b,simplex_barycentre s1] UNION
                       segment[b:real^N,simplex_barycentre s2]`) THEN
        SET_TAC[];
        MATCH_MP_TAC(SET_RULE `(t:real^N->bool) IN u ==> t SUBSET UNIONS u`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[];
        MP_TAC(ASSUME `segment[b,q] SUBSET segment[b:real^N,simplex_barycentre s2]`) THEN
        MP_TAC(ASSUME `S INTER complex_boundary kk =
                       segment[b,simplex_barycentre s1] UNION
                       segment[b:real^N,simplex_barycentre s2]`) THEN
        SET_TAC[]]];
    MP_TAC(ASSUME `S INTER complex_boundary kk =
                   segment[b,simplex_barycentre s1] UNION
                   segment[b:real^N,simplex_barycentre s2]`) THEN
    MP_TAC(ASSUME `Y INTER (segment[b,simplex_barycentre s1] UNION
                            segment[b,simplex_barycentre s2]) =
                   segment[b:real^N,p] UNION segment[b,q]`) THEN
    SET_TAC[];
    MP_TAC(ASSUME `segment[b,p] SUBSET segment[b:real^N,simplex_barycentre s1]`) THEN
    MP_TAC(ASSUME `segment[b,q] SUBSET segment[b:real^N,simplex_barycentre s2]`) THEN
    MP_TAC(ASSUME `Z INTER segment[b,simplex_barycentre s1] = {p:real^N}`) THEN
    MP_TAC(ASSUME `Z INTER segment[b,simplex_barycentre s2] = {q:real^N}`) THEN
    MP_TAC(ISPECL [`b:real^N`; `p:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`b:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ASSUME `p IN (Z:real^N->bool)`) THEN MP_TAC(ASSUME `q IN (Z:real^N->bool)`) THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[ISPECL [`p:real^N`; `b:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`b:real^N`; `p:real^N`; `q:real^N`; `x:real^N`] MOI_S4O_SEG_MEET) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(p:real^N) IN Z INTER segment[b,simplex_barycentre s2]` MP_TAC THENL
       [MP_TAC(ASSUME `segment[b,q] SUBSET segment[b:real^N,simplex_barycentre s2]`) THEN
        MP_TAC(ASSUME `p IN (Z:real^N->bool)`) THEN
        MP_TAC(ASSUME `(p:real^N) IN segment[b,q]`) THEN SET_TAC[];
        REWRITE_TAC[ASSUME `Z INTER segment[b,simplex_barycentre s2] = {q:real^N}`;
                    IN_SING] THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(q:real^N) IN Z INTER segment[b,simplex_barycentre s1]` MP_TAC THENL
       [MP_TAC(ASSUME `segment[b,p] SUBSET segment[b:real^N,simplex_barycentre s1]`) THEN
        MP_TAC(ASSUME `q IN (Z:real^N->bool)`) THEN
        MP_TAC(ASSUME `(q:real^N) IN segment[b,p]`) THEN SET_TAC[];
        REWRITE_TAC[ASSUME `Z INTER segment[b,simplex_barycentre s1] = {p:real^N}`;
                    IN_SING] THEN
        DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[]]]]);;

(* ========================================================================= *)
(* The boundary curve of the outer patch in the h-picture is a PL          *)
(* circle (the corner disks glued onto the cone disk over c).             *)
(* ========================================================================= *)

(* The gluing data at a boundary edge [v,w]: the corner disk is attached   *)
(* to the cone disk over c along the arc polygonal_path [p; b; q].         *)

let MOI_S4O_CORNER_GLUE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk /\ segment[v,w] SUBSET complex_boundary kk
     ==> ?ga. moi_fsa_disk (moi_s4o_corner tt kk v w)
                (moi_s4o_rim tt kk v w UNION path_image ga) /\
              arc ga /\ pl_map_on (interval[vec 0,vec 1]) ga /\
              path_image ga =
                IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w INTER
                complex_boundary kk /\
              moi_s4o_corner tt kk v w SUBSET
                IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w /\
              moi_s4o_corner tt kk v w INTER complex_boundary kk = path_image ga /\
              moi_s4o_rim tt kk v w INTER path_image ga =
                {pathstart ga,pathfinish ga} /\
              IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER path_image ga =
                {pathstart ga,pathfinish ga} /\
              moi_s4o_rim tt kk v w SUBSET
                IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
              {pathstart ga,pathfinish ga} SUBSET moi_s4o_rim tt kk v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`] MOI_S4O_CORNER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `polygonal_path [p:real^N; midpoint(v,w); q]` THEN
  REWRITE_TAC[polygonal_path] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATHSTART_JOIN;
           PATHFINISH_JOIN; PATH_IMAGE_LINEPATH] THEN
  SUBGOAL_THEN `segment[p,midpoint(v,w)] UNION segment[midpoint(v,w),q] =
                segment[midpoint(v,w),p] UNION segment[midpoint(v:real^N,w),q]`
  SUBST1_TAC THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SS2_FSA_OF_CELL THEN
    REWRITE_TAC[UNION_ASSOC] THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_LINEPATH; ARC_LINEPATH_EQ;
             PATH_IMAGE_LINEPATH] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `[p:real^N; midpoint(v,w); q]` MOI_PL2_PL_POLYGONAL_PATH) THEN
    REWRITE_TAC[polygonal_path];
    MP_TAC(ISPECL [`1`; `moi_s4o_rim tt kk v (w:real^N)`; `{p:real^N,q}`]
      MOI_S4O_CELL_BSUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `moi_s4o_rim tt kk v w SUBSET
                   IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`) THEN
    MP_TAC(ASSUME `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                   INTER (segment[midpoint(v,w),p] UNION segment[midpoint(v,w),q]) =
                   {p,q}`) THEN
    MP_TAC(ISPECL [`midpoint(v:real^N,w)`; `p:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`midpoint(v:real^N,w)`; `q:real^N`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `{p:real^N,q} SUBSET moi_s4o_rim tt kk v w` THEN SET_TAC[];
    MP_TAC(ISPECL [`1`; `moi_s4o_rim tt kk v (w:real^N)`; `{p:real^N,q}`]
      MOI_S4O_CELL_BSUB) THEN
    ASM_REWRITE_TAC[]]);;

(* The boundary edges at v form a finite index set. *)

let MOI_S4O_BEDGES_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> FINITE {w | ~(w = v) /\ segment[v,w] IN kk /\
                     segment[v,w] SUBSET complex_boundary kk}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. segment[v,w]`;
                 `{w | ~(w = v) /\ segment[v,w] IN kk /\
                       segment[v,w] SUBSET complex_boundary (kk:(real^N->bool)->bool)}`]
    FINITE_IMAGE_INJ_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; SEGMENT_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S4O_PAIR_EQ) THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:real^N->bool | r IN tt /\ v IN r}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4O_STAR_FINITE_TT THEN EXISTS_TAC `kk:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `segment[v:real^N,w] IN kk` THEN SET_TAC[]]);;

(* The boundary curve of the outer patch in the h-picture is a PL circle:  *)
(* glue the corner disks onto the cone disk over c.                         *)

let MOI_S4O_JH_CIRCLE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     moi_s4o_lev tt kk v h k
     ==> pl_sphere 1
           ((IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
             complex_boundary kk) UNION
            UNIONS (IMAGE (\w. moi_s4o_rim tt kk v w)
                      {w | ~(w = v) /\ segment[v,w] IN kk /\
                           segment[v,w] SUBSET complex_boundary kk}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_BEDGES_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w. w IN {w | ~(w = v) /\ segment[v,w] IN kk /\
                  segment[v,w] SUBSET complex_boundary kk}
        ==> ?ga. moi_fsa_disk (moi_s4o_corner tt kk v w)
                   (moi_s4o_rim tt kk v w UNION path_image ga) /\
                 arc ga /\ pl_map_on (interval[vec 0,vec 1]) ga /\
                 path_image ga =
                   IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w INTER
                   complex_boundary kk /\
                 moi_s4o_corner tt kk v w SUBSET
                   IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w /\
                 moi_s4o_corner tt kk v w INTER complex_boundary kk = path_image ga /\
                 moi_s4o_rim tt kk v w INTER path_image ga =
                   {pathstart ga,pathfinish ga} /\
                 IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER path_image ga =
                   {pathstart ga,pathfinish ga} /\
                 moi_s4o_rim tt kk v w SUBSET
                   IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                 {pathstart ga,pathfinish ga} SUBSET moi_s4o_rim tt kk v w`
  MP_TAC THENL
   [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4O_CORNER_GLUE THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ga:real^N->real^1->real^N` (LABEL_TAC "ga")) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_C_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `c = ((Z:real^N->bool) UNION (Y INTER L)) INTER complex_boundary kk` THEN
  ABBREV_TAC `ix = {w | ~(w = v) /\ segment[v,w] IN kk /\
                        segment[v:real^N,w] SUBSET complex_boundary kk}` THEN
  ABBREV_TAC `d0 = UNIONS {segment[v,x] | x | (x:real^N) IN c}` THEN
  SUBGOAL_THEN `(L:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN EXPAND_TAC "St" THEN REWRITE_TAC[MOI_S4O_LINK_IN_STAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. moi_s4o_stb tt v w SUBSET L` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s4o_stb] THEN EXPAND_TAC "L" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `(Z:real^N->bool) SUBSET St` THEN
    UNDISCH_TAC `(L:real^N->bool) SUBSET St` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N IN c) /\
                (!x y. x IN c /\ y IN c /\ y IN segment[v,x] ==> y = x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `~(v:real^N IN Z UNION Y INTER L)` THEN
    UNDISCH_TAC `!x y:real^N. x IN Z UNION Y INTER L /\ y IN Z UNION Y INTER L /\
                              y IN segment[v,x] ==> y = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d0 INTER L SUBSET (c:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN MATCH_MP_TAC MOI_S4O_CONE_TRACE THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS {segment[v,y] | y | (y:real^N) IN L} = St`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET d0` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `segment[v:real^N,x]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_disk d0 (c:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_FSA_OF_CELL THEN EXPAND_TAC "d0" THEN
    MP_TAC(ISPECL [`1`; `c:real^N->bool`; `v:real^N`] MOI_FTA_CONE_CELL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) IN complex_boundary kk` THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d0:real^N->bool`; `c:real^N->bool`;
                 `\w:real^N. moi_s4o_corner tt kk v w`;
                 `\w:real^N. moi_s4o_rim tt kk v w`;
                 `ga:real^N->real^1->real^N`; `ix:real^N->bool`] MOI_S4O_GLUE_MANY) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "ga" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ASSUME `path_image((ga:real^N->real^1->real^N) w) =
                       Y INTER moi_s4o_stb tt v w INTER complex_boundary kk`) THEN
        MP_TAC(SPEC `w:real^N` (ASSUME `!w:real^N. moi_s4o_stb tt v w SUBSET L`)) THEN
        MP_TAC(ASSUME `((Z:real^N->bool) UNION Y INTER L) INTER complex_boundary kk = c`) THEN
        SET_TAC[];
        MP_TAC(ASSUME `path_image((ga:real^N->real^1->real^N) w) =
                       Y INTER moi_s4o_stb tt v w INTER complex_boundary kk`) THEN
        MP_TAC(ASSUME `moi_s4o_corner tt kk v w SUBSET
                       (Y:real^N->bool) INTER moi_s4o_stb tt v w`) THEN
        MP_TAC(ASSUME `moi_s4o_corner tt kk v w INTER complex_boundary kk =
                       path_image((ga:real^N->real^1->real^N) w)`) THEN
        MP_TAC(SPEC `w:real^N` (ASSUME `!w:real^N. moi_s4o_stb tt v w SUBSET L`)) THEN
        MP_TAC(ASSUME `d0 INTER L SUBSET (c:real^N->bool)`) THEN
        MP_TAC(ASSUME `(c:real^N->bool) SUBSET d0`) THEN
        MP_TAC(ASSUME `((Z:real^N->bool) UNION Y INTER L) INTER complex_boundary kk = c`) THEN
        SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      MAP_EVERY X_GEN_TAC [`w:real^N`; `w':real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "ga" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      USE_THEN "ga" (MP_TAC o SPEC `w':real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`; `w':real^N`]
        MOI_S4O_LEV_DISJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^N) IN ix` THEN UNDISCH_TAC `(w':real^N) IN ix` THEN
        EXPAND_TAC "ix" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM moi_s4o_stb] THEN
      MP_TAC(ASSUME `moi_s4o_corner tt kk v w SUBSET
                     (Y:real^N->bool) INTER moi_s4o_stb tt v w`) THEN
      MP_TAC(ASSUME `moi_s4o_corner tt kk v w' SUBSET
                     (Y:real^N->bool) INTER moi_s4o_stb tt v w'`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SS2_CELL_OF_FSA o
    CONJ (ASSUME `2 <= dimindex(:N)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[ARITH_RULE `1 + 1 = 2`]
    (SPEC `1` MOI_S4O_CELL_SPHERE))) THEN
  MATCH_MP_TAC(MESON[] `s = t ==> pl_sphere 1 s ==> pl_sphere 1 (t:real^N->bool)`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "notin")) THEN
    SUBGOAL_THEN `(x:real^N) IN complex_boundary kk /\ (x IN Z \/ x IN Y /\ x IN L)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN c` THEN EXPAND_TAC "c" THEN
      REWRITE_TAC[IN_INTER; IN_UNION] THEN MESON_TAC[];
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`; `x:real^N`] MOI_S4O_LEV_WALLS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM moi_s4o_stb] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^N) IN ix` ASSUME_TAC THENL
     [EXPAND_TAC "ix" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`] MOI_S4O_STB_CB_INT) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `(x:real^N) IN moi_s4o_stb tt v w`) THEN
      MP_TAC(ASSUME `(x:real^N) IN complex_boundary kk`) THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "ga" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `~((x:real^N) IN path_image((ga:real^N->real^1->real^N) w) DIFF
                                  {pathstart (ga w),pathfinish (ga w)})`
    ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "notin" MP_TAC THEN REWRITE_TAC[] THEN
      EXISTS_TAC `path_image((ga:real^N->real^1->real^N) w) DIFF
                  {pathstart (ga w),pathfinish (ga w)}` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `path_image((ga:real^N->real^1->real^N) w) =
                   Y INTER moi_s4o_stb tt v w INTER complex_boundary kk`) THEN
    MP_TAC(ASSUME `{pathstart((ga:real^N->real^1->real^N) w),pathfinish (ga w)} SUBSET
                   moi_s4o_rim tt kk v w`) THEN
    MP_TAC(ASSUME `moi_s4o_rim tt kk v (w:real^N) SUBSET Z`) THEN
    MP_TAC(ASSUME `(x:real^N) IN Y`) THEN
    MP_TAC(ASSUME `(x:real^N) IN moi_s4o_stb tt v w`) THEN
    MP_TAC(ASSUME `(x:real^N) IN complex_boundary kk`) THEN
    UNDISCH_TAC `~((x:real^N) IN path_image((ga:real^N->real^1->real^N) w) DIFF
                                  {pathstart (ga w),pathfinish (ga w)})` THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[IN_INTER; IN_UNION];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      USE_THEN "ga" (MP_TAC o SPEC `i:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `t:real^N->bool`)) THEN
      MP_TAC(ASSUME `(Z:real^N->bool) INTER path_image((ga:real^N->real^1->real^N) i) =
                     {pathstart (ga i),pathfinish (ga i)}`) THEN
      MP_TAC(ASSUME `(x:real^N) IN Z`) THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* Level functions on star simplices, connectedness of K_w,                *)
(* interior edges and the frontier fact FR for the outer patch.           *)
(* ========================================================================= *)

(* The level function on a simplex of the closed star of v. *)

let MOI_S4O_LEV_STAR = prove
 (`!(tt:(real^N->bool)->bool) kk v h k c.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     moi_bar_chain tt c /\ {v} IN c
     ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
             f v = &1 /\
             (!s. s IN c ==> f (simplex_barycentre s) =
                             if s IN skeleton 1 kk then &1 else &0) /\
             (!x. x IN convex hull (IMAGE simplex_barycentre c)
                  ==> (x IN IMAGE h (moi_s34_vb tt kk v) <=> &1 / &2 <= f x) /\
                      (x IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
                       f x = &1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `convex hull (IMAGE simplex_barycentre
      (c:(real^N->bool)->bool))` o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [moi_s4o_lev]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt /\ ~(s = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_S4O_BARY_IN_GRAPH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
                   `simplex_barycentre (s:real^N->bool)`] MOI_FTA_BS_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "moi_s34_bd" th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "real_le" th &&
      moi_s4o_has_const "moi_s34_vb" th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* PL circles are connected. *)

let MOI_S4O_SPHERE1_CONNECTED = prove
 (`!K:real^N->bool. pl_sphere 1 K ==> connected K`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_PATH_IMAGE THEN
  ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]);;

(* At an interior edge [v,w] of kk the link circle K_w lies in |kk| and   *)
(* every simplex of tt containing the edge is in kk.                       *)

let MOI_S4O_EDGE_IN = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     ~(segment[v,w] SUBSET complex_boundary kk)
     ==> UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                 (midpoint(v,w))) SUBSET UNIONS kk /\
         (!q. q IN tt /\ segment[v,w] SUBSET q ==> q IN kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `segment[v:real^N,w] IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (midpoint(v:real^N,w)))` THEN
  SUBGOAL_THEN `pl_sphere 1 (K:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N->bool) SUBSET
                UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
    REWRITE_TAC[MOI_S4O_LINK_IN_STAR] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[simplicial_link] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN tt /\ segment[v,w] SUBSET q /\ ~(q = segment[v,w])
                    ==> simplex_barycentre q IN (K:real^N->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `{q:real^N->bool}`] MOI_S4O_K_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_bar_chain; SING_SUBSET; FINITE_SING; IN_SING] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          UNDISCH_TAC `segment[v:real^N,w] SUBSET {}` THEN
          REWRITE_TAC[SUBSET_EMPTY; SEGMENT_EQ_EMPTY];
          MESON_TAC[SUBSET_REFL]];
        GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; SING_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N->bool) SUBSET UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y0:real^N) IN UNIONS kk` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `K:real^N->bool` MOI_S4O_SPHERE1_CONNECTED) THEN
    ASM_REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} INTER UNIONS kk`;
      `closure ((K:real^N->bool) DIFF UNIONS kk)`] THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
        MOI_S4O_STAR_SUB) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPEC `(K:real^N->bool) DIFF UNIONS kk` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(K:real^N->bool) SUBSET
                   UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}` THEN
      SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`; `x:real^N`] MOI_S4O_K_FRONT) THEN
      ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THEN
      UNDISCH_TAC `~(segment[v:real^N,w] SUBSET complex_boundary kk)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_TRI_BOUNDARY) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `segment[v:real^N,w]`] MOI_S4O_KK_PURE_GEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        REWRITE_TAC[SEGMENT_EQ_SING] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `simplex_barycentre r:real^N` THEN
      SUBGOAL_THEN `simplex_barycentre r IN (K:real^N->bool)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
          UNDISCH_TAC `(r:real^N->bool) IN kk` THEN SET_TAC[];
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `aff_dim(segment[v:real^N,w]) = &3` THEN
          REWRITE_TAC[AFF_DIM_SEGMENT] THEN COND_CASES_TAC THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
      MAP_EVERY EXISTS_TAC [`kk:(real^N->bool)->bool`; `{r:real^N->bool}`] THEN
      ASM_SIMP_TAC[MOI_FTA_LF_BAR; IN_SING; moi_bar_chain; SING_SUBSET; FINITE_SING] THEN
      CONJ_TAC THENL
       [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
        REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        MESON_TAC[SUBSET_REFL]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y0:real^N` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `q = segment[v:real^N,w]` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
  EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `segment[v:real^N,w] SUBSET {}` THEN
    REWRITE_TAC[SUBSET_EMPTY; SEGMENT_EQ_EMPTY];
    UNDISCH_TAC `(K:real^N->bool) SUBSET UNIONS kk` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N) IN K ==> K SUBSET U ==> x IN U`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A simplex phi of kk at the boundary vertex v that is a proper face of a *)
(* simplex of tt outside kk lies in the boundary surface.                   *)

let MOI_S4O_FR_PHI = prove
 (`!(tt:(real^N->bool)->bool) kk v phi r.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     phi IN kk /\ v IN phi /\ r IN tt /\ ~(r IN kk) /\ phi SUBSET r
     ==> phi SUBSET complex_boundary kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:real^N->bool) IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(phi:real^N->bool) IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(phi:real^N->bool) < aff_dim(r:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_NEST_DIM THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &3` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_TT_DIM THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= aff_dim(phi:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `phi:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `phi:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    SUBGOAL_THEN `~(phi:real^N->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(phi:real^N->bool) = &0 \/ aff_dim phi = &1 \/ aff_dim phi = &2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= aff_dim(phi:real^N->bool)` THEN
    UNDISCH_TAC `aff_dim(phi:real^N->bool) < aff_dim(r:real^N->bool)` THEN
    UNDISCH_TAC `aff_dim(r:real^N->bool) <= &3` THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(v:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[SING_SUBSET];
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                  `phi:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `v:real^N = a \/ v = b` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM EXTREME_POINT_OF_SEGMENT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `phi:real^N->bool`)) THEN
      MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[MOI_FTA_LF_BAR];
      ALL_TAC] THEN
    SUBGOAL_THEN `?w:real^N. ~(w = v) /\ phi = segment[v,w]` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> is_disj(concl th)))
      THENL
       [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[SEGMENT_SYM]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`] MOI_S4O_EDGE_IN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[SYM(ASSUME `phi = segment[v:real^N,w]`)] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT2) THEN
    ASM_MESON_TAC[];
    MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `phi:real^N->bool`] MOI_S4O_TRI_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `phi:real^N->bool`] MOI_S4O_BTRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(phi:real^N->bool) < aff_dim(r:real^N->bool)` THEN
    UNDISCH_TAC `aff_dim(r:real^N->bool) <= &3` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* Points of |kk| in the closed star of v that are limits of points of the *)
(* star off |kk| lie in the boundary surface.                               *)

let MOI_S4O_FR = prove
 (`!(tt:(real^N->bool)->bool) kk v x.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     x IN UNIONS kk /\
     x IN closure (UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} DIFF UNIONS kk)
     ==> x IN complex_boundary kk`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {m:real^N->bool | m IN barycentric_subdivision tt /\ v IN m}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_fta_cstar (barycentric_subdivision tt) (v:real^N)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_fta_cstar] THEN
    X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    UNDISCH_TAC `lf_simplicial_complex (barycentric_subdivision tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `m:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m:real^N->bool. m IN barycentric_subdivision tt /\ v IN m /\
                                 x IN closure (m DIFF UNIONS kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN closure (UNIONS {s | s IN barycentric_subdivision tt /\
                                                    v IN s} DIFF UNIONS kk)` THEN
    SUBGOAL_THEN `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} DIFF
                  UNIONS kk =
                  UNIONS (IMAGE (\m. m DIFF UNIONS kk)
                    {m | m IN barycentric_subdivision tt /\ v IN m})`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSURE_UNIONS; FINITE_IMAGE] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `(m:real^N->bool) IN barycentric_subdivision tt` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre c)` ASSUME_TAC THENL
   [SUBGOAL_THEN `closure (convex hull (IMAGE simplex_barycentre c) DIFF UNIONS kk)
                  SUBSET convex hull (IMAGE simplex_barycentre
                                       (c:(real^N->bool)->bool))` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[SUBSET_DIFF] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[moi_bar_chain];
      UNDISCH_TAC `(x:real^N) IN closure (convex hull (IMAGE simplex_barycentre c) DIFF
                                          UNIONS kk)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull (IMAGE simplex_barycentre c) SUBSET
                  UNIONS (kk:(real^N->bool)->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN closure (convex hull (IMAGE simplex_barycentre c) DIFF
                                        UNIONS kk)` THEN
    SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre c) DIFF UNIONS kk =
                  {}:real^N->bool` SUBST1_TAC THENL
     [UNDISCH_TAC `convex hull (IMAGE simplex_barycentre c) SUBSET
                   UNIONS (kk:(real^N->bool)->bool)` THEN SET_TAC[];
      REWRITE_TAC[CLOSURE_EMPTY; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_VERTEX_IN_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `c INTER (kk:(real^N->bool)->bool)`)) (rhs(concl th)))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain tt (c INTER (kk:(real^N->bool)->bool)) /\
                ~(c INTER kk = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain tt (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[FINITE_INTER; IN_INTER] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c INTER (kk:(real^N->bool)->bool)`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `c INTER (kk:(real^N->bool)->bool)`]
    MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `phi = UNIONS (c INTER (kk:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN c /\ ~(r IN kk)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `c SUBSET (kk:(real^N->bool)->bool)` THENL
     [UNDISCH_TAC `~(convex hull (IMAGE simplex_barycentre c) SUBSET
                     UNIONS (kk:(real^N->bool)->bool))` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `c INTER kk = c:(real^N->bool)->bool` ASSUME_TAC THENL
       [UNDISCH_TAC `c SUBSET (kk:(real^N->bool)->bool)` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `convex hull (IMAGE simplex_barycentre c) INTER UNIONS kk =
                   convex hull (IMAGE simplex_barycentre
                                  (c INTER kk:(real^N->bool)->bool))` THEN
      REWRITE_TAC[ASSUME `c INTER kk = c:(real^N->bool)->bool`] THEN SET_TAC[];
      UNDISCH_TAC `~(c SUBSET (kk:(real^N->bool)->bool))` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [SUBGOAL_THEN `(phi:real^N->bool) IN c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[moi_bar_chain] THEN
    DISCH_THEN(MP_TAC o SPECL [`phi:real^N->bool`; `r:real^N->bool`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN kk`
      (fun th -> UNDISCH_TAC `~((r:real^N->bool) IN kk)` THEN REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(phi:real^N->bool) IN kk /\ r IN tt /\ phi IN tt` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `simplicial_subcomplex kk (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `phi:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `phi:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r INTER phi:real^N->bool = r` (fun th -> SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `phi:real^N->bool`; `r:real^N->bool`] MOI_S4O_FR_PHI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      SUBGOAL_THEN `{v:real^N} SUBSET phi` MP_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
      MP_TAC(ASSUME `moi_bar_chain tt (c:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (c INTER kk))` THEN
  UNDISCH_TAC `convex hull (IMAGE simplex_barycentre (c INTER kk)) SUBSET
               (phi:real^N->bool)` THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Density of the outer patch along the boundary surface, rays            *)
(* from edge midpoints, Z as a polyhedron, corners against Z, and the     *)
(* splitting of Y INTER L1.                                                *)
(* ========================================================================= *)

(* Density: every point of Z on the boundary surface is a limit of points  *)
(* of Z off |kk| (move towards the midpoint of v and the barycentre of the *)
(* outer tetrahedron at a boundary triangle).                               *)

let MOI_S4O_DENSE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k x.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     x IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     x IN complex_boundary kk
     ==> x IN closure (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
                       UNIONS kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `(x:real^N) IN St` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN Z` THEN EXPAND_TAC "Z" THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> h x IN St /\ k (h x) = x /\ h (k x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN complex_boundary kk` THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_S4O_ST_MISS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN St` THEN UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `s:real^N->bool`] MOI_S4O_BTRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN St` THEN EXPAND_TAC "St" THEN
  ASM_SIMP_TAC[MOI_FTA_IN_STAR1] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `{f:real^N->bool | f face_of s}`;
                 `c:(real^N->bool)->bool`] MOI_S4O_HULL_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c0 = c INTER {f:real^N->bool | f face_of s}` THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre c0)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `convex hull (IMAGE simplex_barycentre
                                     (c0:(real^N->bool)->bool))`)) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{v:real^N} INTER s = {v}` (fun th -> SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain tt ((r:real^N->bool) INSERT c0)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain tt (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `!f:real^N->bool. f IN c0 ==> f IN c /\ f SUBSET s` ASSUME_TAC THENL
     [EXPAND_TAC "c0" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `!f:real^N->bool. f IN c0 ==> f IN c /\ f SUBSET s`) THEN
      MP_TAC(ASSUME `c SUBSET (tt:(real^N->bool)->bool)`) THEN SET_TAC[];
      EXPAND_TAC "c0" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      MP_TAC(ASSUME `!f:real^N->bool. f IN c0 ==> f IN c /\ f SUBSET s`) THEN
      MP_TAC(ASSUME `~({} IN (c:(real^N->bool)->bool))`) THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN
      MP_TAC(ASSUME `!f:real^N->bool. f IN c0 ==> f IN c /\ f SUBSET s`) THEN
      MP_TAC(ASSUME `(s:real^N->bool) SUBSET r`) THEN
      MP_TAC(ASSUME `!s t:real^N->bool. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s`) THEN
      MESON_TAC[SUBSET_REFL; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (r INSERT c0)) /\
                v IN convex hull (IMAGE simplex_barycentre (r INSERT c0)) /\
                simplex_barycentre r IN
                  convex hull (IMAGE simplex_barycentre (r INSERT c0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre c0)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> (x:real^N) IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `{v:real^N}` THEN
      ASM_REWRITE_TAC[MOI_FTA_BARY_SING; IN_INSERT];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `r:real^N->bool` THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `(r:real^N->bool) INSERT c0`]
    MOI_S4O_LEV_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->real) x = &1 / &2` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "convex" th &&
      moi_s4o_has_const "real_div" th)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real) (simplex_barycentre r) = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "skeleton" th)) THEN
    REWRITE_TAC[IN_INSERT; skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z = midpoint(v:real^N,simplex_barycentre r)` THEN
  SUBGOAL_THEN `(z:real^N) IN convex hull (IMAGE simplex_barycentre (r INSERT c0)) /\
                f z = &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[midpoint] THEN
    REWRITE_TAC[VECTOR_ARITH `inv(&2) % (v + b):real^N =
                              (&1 - &1 / &2) % v + &1 / &2 % b`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^N) IN UNIONS kk)` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[MOI_S4O_MIDPOINT_RAY] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `(r:real^N->bool) INSERT c0`; `v:real^N`;
                   `simplex_barycentre r:real^N`; `&1 / &2`] MOI_S4O_RAY_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        CONV_TAC REAL_RAT_REDUCE_CONV];
      DISCH_THEN SUBST1_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((r:real^N->bool) IN kk)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment(x:real^N,z) SUBSET Z DIFF UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SEGMENT; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(&1 - t) % x + t % z IN
                    convex hull (IMAGE simplex_barycentre ((r:real^N->bool) INSERT c0))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `(&1 - t) % x + t % z:real^N` o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "convex" th &&
        moi_s4o_has_const "real_div" th)) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `(&1 - t) % x + t % z:real^N = x + t % (z - x)`] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `(r:real^N->bool) INSERT c0`; `x:real^N`; `z:real^N`; `t:real`]
        MOI_S4O_RAY_SUB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `closure(segment(x:real^N,z))` THEN CONJ_TAC THENL
   [REWRITE_TAC[CLOSURE_SEGMENT] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `~((z:real^N) IN UNIONS kk)` THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS kk` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[ENDS_IN_SEGMENT]];
    MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Rays from b = midpoint(v,w) to K_w meet subcomplexes through b as cones. *)

let MOI_S4O_KRAY_SUB = prove
 (`!(tt:(real^N->bool)->bool) kk v w sub y t.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     simplicial_subcomplex sub tt /\ midpoint(v,w) IN UNIONS sub /\
     y IN UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                  (midpoint(v,w))) /\
     &0 < t /\ t <= &1
     ==> (midpoint(v,w) + t % (y - midpoint(v,w)) IN UNIONS sub <=> y IN UNIONS sub)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `y IN UNIONS (simplicial_link (simplicial_link
                 (barycentric_subdivision tt) v) (midpoint(v:real^N,w)))` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN o check (fun th ->
    concl th = `(t':real^N->bool) IN simplicial_link (barycentric_subdivision tt) v`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION] o check (fun th ->
    concl th = `(t':real^N->bool) IN barycentric_subdivision (tt:(real^N->bool)->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S4O_RAY_SUB THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `c:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) face_of t'` THEN
  UNDISCH_TAC `(y:real^N) IN r` THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]);;

(* Z is a polyhedron in the closed star of v. *)

let MOI_S4O_Z_POLY = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> pl_polyhedron (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) /\
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_vb; moi_s34_bd] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                   `v:real^N`] MOI_FTA_CELL_FRONTIER_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}`;
                 `h:real^N->real^N`; `k:real^N->real^N`;
                 `moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool)`]
    MOI_FTA_PLH_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_s4o_lev tt kk (v:real^N) h k` THEN
      REWRITE_TAC[moi_s4o_lev] THEN SIMP_TAC[];
      UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET
                   UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}` THEN
      SET_TAC[]];
    SIMP_TAC[]] THEN
  UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET
               UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}` THEN
  UNDISCH_TAC `!x:real^N. x IN UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}
               ==> h x IN UNIONS {s | s IN barycentric_subdivision tt /\ v IN s} /\
                   k (h x) = x /\ h (k x) = x` THEN
  SET_TAC[]);;

(* The corner at an edge meets Z only in the rim. *)

let MOI_S4O_CORNER_Z = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk
     ==> moi_s4o_corner tt kk v w INTER
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         moi_s4o_rim tt kk v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `w:real^N`] MOI_S4O_K_FINITE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4o_corner] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x':real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `x:real^N = x'` SUBST1_TAC THENL
   [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(ASSUME `(x':real^N) IN moi_s4o_rim tt kk v w`) THEN
  REWRITE_TAC[moi_s4o_rim; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y IN UNIONS (simplicial_link (simplicial_link
                  (barycentric_subdivision tt) v) (midpoint(v:real^N,w)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (simplicial_link (simplicial_link
       (barycentric_subdivision tt) v) (midpoint(v:real^N,w))) DIFF UNIONS kk`;
       `UNIONS (simplicial_link (simplicial_link
       (barycentric_subdivision tt) v) (midpoint(v:real^N,w)))`] CLOSURE_MINIMAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_DIFF] THEN
    UNDISCH_TAC `y IN closure (UNIONS (simplicial_link (simplicial_link
       (barycentric_subdivision tt) v) (midpoint(v:real^N,w))) DIFF UNIONS kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`; `y:real^N`]
    MOI_S4O_SEG_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `segment[midpoint(v,w),x'] SUBSET segment[midpoint(v:real^N,w),y]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                              segment[midpoint(v,w),y]` MP_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM SET_TAC[]];
    ASM_REWRITE_TAC[IN_SING]]);;

(* The part Y INTER L1 of the sphere lies in |kk| or in a corner at a     *)
(* boundary edge.                                                           *)

let MOI_S4O_YL_SPLIT = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> IMAGE h (moi_s34_vb tt kk v) INTER
         UNIONS (simplicial_link (barycentric_subdivision tt) v)
         SUBSET UNIONS kk UNION
                UNIONS (IMAGE (\w. moi_s4o_corner tt kk v w)
                          {w | ~(w = v) /\ segment[v,w] IN kk /\
                               segment[v,w] SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `x:real^N`] MOI_S4O_LEV_WALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`] MOI_S4O_LEV_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS {segment[midpoint(v,w),midpoint(midpoint(v,w),y)] | y |
                 y IN UNIONS (simplicial_link (simplicial_link
                        (barycentric_subdivision tt) v) (midpoint(v,w)))}`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[IN_UNION] THEN
  ASM_CASES_TAC `(y:real^N) IN UNIONS kk` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `midpoint(v:real^N,w) IN UNIONS kk` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4O_TUBE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `kk:(real^N->bool)->bool`; `y:real^N`]
      MOI_S4O_KRAY_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
    UNDISCH_TAC `(x:real^N) IN segment[b,midpoint(b,y)]` THEN
    REWRITE_TAC[MOI_S4O_MIDPOINT_RAY; MOI_FTA_SEG_RAY] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_CASES_TAC `u = &0` THENL
     [ASM_REWRITE_TAC[REAL_ARITH `&0 * &1 / &2 = &0`; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u * &1 / &2` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "real_lt" th)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `u <= &1` THEN REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN
    SUBGOAL_THEN `segment[v:real^N,w] SUBSET complex_boundary kk` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `w:real^N`] MOI_S4O_EDGE_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `~((y:real^N) IN UNIONS kk)` THEN
      UNDISCH_TAC `y IN UNIONS (simplicial_link (simplicial_link
                     (barycentric_subdivision tt) v) (midpoint(v:real^N,w)))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `moi_s4o_corner tt kk v (w:real^N)` THEN CONJ_TAC THENL
     [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s4o_corner; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `segment[midpoint(v,w),midpoint(midpoint(v:real^N,w),y)]` THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `midpoint(midpoint(v:real^N,w),y)` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s4o_rim; IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM_REWRITE_TAC[IN_DIFF]]);;

(* ========================================================================= *)
(* Witness points and the outer patch in the h-picture as a PL             *)
(* disk (MOI_S4O_SPHERE_PIECE).                                            *)
(* ========================================================================= *)

(* The midpoint of v and the barycentre of a tetrahedron at v lies on Z.  *)

let MOI_S4O_TETRA_MID = prove
 (`!(tt:(real^N->bool)->bool) kk v h k q.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     q IN tt /\ v IN q /\ aff_dim q = &3
     ==> midpoint(v,simplex_barycentre q) IN
           IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
         simplex_barycentre q IN
           UNIONS (simplicial_link (barycentric_subdivision tt) v) /\
         (!sub. simplicial_subcomplex sub tt /\ v IN UNIONS sub
                ==> (midpoint(v,simplex_barycentre q) IN UNIONS sub <=>
                     simplex_barycentre q IN UNIONS sub))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^N->bool = {}) /\ ~(q = {v})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      moi_s4o_has_const "aff_dim" th)) THEN
    REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain tt {{v:real^N},q}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; IN_SING] THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `v IN convex hull (IMAGE simplex_barycentre {{v:real^N},q}) /\
                simplex_barycentre q IN
                  convex hull (IMAGE simplex_barycentre {{v:real^N},q})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`; `{{v:real^N},q}`]
      MOI_S4O_LEV_STAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^N->real) (simplex_barycentre q) = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N->bool` o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "skeleton" th)) THEN
      REWRITE_TAC[IN_INSERT; skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `midpoint(v,simplex_barycentre q) IN
                  convex hull (IMAGE simplex_barycentre {{v:real^N},q})` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `segment[v:real^N,simplex_barycentre q]` THEN
      REWRITE_TAC[MIDPOINT_IN_SEGMENT] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `midpoint(v,simplex_barycentre q):real^N` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "convex" th &&
      moi_s4o_has_const "real_div" th)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[midpoint; VECTOR_ARITH `inv(&2) % (v + b):real^N =
                                        (&1 - &1 / &2) % v + &1 / &2 % b`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`;
                   `convex hull (IMAGE simplex_barycentre {q:real^N->bool})`]
      MOI_S4O_LINK_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [EXISTS_TAC `{q:real^N->bool}` THEN ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IN_SING];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{simplex_barycentre q:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    X_GEN_TAC `sub:(real^N->bool)->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[MOI_S4O_MIDPOINT_RAY] THEN MATCH_MP_TAC MOI_S4O_RAY_SUB THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `{{v:real^N},q}`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* Two witness points on Z at a boundary vertex: one off |kk| and off the  *)
(* link, one in |kk| off the boundary surface.                              *)

let MOI_S4O_TWO_POINTS = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     moi_s4o_lev tt kk v h k
     ==> (?z. z IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
              ~(z IN UNIONS kk) /\
              ~(z IN UNIONS (simplicial_link (barycentric_subdivision tt) v))) /\
         (?z. z IN IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
              z IN UNIONS kk /\ ~(z IN complex_boundary kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4O_BC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS kk` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN kk /\ aff_dim s = &2 /\
                                 CARD {r | r IN kk /\ aff_dim r = &3 /\ s SUBSET r} = 1 /\
                                 v IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N) IN complex_boundary kk` THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `s:real^N->bool`] MOI_S4O_BTRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`; `r:real^N->bool`]
      MOI_S4O_TETRA_MID) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `kk:(real^N->bool)->bool`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC `midpoint(v:real^N,simplex_barycentre r)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((r:real^N->bool) IN kk)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `midpoint(v:real^N,simplex_barycentre r) = simplex_barycentre r`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          moi_s4o_has_const "closed_segment" th)) THEN
        ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
        REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN DISCH_THEN SUBST_ALL_TAC THEN
        ASM_MESON_TAC[]]];
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `s:real^N->bool`] MOI_S4O_KK_PURE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({v:real^N}) = &2` THEN REWRITE_TAC[AFF_DIM_SING] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r:real^N->bool) IN tt` ASSUME_TAC THENL
     [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(r:real^N->bool) IN kk` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`; `r:real^N->bool`]
      MOI_S4O_TETRA_MID) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))) THEN
    EXISTS_TAC `midpoint(v:real^N,simplex_barycentre r)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre r IN (r:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `{r:real^N->bool}`] THEN
      ASM_SIMP_TAC[MOI_FTA_LF_BAR; MOI_FTA_CHAIN_SING; IN_SING];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "eq" (MP_TAC o SPEC `kk:(real^N->bool)->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "eq" (MP_TAC o SPEC `boundary_complex kk:(real^N->bool)->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) IN boundary_complex kk` MP_TAC THENL
       [MATCH_MP_TAC MOI_FTA_BARY_IN_SUBCOMPLEX THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
        ALL_TAC] THEN
      REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `r:real^N->bool`] MOI_S4O_IN_BOUNDARY) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `s':real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* The rims lie in the closure of Z off |kk|. *)

let MOI_S4O_RIM_PH = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk
     ==> moi_s4o_rim tt kk v w SUBSET
         closure (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4o_rim; GSYM MOI_S4O_CLOSURE_MIDPOINT] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`; `y:real^N`]
    MOI_S4O_SEG_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ASSUME `IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                   INTER segment[midpoint(v,w),y] = {midpoint(midpoint(v,w),y)}`) THEN
    SET_TAC[];
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `w:real^N`; `kk:(real^N->bool)->bool`; `y:real^N`] MOI_S4O_HOM_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* The outer patch in the h-picture is a PL disk with the stated boundary  *)
(* (a piece of the sphere Z UNION (Y INTER L1) cut out by the circle Jh).  *)

let MOI_S4O_PH_DISK = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk /\
     moi_s4o_lev tt kk v h k
     ==> pl_cell_with_boundary 2
           (closure (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk))
           ((IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
             complex_boundary kk) UNION
            UNIONS (IMAGE (\w. moi_s4o_rim tt kk v w)
                      {w | ~(w = v) /\ segment[v,w] IN kk /\
                           segment[v,w] SUBSET complex_boundary kk}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_SH_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_JH_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_Z_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_YL_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_TWO_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_BEDGES_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_STAR_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!w. w IN {w | ~(w = v) /\ segment[v,w] IN kk /\
                  segment[v,w] SUBSET complex_boundary kk}
        ==> moi_s4o_corner tt kk v w SUBSET
              IMAGE h (moi_s34_vb tt kk v) INTER moi_s4o_stb tt v w /\
            closed (moi_s4o_corner tt kk v w) /\
            moi_s4o_rim tt kk v w SUBSET moi_s4o_corner tt kk v w /\
            moi_s4o_corner tt kk v w INTER
              IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
              moi_s4o_rim tt kk v w /\
            moi_s4o_rim tt kk v w SUBSET
              closure (IMAGE (h:real^N->real^N)
                         (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)`
  (LABEL_TAC "cor") THENL
   [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`] MOI_S4O_CORNER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
      MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC [`2`; `moi_s4o_rim tt kk v w UNION
                                  segment[midpoint(v,w),p] UNION
                                  segment[midpoint(v:real^N,w),q]`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[moi_s4o_corner; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `segment[midpoint(v:real^N,w),x]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4O_CORNER_Z THEN EXISTS_TAC `k:real^N->real^N` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4O_RIM_PH THEN EXISTS_TAC `k:real^N->real^N` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision tt:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_LINK_IN_STAR) THEN DISCH_TAC THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision tt) (v:real^N))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `ix = {w | ~(w = v) /\ segment[v,w] IN kk /\
                        segment[v:real^N,w] SUBSET complex_boundary kk}` THEN
  ABBREV_TAC `Ph = closure ((Z:real^N->bool) DIFF UNIONS kk)` THEN
  SUBGOAL_THEN `(Ph:real^N->bool) SUBSET Z` ASSUME_TAC THENL
   [EXPAND_TAC "Ph" THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ph:real^N->bool) SUBSET closure (St DIFF UNIONS kk)` ASSUME_TAC THENL
   [EXPAND_TAC "Ph" THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    UNDISCH_TAC `(Z:real^N->bool) SUBSET St` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. moi_s4o_stb tt v w SUBSET L` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s4o_stb] THEN EXPAND_TAC "L" THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN
  EXISTS_TAC `(Z:real^N->bool) UNION (Y INTER L)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                    `h:real^N->real^N`; `k:real^N->real^N`; `x:real^N`] MOI_S4O_DENSE) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_TAC THEN USE_THEN "cor" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    UNDISCH_TAC `(Ph:real^N->bool) SUBSET Z` THEN SET_TAC[];
    EXPAND_TAC "Ph" THEN REWRITE_TAC[CLOSED_CLOSURE];
    MATCH_MP_TAC(SET_RULE `!G. s SUBSET G /\ G INTER p SUBSET (j:real^N->bool)
                               ==> s INTER p SUBSET j`) THEN
    EXISTS_TAC `((Z:real^N->bool) UNION (Y INTER L)) INTER (St INTER UNIONS kk) UNION
                UNIONS (IMAGE (\w. moi_s4o_corner tt kk v w) ix)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        ASM_CASES_TAC `(x:real^N) IN UNIONS kk` THENL
         [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(x:real^N) IN Z \/ x IN Y /\ x IN L` THEN
          UNDISCH_TAC `(Z:real^N->bool) SUBSET St` THEN
          UNDISCH_TAC `(L:real^N->bool) SUBSET St` THEN SET_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
         [UNDISCH_TAC `~((x:real^N) IN Ph)` THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
          EXPAND_TAC "Ph" THEN
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
          ASM_REWRITE_TAC[IN_DIFF];
          DISJ2_TAC THEN
          UNDISCH_TAC `(Y:real^N->bool) INTER L SUBSET
                       UNIONS kk UNION UNIONS (IMAGE (\w. moi_s4o_corner tt kk v w) ix)` THEN
          UNDISCH_TAC `~((x:real^N) IN UNIONS kk)` THEN
          UNDISCH_TAC `(x:real^N) IN Y /\ x IN L` THEN SET_TAC[]];
        MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
          MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `2` THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
          X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
          USE_THEN "cor" (MP_TAC o SPEC `w:real^N`) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]]];
      REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      REWRITE_TAC[IN_UNION] THEN
      ASM_CASES_TAC `(x:real^N) IN UNIONS kk` THENL
       [DISJ1_TAC THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(x:real^N) IN Ph` THEN UNDISCH_TAC `(Ph:real^N->bool) SUBSET Z` THEN
          SET_TAC[];
          MATCH_MP_TAC MOI_S4O_FR THEN
          MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `v:real^N`] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(x:real^N) IN Ph` THEN
          UNDISCH_TAC `(Ph:real^N->bool) SUBSET closure (St DIFF UNIONS kk)` THEN
          SET_TAC[]];
        DISJ2_TAC THEN
        SUBGOAL_THEN `(x:real^N) IN UNIONS (IMAGE (\w. moi_s4o_corner tt kk v w) ix)`
        MP_TAC THENL
         [UNDISCH_TAC `(x:real^N) IN (Z UNION Y INTER L) INTER (St INTER UNIONS kk) UNION
                       UNIONS (IMAGE (\w. moi_s4o_corner tt kk v w) ix)` THEN
          UNDISCH_TAC `~((x:real^N) IN UNIONS kk)` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
        EXISTS_TAC `moi_s4o_rim tt kk v (w:real^N)` THEN
        CONJ_TAC THENL [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "cor" (MP_TAC o SPEC `w:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s4o_corner tt kk v w INTER Z SUBSET moi_s4o_rim tt kk v (w:real^N)` THEN
        UNDISCH_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:real^N) IN Ph` THEN UNDISCH_TAC `(Ph:real^N->bool) SUBSET Z` THEN
        SET_TAC[]]];
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `z1:real^N` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Ph" THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      REWRITE_TAC[IN_UNION; IN_INTER; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~((z1:real^N) IN UNIONS kk)` THEN
        REWRITE_TAC[] THEN
        MP_TAC(ISPEC `kk:(real^N->bool)->bool` MOI_FMB_CB_SUBSET) THEN
        UNDISCH_TAC `(z1:real^N) IN complex_boundary kk` THEN SET_TAC[];
        REWRITE_TAC[IN_UNIONS; IN_IMAGE; NOT_EXISTS_THM] THEN
        X_GEN_TAC `t:real^N->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)
          ASSUME_TAC) THEN
        USE_THEN "cor" (MP_TAC o SPEC `w:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `~((z1:real^N) IN L)` THEN REWRITE_TAC[] THEN
        MP_TAC(SPEC `w:real^N` (ASSUME `!w:real^N. moi_s4o_stb tt v w SUBSET L`)) THEN
        UNDISCH_TAC `moi_s4o_rim tt kk v w SUBSET moi_s4o_corner tt kk v (w:real^N)` THEN
        UNDISCH_TAC `moi_s4o_corner tt kk v w SUBSET
                     (Y:real^N->bool) INTER moi_s4o_stb tt v w` THEN
        UNDISCH_TAC `(z1:real^N) IN t` THEN
        REWRITE_TAC[ASSUME `t = moi_s4o_rim tt kk v (w:real^N)`] THEN SET_TAC[]]];
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `z2:real^N` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((z2:real^N) IN complex_boundary kk)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4O_FR THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z2:real^N) IN Ph` THEN
    UNDISCH_TAC `(Ph:real^N->bool) SUBSET closure (St DIFF UNIONS kk)` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Transfer back by k (clause 7) and the main theorems                       *)
(* OUTER_CELLS, SCELL_A.                                                     *)
(* ========================================================================= *)

(* The h-image of the outer rim of the splitting disk of an edge [v,w]. *)

let MOI_S4O_RIM_IMAGE = prove
 (`!(tt:(real^N->bool)->bool) kk v h k w.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k /\
     ~(w = v) /\ segment[v,w] IN kk
     ==> IMAGE h (closure (((moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                            moi_s34_bd tt kk) DIFF UNIONS kk)) =
         moi_s4o_rim tt kk v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`] MOI_S4O_LEV_DISK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4o_rim] THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  ABBREV_TAC `b = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `K = UNIONS (simplicial_link (simplicial_link (barycentric_subdivision tt) v)
                                          (b:real^N))` THEN
  ABBREV_TAC `R = (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                  moi_s34_bd tt (kk:(real^N->bool)->bool)` THEN
  ABBREV_TAC `hom = \y:real^N. midpoint(b,y)` THEN
  SUBGOAL_THEN `(R:real^N->bool) DIFF UNIONS kk SUBSET St` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                 `h:real^N->real^N`; `k:real^N->real^N`;
                 `kk:(real^N->bool)->bool`; `R:real^N->bool`] MOI_S4O_LEV_PRES_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(R:real^N->bool) DIFF UNIONS kk SUBSET St` THEN
    EXPAND_TAC "R" THEN UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (hom:real^N->real^N) K DIFF UNIONS kk =
                IMAGE hom (K DIFF UNIONS kk)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(b:real^N) IN UNIONS kk` ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(ASSUME `midpoint(v:real^N,w) = b`); MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y:real^N. y IN K ==> (hom y IN UNIONS kk <=> y IN UNIONS kk)`
    MP_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `v:real^N`; `w:real^N`; `kk:(real^N->bool)->bool`;
                     `y:real^N`] MOI_S4O_HOM_SUB) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)];
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `(\y:real^N. midpoint (b,y)) = hom`)] THEN
  REWRITE_TAC[MOI_S4O_CLOSURE_MIDPOINT]);;

(* The boundary edges at v, indexed by their far vertex. *)

let MOI_S4O_BEDGE_PARAM = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> {g | g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET complex_boundary kk} =
         IMAGE (\w. segment[v,w])
           {w | ~(w = v) /\ segment[v,w] IN kk /\ segment[v,w] SUBSET complex_boundary kk}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `g:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                  `g:real^N->bool`] MOI_S4O_EDGE_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `v:real^N = a \/ v = b` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM EXTREME_POINT_OF_SEGMENT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `g:real^N->bool`)) THEN
      MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
      UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
      UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> is_disj(concl th)))
    THENL
     [EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* Pulling a PL cell back through a PL self-homeomorphism of a set. *)

let MOI_S4O_CELL_PULLBACK = prove
 (`!(St:real^N->bool) h k n C D.
     pl_homeomorphism (St,St) (h,k) /\ C SUBSET St /\ D SUBSET St /\
     pl_cell_with_boundary n (IMAGE h C) (IMAGE h D)
     ==> pl_cell_with_boundary n C D`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) (IMAGE h C) = C /\ IMAGE k (IMAGE h D) = D /\
                IMAGE h C SUBSET St`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(C:real^N->bool) SUBSET St` THEN UNDISCH_TAC `(D:real^N->bool) SUBSET St` THEN
    UNDISCH_TAC `!x:real^N. x IN St ==> (k:real^N->real^N) (h x) = x` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^N) St = St` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`St:real^N->bool`; `St:real^N->bool`; `k:real^N->real^N`;
                 `h:real^N->real^N`; `IMAGE (h:real^N->real^N) C`] MOI_FMB_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `IMAGE (h:real^N->real^N) D`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `IMAGE (h:real^N->real^N) C`; `IMAGE (h:real^N->real^N) D`;
                 `k:real^N->real^N`; `h:real^N->real^N`] MOI_FTA_CELL_PLH) THEN
  ASM_REWRITE_TAC[]);;

(* A comprehension over a predicate as an image. *)

let MOI_S4O_GSPEC_IMAGE = prove
 (`!(f:A->B) P. {f x | x | P x} = IMAGE f {x | P x}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The h-image of the triangle part of the stated boundary. *)

let MOI_S4O_IMAGE_A = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> IMAGE h (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                          s IN moi_s34_simp kk (&2) /\ v IN s /\
                          s SUBSET complex_boundary kk}) =
         IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER complex_boundary kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_Z_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_S4A_IMAGE_UNIONS_GSPEC] THEN
  SUBGOAL_THEN
   `{IMAGE (h:real^N->real^N) (s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) | s |
     s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk} =
    {IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER s | s |
     s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET complex_boundary kk}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S4A_GSPEC_EQ THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
     [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
      UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_FACES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                   `h:real^N->real^N`; `k:real^N->real^N`;
                   `{f:real^N->bool | f face_of s}`;
                   `moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      MOI_S4O_LEV_PRES_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET
                   UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS {f:real^N->bool | f face_of s} = s`] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z = IMAGE (h:real^N->real^N) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET complex_boundary kk` THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN complex_boundary kk` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [complex_boundary] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(Z:real^N->bool) INTER s` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN EXISTS_TAC `s:real^N->bool` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_S4O_ST_MISS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
        UNDISCH_TAC `(s:real^N->bool) IN kk` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(x:real^N) IN Z` THEN UNDISCH_TAC `(x:real^N) IN s` THEN
      UNDISCH_TAC `(Z:real^N->bool) SUBSET
                   UNIONS {s | s IN barycentric_subdivision tt /\ v IN s}` THEN
      SET_TAC[];
      MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4O_TRI_BOUNDARY) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET]]]);;

(* The h-image of the rim part of the stated boundary. *)

let MOI_S4O_IMAGE_B = prove
 (`!(tt:(real^N->bool)->bool) kk v h k.
     moi_s34_tube tt kk /\ {v} IN kk /\ moi_s4o_lev tt kk v h k
     ==> IMAGE h (UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                   UNIONS kk) | g |
                          g IN moi_s34_simp kk (&1) /\ v IN g /\
                          g SUBSET complex_boundary kk}) =
         UNIONS (IMAGE (\w. moi_s4o_rim tt kk v w)
                   {w | ~(w = v) /\ segment[v,w] IN kk /\
                        segment[v,w] SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_S4A_IMAGE_UNIONS_GSPEC] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_BEDGE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w. ~(w = v) /\ segment[v,w] IN kk /\ segment[v,w] SUBSET complex_boundary kk
        ==> IMAGE (h:real^N->real^N)
              (closure ((moi_s34_sd tt kk (segment[v,w]) INTER moi_s34_bd tt kk) DIFF
                        UNIONS kk)) = moi_s4o_rim tt kk v w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_s34_sd tt kk (segment[v:real^N,w]) =
                  moi_s34_vb tt kk v INTER moi_s34_vb tt kk w` SUBST1_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC MOI_S4A_SD_EDGE THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4O_RIM_IMAGE THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "moi_s34_simp" th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && moi_s4o_has_const "moi_s4o_rim" th)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s34_simp" th)) THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && moi_s4o_has_const "moi_s4o_rim" th)) THEN
      ASM_REWRITE_TAC[]]]);;

(* Clause 7 of moi_s4a_outer: the outer patch at a boundary vertex of kk   *)
(* is a PL 2-cell with the stated boundary.                                 *)

let MOI_S4O_CLAUSE7 = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk /\ v IN complex_boundary kk
     ==> pl_cell_with_boundary 2
           (closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk))
           (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                    s IN moi_s34_simp kk (&2) /\ v IN s /\
                    s SUBSET complex_boundary kk} UNION
            UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                             UNIONS kk) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g /\
                    g SUBSET complex_boundary kk})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
    MOI_S4O_LEV_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_LEV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4O_CELL_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}`;
    `h:real^N->real^N`; `k:real^N->real^N`] THEN
  ABBREV_TAC `St = UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `closed (St:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ASSUME `moi_s4o_lev tt kk (v:real^N) h k`) THEN
    REWRITE_TAC[moi_s4o_lev] THEN
    REWRITE_TAC[ASSUME `UNIONS {s | s IN barycentric_subdivision tt /\ (v:real^N) IN s} =
                        St`] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[];
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THENL
     [UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_s34_sd tt kk s SUBSET moi_s34_vb tt kk (v:real^N)` MP_TAC THENL
       [REWRITE_TAC[moi_s34_sd] THEN MATCH_MP_TAC(SET_RULE
         `(t:real^N->bool) IN u ==> INTERS u SUBSET t`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[]]];
    REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_IMAGE_A) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                  `h:real^N->real^N`; `k:real^N->real^N`] MOI_S4O_IMAGE_B) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `IMAGE (h:real^N->real^N)
        (closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)) =
      closure (IMAGE h (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `(moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk SUBSET
                    (St:real^N->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`;
                     `h:real^N->real^N`; `k:real^N->real^N`;
                     `kk:(real^N->bool)->bool`;
                     `moi_s34_vb tt kk v INTER moi_s34_bd tt (kk:(real^N->bool)->bool)`]
        MOI_S4O_LEV_PRES_SUB) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET St` THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4O_PH_DISK THEN EXISTS_TAC `k:real^N->real^N` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Targets.                                                                  *)
(* ------------------------------------------------------------------------- *)

let OUTER_CELLS = prove
 (`!(tt:(real^N->bool)->bool) kk. moi_s34_tube tt kk ==> moi_s4a_outer tt kk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4a_outer] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CLAUSE7 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4O_CLAUSE8 THEN ASM_REWRITE_TAC[]]);;

let SCELL_A = prove
 (MOI_S34_SCELL_A,
  MATCH_MP_TAC MOI_S4A_SCELL_A_FROM_OUTER THEN ACCEPT_TAC OUTER_CELLS);;


