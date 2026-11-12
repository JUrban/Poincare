(* ========================================================================= *)
(* pc_moi_s34_op1a: Moise Sec 34, Operation 1 with the compressing disk    *)
(* inside the face ball (p.241, Lemma 6).                                   *)
(* Theorem OP1_IN : |- MOI_S34_OP1_IN (pc_moi_s34_stmt.ml).  Route: the     *)
(* disk d splits the ball cb s (MOI_S5N_SPLIT_BALL); the half containing   *)
(* h(Bd s) is pushed off d by a homothety of a pair simplex (ball, facet)  *)
(* (MOI_S4N_COMPRESS); near d the tube boundary meets the old ball only in *)
(* d (MOI_S4N_KEY, from the crossing charts), so the new trace is the old  *)
(* trace minus its component j on one side of d, and the rank drops.  The  *)
(* H_1 clause of the face-ball invariant (MOI_S4N_H1_KEEP_THM) uses         *)
(* the torus unit pc_moi_s34_torus (T1 and SEP on the boundary torus of    *)
(* the face torus).                                                         *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_s35_finb1.ml";;
needs "src/pc_moi_s35_charts.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_s34_torus.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* General PL facts for the compression: restriction of a PL                *)
(* homeomorphism, images of cells, 3-simplices in real^3, PL balls as       *)
(* images of 3-simplices, homotheties of a simplex about a vertex, and a    *)
(* pair homeomorphism (ball, frontier disk) to (simplex, facet).           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_PLH_RESTRICT = prove
 (`!(f:real^M->real^N) g s t u.
     pl_homeomorphism (s,t) (f,g) /\ u SUBSET s /\
     locally_polyhedral u /\ locally_polyhedral (IMAGE f u)
     ==> pl_homeomorphism (u,IMAGE f u) (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) u SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (s,t) (f:real^M->real^N,g)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^M->real^N) s = t` THEN
    UNDISCH_TAC `(u:real^M->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4N_CELL_IMAGE = prove
 (`!n (f:real^N->real^N) g s t d j.
     pl_homeomorphism (s,t) (f,g) /\ d SUBSET s /\ pl_cell_with_boundary n d j
     ==> pl_cell_with_boundary n (IMAGE f d) (IMAGE f j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5H_CELL_POLY]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on d (f:real^N->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    UNDISCH_TAC `pl_homeomorphism (s,t) (f:real^N->real^N,g)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTA_CELL_PLH THEN EXISTS_TAC `g:real^N->real^N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4N_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; PL_POLYHEDRON_PL_IMAGE]);;

let MOI_S4N_SIMPLEX3_FACTS = prove
 (`!k:real^3->bool.
     &3 simplex k
     ==> compact k /\ convex k /\ ~(interior k = {}) /\
         relative_interior k = interior k /\
         relative_frontier k = frontier k /\
         frontier k = k DIFF interior k /\ interior k SUBSET k`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `polytope (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (k:real^3->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (k:real^3->bool) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `&3 simplex (k:real^3->bool)` THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:real^3->bool) HAS_SIZE (dimindex(:3) + 1)` ASSUME_TAC THENL
     [REWRITE_TAC[HAS_SIZE; DIMINDEX_3] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
      UNDISCH_TAC `&(CARD (c:real^3->bool)):int = &3 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_EQ_EMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR; RELATIVE_FRONTIER_NONEMPTY_INTERIOR;
               INTERIOR_SUBSET] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]);;

let MOI_S4N_BALL_INTERIOR = prove
 (`!k c (p:real^3->real^3) q.
     &3 simplex k /\ pl_homeomorphism (k,c) (p,q)
     ==> compact c /\ frontier c = IMAGE p (relative_frontier k) /\
         interior c = IMAGE p (interior k) /\ frontier c SUBSET c /\
         interior c = c DIFF frontier c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4N_SIMPLEX3_FACTS) THEN
  SUBGOAL_THEN `homeomorphism (k,c) (p:real^3->real^3,q)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,c) (p:real^3->real^3,q)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (c:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (p:real^3->real^3) k = c`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (c:real^3->bool) SUBSET c /\ interior c = c DIFF frontier c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (c:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSURE_CLOSED th]) THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier c = IMAGE (p:real^3->real^3) (relative_frontier k)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `q:real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior c = IMAGE (p:real^3->real^3) (interior k)` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior c = IMAGE (p:real^3->real^3) k DIFF IMAGE p (k DIFF interior k)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `interior (c:real^3->bool) = c DIFF frontier c` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `frontier c = IMAGE (p:real^3->real^3) (relative_frontier k)` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `relative_frontier (k:real^3->bool) = frontier k` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `frontier (k:real^3->bool) = k DIFF interior k` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `IMAGE (p:real^3->real^3) k = c` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`!x. x IN k ==> (q:real^3->real^3) (p x) = x`;
                           `interior (k:real^3->bool) SUBSET k`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The homothety of ratio lam about the vertex p of the simplex with vertex *)
(* set p INSERT vf: it maps the simplex into itself and off the opposite    *)
(* facet, the points it misses lie near that facet, and it maps interior    *)
(* to interior.                                                             *)

let MOI_S4N_HOMOTHETY = prove
 (`!p (vf:real^3->bool) lam.
     ~affine_dependent (p INSERT vf) /\ ~(p IN vf) /\ ~(vf = {}) /\
     &0 < lam /\ lam < &1
     ==> IMAGE (\y. lam % y + (&1 - lam) % p) (convex hull (p INSERT vf)) SUBSET
         convex hull (p INSERT vf) /\
         IMAGE (\y. lam % y + (&1 - lam) % p) (convex hull (p INSERT vf)) INTER
         convex hull vf = {} /\
         (!y. y IN convex hull (p INSERT vf) /\
              ~(y IN IMAGE (\y. lam % y + (&1 - lam) % p) (convex hull (p INSERT vf)))
              ==> ?x. x IN convex hull vf /\ norm(y - x) <= (&1 - lam) * norm(p - x)) /\
         interior(IMAGE (\y. lam % y + (&1 - lam) % p) (convex hull (p INSERT vf))) =
         IMAGE (\y. lam % y + (&1 - lam) % p) (interior(convex hull (p INSERT vf)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN convex hull (p INSERT vf)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^3) IN convex hull vf)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~affine_dependent ((p:real^3) INSERT vf)` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `p:real^3` THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `((p:real^3) INSERT vf) DELETE p = vf` SUBST1_TAC THENL
     [UNDISCH_TAC `~((p:real^3) IN vf)` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `vf:real^3->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    UNDISCH_TAC `(p:real^3) IN convex hull vf` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (vf:real^3->bool) face_of convex hull (p INSERT vf)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `vf:real^3->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* into the simplex *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPEC `(p:real^3) INSERT vf` CONVEX_CONVEX_HULL) THEN
    REWRITE_TAC[convex] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lam < &1` THEN UNDISCH_TAC `&0 < lam` THEN
    REAL_ARITH_TAC;
    (* off the facet *)
    REWRITE_TAC[SET_RULE `(s:real^3->bool) INTER t = {} <=> !x. x IN s ==> ~(x IN t)`;
                FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = p` THENL
     [UNDISCH_TAC `lam % y + (&1 - lam) % p IN convex hull (vf:real^3->bool)` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `lam % p + (&1 - lam) % p:real^3 = p`];
      ALL_TAC] THEN
    SUBGOAL_THEN `lam % y + (&1 - lam) % p IN segment(p:real^3,y)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(y:real^3 = p)` THEN MESON_TAC[];
        EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `~((p:real^3) IN convex hull vf)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull (vf:real^3->bool) face_of convex hull (p INSERT vf)` THEN
    REWRITE_TAC[face_of] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^3`; `y:real^3`;
                               `lam % y + (&1 - lam) % p:real^3`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    (* the points missed are near the facet *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN convex hull (p INSERT vf)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_INSERT_ALT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `lam < u` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(u <= lam) ==> lam < u`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN IMAGE (\y. lam % y + (&1 - lam) % p)
                                     (convex hull (p INSERT vf)))` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(&1 - u / lam) % p + (u / lam) % x:real^3` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `lam * u / lam = u` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        SUBGOAL_THEN `lam * (&1 - u / lam) = lam - u` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        VECTOR_ARITH_TAC;
        ASM_REWRITE_TAC[CONVEX_HULL_INSERT_ALT; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`u / lam`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
        UNDISCH_TAC `u <= lam` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `x:real^3` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `y - x:real^3 = (&1 - u) % (p - x)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(&1 - u) = &1 - u` SUBST1_TAC THENL
     [UNDISCH_TAC `u <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    UNDISCH_TAC `lam < u` THEN REAL_ARITH_TAC;
    (* interior *)
    SUBGOAL_THEN `!s. IMAGE (\y. lam % y + (&1 - lam) % (p:real^3)) s =
                      IMAGE (\y:real^3. (&1 - lam) % p + y) (IMAGE (\y. lam % y) s)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN BETA_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INTERIOR_TRANSLATION] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
    REWRITE_TAC[LINEAR_SCALING] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(lam = &0)` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LCANCEL]) THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC]);;

(* A PL 3-ball x with a PL disk d in its frontier is PL homeomorphic to a  *)
(* 3-simplex with d going to a facet (DISK in sphere: MOI_SPU_SPHERE_DISK_PLH *)
(* moves d onto a facet; the Alexander extension MOI_SCD_COR_EXTEND_BALL).  *)

let MOI_S4N_PAIR_SIMPLEX = prove
 (`!x d j:real^3->bool.
     pl_ball 3 x /\ pl_cell_with_boundary 2 d j /\ d SUBSET frontier x
     ==> ?p vf (gg:real^3->real^3) ff.
           ~affine_dependent (p INSERT vf) /\ vf HAS_SIZE 3 /\ ~(p IN vf) /\
           pl_homeomorphism (convex hull (p INSERT vf),x) (gg,ff) /\
           IMAGE gg (convex hull vf) = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_ball 3 (x:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `g0:real^3->real^3`
    (X_CHOOSE_THEN `f0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `x:real^3->bool`; `g0:real^3->real^3`;
                 `f0:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4N_SIMPLEX3_FACTS) THEN
  SUBGOAL_THEN `homeomorphism (k,x) (g0:real^3->real^3,f0)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,x) (g0:real^3->real^3,f0)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET x` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^3->bool) SUBSET frontier x` THEN
    UNDISCH_TAC `frontier (x:real^3->bool) SUBSET x` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the disk moved into the simplex boundary *)
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f0:real^3->real^3) d) (IMAGE f0 j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_CELL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3`; `x:real^3->bool`; `k:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f0:real^3->real^3) d SUBSET relative_frontier k` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(d:real^3->bool) SUBSET frontier x`;
      `frontier x = IMAGE (g0:real^3->real^3) (relative_frontier k)`;
      `relative_frontier (k:real^3->bool) = frontier k`;
      `frontier (k:real^3->bool) = k DIFF interior k`;
      `!x. x IN k ==> (f0:real^3->real^3) (g0 x) = x`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the vertices and a facet *)
  MP_TAC(ASSUME `&3 simplex (k:real^3->bool)`) THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  SUBGOAL_THEN `FINITE (c:real^3->bool) /\ CARD c = 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    UNDISCH_TAC `&(CARD (c:real^3->bool)):int = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p:real^3. p IN c` (X_CHOOSE_TAC `p:real^3`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (c:real^3->bool) = 4` THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `vf = (c:real^3->bool) DELETE p` THEN
  SUBGOAL_THEN `(p:real^3) INSERT vf = c /\ ~(p IN vf) /\ vf HAS_SIZE 3 /\
                vf SUBSET c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vf" THEN REWRITE_TAC[IN_DELETE; HAS_SIZE] THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; INSERT_DELETE; DELETE_SUBSET] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (vf:real^3->bool) face_of k /\
                aff_dim (convex hull vf) = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `convex hull (c:real^3->bool) = k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `vf:real^3->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      SUBGOAL_THEN `~affine_dependent (vf:real^3->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `c:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
      UNDISCH_TAC `(vf:real^3->bool) HAS_SIZE 3` THEN SIMP_TAC[HAS_SIZE] THEN
      DISCH_THEN(K ALL_TAC) THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  (* move the disk onto the facet in the boundary sphere *)
  MP_TAC(ISPECL [`k:real^3->bool`; `IMAGE (f0:real^3->real^3) d`;
                 `IMAGE (f0:real^3->real^3) j`; `convex hull (vf:real^3->bool)`]
    MOI_SPU_SPHERE_DISK_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^3->real^3` (X_CHOOSE_THEN `ps:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* extend to the simplex *)
  MP_TAC(ISPECL [`k:real^3->bool`; `k:real^3->bool`; `ph:real^3->real^3`;
                 `ps:real^3->real^3`] MOI_SCD_COR_EXTEND_BALL) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `pl_ball 3 (k:real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC PL_BALL_SIMPLEX THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `relative_frontier (k:real^3->bool) = frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Psi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (k,k) (Phi:real^3->real^3,Psi)` MP_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,k) (Phi:real^3->real^3,Psi)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) (IMAGE (f0:real^3->real^3) d) = convex hull vf` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (ph:real^3->real^3) (IMAGE (f0:real^3->real^3) d) = convex hull vf`;
      `!x. x IN frontier k ==> (Phi:real^3->real^3) x = ph x`;
      `IMAGE (f0:real^3->real^3) d SUBSET relative_frontier k`;
      `relative_frontier (k:real^3->bool) = frontier k`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Psi:real^3->real^3) (convex hull vf) = IMAGE (f0:real^3->real^3) d` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (Phi:real^3->real^3) (IMAGE (f0:real^3->real^3) d) = convex hull vf`;
      `!x. x IN k ==> (Psi:real^3->real^3) (Phi x) = x`;
      `IMAGE (f0:real^3->real^3) d SUBSET relative_frontier k`;
      `relative_frontier (k:real^3->bool) = frontier k`;
      `frontier (k:real^3->bool) = k DIFF interior k`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g0:real^3->real^3) (IMAGE (f0:real^3->real^3) d) = d` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`!y. y IN x ==> (g0:real^3->real^3) (f0 y) = y`;
      `(d:real^3->bool) SUBSET x`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `vf:real^3->bool`;
                        `(g0:real^3->real^3) o (Psi:real^3->real^3)`;
                        `(Phi:real^3->real^3) o (f0:real^3->real^3)`] THEN
  SUBGOAL_THEN `convex hull ((p:real^3) INSERT vf) = k` SUBST1_TAC THENL
   [UNDISCH_TAC `convex hull (c:real^3->bool) = k` THEN
    UNDISCH_TAC `(p:real^3) INSERT vf = c` THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

(* ------------------------------------------------------------------------- *)
(* The compression of a PL 3-ball along a proper PL disk d: the half        *)
(* containing a compact connected K, pushed off d by a homothety of a pair  *)
(* simplex (MOI_S4N_PAIR_SIMPLEX); the new frontier agrees with the old one *)
(* outside a compact Z inside a given open W around d.                      *)
(* ------------------------------------------------------------------------- *)

(* Frontier bookkeeping for the image c' of a smaller simplex kl in k under *)
(* a homeomorphism gg of k onto x1: outside the image of the closed set nb  *)
(* (which contains k DIFF kl), the frontier of c' is the part s1 of the     *)
(* frontier of x1 off the image d of the facet f.                          *)

let MOI_S4N_SLAB_FRONTIER = prove
 (`!(k:real^3->bool) kl nb f (gg:real^3->real^3) ff x1 c' s1 d j.
     kl SUBSET k /\ kl INTER f = {} /\ f SUBSET k /\ closed nb /\
     k DIFF kl SUBSET nb /\
     (!x. x IN k ==> ff (gg x) = x) /\ IMAGE gg k = x1 /\
     IMAGE gg kl = c' /\ IMAGE gg f = d /\
     frontier k = k DIFF interior k /\ frontier kl = kl DIFF interior kl /\
     frontier x1 = IMAGE gg (frontier k) /\ frontier c' = IMAGE gg (frontier kl) /\
     frontier x1 = s1 UNION d /\ s1 INTER d = j
     ==> frontier c' SUBSET
         (s1 DIFF j) UNION (IMAGE gg (k INTER nb) INTER (x1 DIFF d)) /\
         frontier c' DIFF IMAGE gg (k INTER nb) = s1 DIFF IMAGE gg (k INTER nb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q:real^3. q IN frontier kl /\ ~(q IN nb) ==> q IN frontier k`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^3` THEN
    REWRITE_TAC[ASSUME `frontier (k:real^3->bool) = k DIFF interior k`;
                ASSUME `frontier (kl:real^3->bool) = kl DIFF interior kl`; IN_DIFF] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(q:real^3) IN kl` THEN UNDISCH_TAC `(kl:real^3->bool) SUBSET k` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((q:real^3) IN interior kl)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^3) IN interior k` THEN REWRITE_TAC[IN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `(:real^3) DIFF nb` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[GSYM closed; ASSUME `closed (nb:real^3->bool)`] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; ASSUME `~((q:real^3) IN nb)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r1 r2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < r1` THEN UNDISCH_TAC `&0 < r2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball(q:real^3,min r1 r2) SUBSET ball(q,r1) /\
                  ball(q:real^3,min r1 r2) SUBSET ball(q,r2)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`ball(q:real^3,r1) SUBSET k`;
                           `ball(q:real^3,r2) SUBSET (:real^3) DIFF nb`;
                           `k DIFF kl SUBSET (nb:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN frontier k /\ ~(q IN nb) ==> q IN frontier kl`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kl:real^3->bool`; `k:real^3->bool`] SUBSET_INTERIOR) THEN
    REWRITE_TAC[ASSUME `(kl:real^3->bool) SUBSET k`] THEN
    MAP_EVERY UNDISCH_TAC [`(q:real^3) IN frontier k`; `~((q:real^3) IN nb)`;
                           `k DIFF kl SUBSET (nb:real^3->bool)`;
                           `frontier (k:real^3->bool) = k DIFF interior k`;
                           `frontier (kl:real^3->bool) = kl DIFF interior kl`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. q IN kl ==> ~((gg:real^3->real^3) q IN d)` ASSUME_TAC THENL
   [X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(q:real^3) IN kl`; `IMAGE (gg:real^3->real^3) f = d`;
                           `(kl:real^3->bool) SUBSET k`; `(f:real^3->bool) SUBSET k`;
                           `kl INTER (f:real^3->bool) = {}`;
                           `!x. x IN k ==> (ff:real^3->real^3) (gg x) = x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier c' = IMAGE (gg:real^3->real^3) (frontier kl)`;
      `frontier x1 = IMAGE (gg:real^3->real^3) (frontier k)`;
      `frontier x1 = (s1:real^3->bool) UNION d`; `(s1:real^3->bool) INTER d = j`;
      `!q:real^3. q IN frontier kl /\ ~(q IN nb) ==> q IN frontier k`;
      `!q:real^3. q IN kl ==> ~((gg:real^3->real^3) q IN d)`;
      `frontier (kl:real^3->bool) = kl DIFF interior kl`;
      `(kl:real^3->bool) SUBSET k`; `IMAGE (gg:real^3->real^3) k = x1`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`frontier c' = IMAGE (gg:real^3->real^3) (frontier kl)`;
      `frontier x1 = IMAGE (gg:real^3->real^3) (frontier k)`;
      `frontier x1 = (s1:real^3->bool) UNION d`;
      `!q:real^3. q IN frontier kl /\ ~(q IN nb) ==> q IN frontier k`;
      `!q:real^3. q IN frontier k /\ ~(q IN nb) ==> q IN frontier kl`;
      `!q:real^3. q IN kl ==> ~((gg:real^3->real^3) q IN d)`;
      `frontier (kl:real^3->bool) = kl DIFF interior kl`;
      `frontier (k:real^3->bool) = k DIFF interior k`;
      `(kl:real^3->bool) SUBSET k`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]]);;

(* A point z of k at distance at least e2 from the complement of interior k *)
(* is the image under the homothety of ratio lam about p of a point of      *)
(* interior k, once (1 - lam) is small against e2 and the size B of k.     *)

let MOI_S4N_RATIO_INTERIOR = prove
 (`!(k:real^3->bool) p z lam e2 B.
     p IN k /\ z IN k /\ (!y. y IN k ==> norm y <= B) /\
     (!y. ~(y IN interior k) ==> e2 <= dist(z,y)) /\
     &1 / &2 <= lam /\ lam < &1 /\ (&1 - lam) * (&4 * B) <= e2 / &2 /\ &0 < e2
     ==> p + inv lam % (z - p) IN interior k /\
         lam % (p + inv lam % (z - p)) + (&1 - lam) % p = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 / &2 <= lam` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `!y. ~(y IN interior k) ==> e2 <= dist(z:real^3,y)` THEN
    DISCH_THEN(MP_TAC o SPEC `p + inv lam % (z - p):real^3`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `dist(z:real^3,p + inv lam % (z - p)) = (inv lam - &1) * norm(z - p)`
    SUBST1_TAC THENL
     [REWRITE_TAC[dist] THEN
      SUBGOAL_THEN `z - (p + inv lam % (z - p)):real^3 = (&1 - inv lam) % (z - p)`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `&1 <= inv lam` MP_TAC THENL
       [MATCH_MP_TAC REAL_INV_1_LE THEN
        MAP_EVERY UNDISCH_TAC [`&0 < lam`; `lam < &1`] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv lam - &1 <= &2 * (&1 - lam) /\ &0 <= inv lam - &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `inv lam - &1 = (&1 - lam) / lam` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        MP_TAC(SPECL [`&1 - lam`; `&2 * lam - &1`] REAL_LE_MUL) THEN
        ANTS_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`&1 / &2 <= lam`; `lam < &1`] THEN REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x - &1`) THEN
        MATCH_MP_TAC REAL_INV_1_LE THEN
        MAP_EVERY UNDISCH_TAC [`&0 < lam`; `lam < &1`] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(z - p:real^3) <= &2 * B` ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
        `norm(z:real^3) <= B /\ norm(p:real^3) <= B ==> norm(z - p) <= &2 * B`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(inv lam - &1) * norm(z - p:real^3) <= (&2 * (&1 - lam)) * (&2 * B)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(&1 - lam) * (&4 * B) <= e2 / &2`; `&0 < e2`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `lam * inv lam = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_S4N_PUSH = prove
 (`!x1 d j s1 (K:real^3->bool) W.
     pl_ball 3 x1 /\ pl_cell_with_boundary 2 d j /\
     frontier x1 = s1 UNION d /\ s1 INTER d = j /\
     compact K /\ K SUBSET interior x1 /\ open W /\ d SUBSET W
     ==> ?c' Z. pl_ball 3 c' /\ c' SUBSET x1 /\ K SUBSET interior c' /\
                c' INTER d = {} /\ compact Z /\ Z SUBSET W /\
                frontier c' SUBSET (s1 DIFF j) UNION (W INTER (x1 DIFF d)) /\
                frontier c' DIFF Z = s1 DIFF Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x1:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S4N_PAIR_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `vf:real^3->bool`
    (X_CHOOSE_THEN `gg:real^3->real^3` (X_CHOOSE_THEN `ff:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY ABBREV_TAC [`k = convex hull ((p:real^3) INSERT vf)`;
                        `f = convex hull (vf:real^3->bool)`] THEN
  SUBGOAL_THEN `~(vf:real^3->bool = {}) /\ FINITE vf /\ CARD vf = 3` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(vf:real^3->bool) HAS_SIZE 3` THEN REWRITE_TAC[HAS_SIZE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (vf:real^3->bool) = 3` THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (k:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) SUBSET k /\ compact f` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "k"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4N_SIMPLEX3_FACTS (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `x1:real^3->bool`; `gg:real^3->real^3`;
                 `ff:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `homeomorphism (k,x1) (gg:real^3->real^3,ff)` MP_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (k,x1) (gg:real^3->real^3,ff)`) THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  (* B bounds k *)
  SUBGOAL_THEN `?B. &0 < B /\ !y:real^3. y IN k ==> norm y <= B`
  (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `compact (k:real^3->bool)` THEN
    MESON_TAC[BOUNDED_POS; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  (* e1: f is away from the points of k that gg maps outside W *)
  SUBGOAL_THEN `closed {y | y IN k /\ (gg:real^3->real^3) y IN (:real^3) DIFF W}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; GSYM OPEN_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->bool`;
                 `{y | y IN k /\ (gg:real^3->real^3) y IN (:real^3) DIFF W}`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`IMAGE (gg:real^3->real^3) f = d`; `(d:real^3->bool) SUBSET W`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)] THEN
  (* e2: the image of K under ff is inside interior k *)
  SUBGOAL_THEN `compact (IMAGE (ff:real^3->real^3) K) /\ IMAGE ff K SUBSET interior k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `x1:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `x1:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(K:real^3->bool) SUBSET interior x1` THEN SET_TAC[];
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(K:real^3->bool) SUBSET interior x1`;
        `interior x1 = IMAGE (gg:real^3->real^3) (interior k)`;
        `interior (k:real^3->bool) SUBSET k`;
        `!x. x IN k ==> (ff:real^3->real^3) (gg x) = x`] THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (ff:real^3->real^3) K`; `(:real^3) DIFF interior k`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
    UNDISCH_TAC `IMAGE (ff:real^3->real^3) K SUBSET interior k` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)] THEN
  (* the ratio *)
  ABBREV_TAC `m1 = min e1 (e2 / &2)` THEN
  ABBREV_TAC `del = min (&1 / &2) (m1 / (&4 * B))` THEN
  SUBGOAL_THEN `&0 < del /\ del <= &1 / &2 /\ del * (&4 * B) <= e1 /\
                del * (&4 * B) <= e2 / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < m1 /\ &0 < &4 * B` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m1" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < e1`; `&0 < e2`; `&0 < B`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < m1 / (&4 * B)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `del <= m1 / (&4 * B) /\ &0 < del /\ del <= &1 / &2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "del" THEN UNDISCH_TAC `&0 < m1 / (&4 * B)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `del * (&4 * B) <= m1` MP_TAC THENL
     [UNDISCH_TAC `del <= m1 / (&4 * B)` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`min e1 (e2 / &2) = m1`; `&0 < del`; `del <= &1 / &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = &1 - del` THEN
  SUBGOAL_THEN `&0 < lam /\ lam < &1 /\ &1 / &2 <= lam /\ &1 - lam = del`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MAP_EVERY UNDISCH_TAC [`&0 < del`; `del <= &1 / &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the homothety and the smaller simplex kl *)
  MP_TAC(ISPECL [`p:real^3`; `vf:real^3->bool`; `lam:real`] MOI_S4N_HOMOTHETY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `convex hull ((p:real^3) INSERT vf) = k`;
              ASSUME `convex hull (vf:real^3->bool) = f`] THEN
  MP_TAC(ISPECL [`\x:real^3. lam % x`; `(&1 - lam) % (p:real^3)`; `&3:int`;
                 `k:real^3->bool`] MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  REWRITE_TAC[LINEAR_SCALING] THEN BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(lam = &0)` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LCANCEL]) THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kl = IMAGE (\y. lam % y + (&1 - lam) % p) (k:real^3->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "near") ASSUME_TAC))) THEN
  MP_TAC(MATCH_MP MOI_S4N_SIMPLEX3_FACTS (ASSUME `&3 simplex (kl:real^3->bool)`)) THEN
  STRIP_TAC THEN
  (* the closed neighbourhood nb of the facet *)
  ABBREV_TAC `nb = {a + b:real^3 | a IN f /\ b IN cball(vec 0,e1 / &2)}` THEN
  SUBGOAL_THEN `compact (nb:real^3->bool) /\
                (!y. y IN nb <=> ?a. a IN f /\ norm(y - a) <= e1 / &2)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nbc")) THENL
   [EXPAND_TAC "nb" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
      EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB];
        DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`a:real^3`; `y - a:real^3`] THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (nb:real^3->bool) /\ compact (k INTER nb:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `k DIFF kl SUBSET (nb:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "nbc" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "near" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:real^3` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(p - a:real^3) <= &2 * B` ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
        `norm(p:real^3) <= B /\ norm(a:real^3) <= B ==> norm(p - a) <= &2 * B`) THEN
      SUBGOAL_THEN `(a:real^3) IN k` ASSUME_TAC THENL
       [UNDISCH_TAC `(a:real^3) IN f` THEN UNDISCH_TAC `(f:real^3->bool) SUBSET k` THEN
        SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        concl th = `!y:real^3. y IN k ==> norm y <= B`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `del * norm(p - a:real^3) <= del * (&2 * B)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `norm(y - a:real^3) <= (&1 - lam) * norm(p - a)` THEN
    REWRITE_TAC[ASSUME `&1 - lam = del`] THEN
    UNDISCH_TAC `del * (&4 * B) <= e1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gg:real^3->real^3) (k INTER nb) SUBSET W` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN
    USE_THEN "nbc" (fun th -> MP_TAC(EQ_MP (SPEC `y:real^3` th)
                                         (ASSUME `(y:real^3) IN nb`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `y:real^3`] o check (fun th ->
      can (find_term ((=) `e1:real`)) (concl th) && is_forall (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`norm(y - a:real^3) <= e1 / &2`; `&0 < e1`] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REMOVE_THEN "nbc" (K ALL_TAC) THEN REMOVE_THEN "near" (K ALL_TAC) THEN
  (* the new ball c' *)
  SUBGOAL_THEN `pl_homeomorphism (kl,IMAGE (gg:real^3->real^3) kl) (gg,ff)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `x1:real^3->bool`] THEN
    REWRITE_TAC[ASSUME `pl_homeomorphism (k,x1) (gg:real^3->real^3,ff)`;
                ASSUME `(kl:real^3->bool) SUBSET k`] THEN
    SUBGOAL_THEN `pl_polyhedron (kl:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&3:int` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    REWRITE_TAC[ASSUME `(kl:real^3->bool) SUBSET k`] THEN
    CONJ_TAC THENL
     [MP_TAC(ASSUME `pl_homeomorphism (k,x1) (gg:real^3->real^3,ff)`) THEN
      SIMP_TAC[pl_homeomorphism];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `c' = IMAGE (gg:real^3->real^3) kl` THEN
  MP_TAC(ISPECL [`kl:real^3->bool`; `c':real^3->bool`; `gg:real^3->real^3`;
                 `ff:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* frontier bookkeeping *)
  MP_TAC(ISPECL [`k:real^3->bool`; `kl:real^3->bool`; `nb:real^3->bool`;
                 `f:real^3->bool`; `gg:real^3->real^3`; `ff:real^3->real^3`;
                 `x1:real^3->bool`; `c':real^3->bool`; `s1:real^3->bool`;
                 `d:real^3->bool`; `j:real^3->bool`] MOI_S4N_SLAB_FRONTIER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `frontier x1 = IMAGE (gg:real^3->real^3) (relative_frontier k)` THEN
      REWRITE_TAC[ASSUME `relative_frontier (k:real^3->bool) = frontier k`];
      UNDISCH_TAC `frontier c' = IMAGE (gg:real^3->real^3) (relative_frontier kl)` THEN
      REWRITE_TAC[ASSUME `relative_frontier (kl:real^3->bool) = frontier kl`]];
    STRIP_TAC] THEN
  (* the witnesses *)
  MAP_EVERY EXISTS_TAC [`c':real^3->bool`; `IMAGE (gg:real^3->real^3) (k INTER nb)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`kl:real^3->bool`; `gg:real^3->real^3`; `ff:real^3->real^3`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`IMAGE (gg:real^3->real^3) kl = c'`;
                           `(kl:real^3->bool) SUBSET k`;
                           `IMAGE (gg:real^3->real^3) k = x1`] THEN
    SET_TAC[];
    (* K inside the new interior *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^3->real^3) z0 IN interior k` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (ff:real^3->real^3) K SUBSET interior k` THEN
      UNDISCH_TAC `(z0:real^3) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gg:real^3->real^3) (ff z0) = z0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        concl th = `!y. y IN x1 ==> (gg:real^3->real^3) (ff y) = y`)) THEN
      MP_TAC(ISPEC `x1:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(K:real^3->bool) SUBSET interior x1` THEN
      UNDISCH_TAC `(z0:real^3) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `p:real^3`; `(ff:real^3->real^3) z0`; `lam:real`;
                   `e2:real`; `B:real`] MOI_S4N_RATIO_INTERIOR) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(ff:real^3->real^3) z0 IN interior k` THEN
        UNDISCH_TAC `interior (k:real^3->bool) SUBSET k` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `e2:real`)) (concl th) && is_forall (concl th))) THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
         [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z0:real^3` THEN
          CONJ_TAC THENL [REFL_TAC; FIRST_ASSUM ACCEPT_TAC];
          FIRST_ASSUM ACCEPT_TAC];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[ASSUME `&1 - lam = del`] THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `z' = p + inv lam % ((ff:real^3->real^3) z0 - p)` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(ff:real^3->real^3) z0 IN interior kl` ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `interior kl =
        IMAGE (\y. lam % y + (&1 - lam) % p) (interior (k:real^3->bool))`] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z':real^3` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(gg:real^3->real^3) (ff z0) = z0`;
                           `(ff:real^3->real^3) z0 IN interior kl`;
                           `interior c' = IMAGE (gg:real^3->real^3) (interior kl)`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    (* c' misses d *)
    MAP_EVERY UNDISCH_TAC [`IMAGE (gg:real^3->real^3) kl = c'`;
                           `IMAGE (gg:real^3->real^3) f = d`;
                           `(kl:real^3->bool) SUBSET k`; `(f:real^3->bool) SUBSET k`;
                           `kl INTER (f:real^3->bool) = {}`;
                           `!x. x IN k ==> (ff:real^3->real^3) (gg x) = x`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    (* Z compact *)
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN FIRST_ASSUM ACCEPT_TAC;
    (* Z inside W *)
    FIRST_ASSUM ACCEPT_TAC;
    (* the new frontier *)
    MAP_EVERY UNDISCH_TAC
     [`frontier c' SUBSET (s1 DIFF j) UNION
       (IMAGE (gg:real^3->real^3) (k INTER nb) INTER (x1 DIFF d))`;
      `IMAGE (gg:real^3->real^3) (k INTER nb) SUBSET W`] THEN
    SET_TAC[];
    (* agreement outside Z *)
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S4N_COMPRESS = prove
 (`!c d j (K:real^3->bool) W.
     PL_SCHOENFLIES_3_STATEMENT /\
     pl_ball 3 c /\ pl_cell_with_boundary 2 d j /\ d INTER frontier c = j /\
     d DIFF j SUBSET interior c /\
     compact K /\ connected K /\ K SUBSET interior c /\ K INTER d = {} /\
     open W /\ d SUBSET W
     ==> ?c' s1 s2 Z. pl_ball 3 c' /\ c' SUBSET c /\ K SUBSET interior c' /\
                      closed s1 /\ closed s2 /\ s1 UNION s2 = frontier c /\
                      s1 INTER s2 = j /\ compact Z /\ Z SUBSET W /\
                      c' INTER frontier c SUBSET s1 DIFF j /\
                      frontier c' SUBSET (s1 DIFF j) UNION (W INTER (c DIFF d)) /\
                      frontier c' DIFF Z = s1 DIFF Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3->bool. pl_ball 3 x
                  ==> compact x /\ closed x /\ frontier x SUBSET x /\
                      interior x = x DIFF frontier x` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `g0:real^3->real^3`
      (X_CHOOSE_THEN `f0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `x:real^3->bool`; `g0:real^3->real^3`;
                   `f0:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (c:real^3->bool) /\ closed c /\ frontier c SUBSET c /\
                interior c = c DIFF frontier c` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `c:real^3->bool` th) THEN ASSUME_TAC th) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:real^3->bool` (X_CHOOSE_THEN `fd:real^3->real^3`
    (X_CHOOSE_THEN `gd:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET c` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`d DIFF j SUBSET interior (c:real^3->bool)`;
                           `d INTER frontier c = (j:real^3->bool)`;
                           `frontier (c:real^3->bool) SUBSET c`;
                           `interior (c:real^3->bool) = c DIFF frontier c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S5N_SPLIT_BALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3->bool` (X_CHOOSE_THEN `x2:real^3->bool`
    (X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `s2:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `closed (x1:real^3->bool) /\ closed (x2:real^3->bool) /\
                interior x1 = x1 DIFF frontier x1 /\
                interior x2 = x2 DIFF frontier x2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^3->bool. pl_ball 3 x
                  ==> compact x /\ closed x /\ frontier x SUBSET x /\
                      interior x = x DIFF frontier x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x1:real^3->bool` th) THEN
                         MP_TAC(SPEC `x2:real^3->bool` th)) THEN
    REWRITE_TAC[ASSUME `pl_ball 3 (x1:real^3->bool)`;
                ASSUME `pl_ball 3 (x2:real^3->bool)`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (s1:real^3->bool) /\ closed (s2:real^3->bool) /\
                j SUBSET (s1:real^3->bool) /\ j SUBSET (s2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
      (ASSUME `pl_cell_with_boundary 2 (s1:real^3->bool) j`)) THEN
    MP_TAC(MATCH_MP MOI_SS2_CELL_FACTS
      (ASSUME `pl_cell_with_boundary 2 (s2:real^3->bool) j`)) THEN
    MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET x1 /\ (s2:real^3->bool) SUBSET x2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP FRONTIER_SUBSET_CLOSED (ASSUME `closed (x1:real^3->bool)`)) THEN
    MP_TAC(MATCH_MP FRONTIER_SUBSET_CLOSED (ASSUME `closed (x2:real^3->bool)`)) THEN
    MAP_EVERY UNDISCH_TAC [`frontier x1 = s1 UNION (d:real^3->bool)`;
                           `frontier x2 = s2 UNION (d:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^3->bool) INTER d = j /\ (s2:real^3->bool) INTER d = j`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`s1 UNION s2 = frontier (c:real^3->bool)`;
                           `d INTER frontier c = (j:real^3->bool)`;
                           `j SUBSET (s1:real^3->bool)`; `j SUBSET (s2:real^3->bool)`;
                           `j SUBSET (d:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* K lies on one side *)
  SUBGOAL_THEN `(K:real^3->bool) SUBSET x1 \/ K SUBSET x2` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (K:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`x1:real^3->bool`; `x2:real^3->bool`]) THEN
    REWRITE_TAC[ASSUME `closed (x1:real^3->bool)`; ASSUME `closed (x2:real^3->bool)`] THEN
    MAP_EVERY UNDISCH_TAC [`x1 UNION x2 = (c:real^3->bool)`;
                           `x1 INTER x2 = (d:real^3->bool)`;
                           `K INTER d = {}:real^3->bool`;
                           `(K:real^3->bool) SUBSET interior c`] THEN
    MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL [`x1:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `s1:real^3->bool`; `K:real^3->bool`; `W:real^3->bool`]
      MOI_S4N_PUSH) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY UNDISCH_TAC [`(K:real^3->bool) SUBSET x1`;
                             `interior x1 = x1 DIFF frontier (x1:real^3->bool)`;
                             `frontier x1 = s1 UNION (d:real^3->bool)`;
                             `K INTER d = {}:real^3->bool`;
                             `(K:real^3->bool) SUBSET interior c`;
                             `interior (c:real^3->bool) = c DIFF frontier c`;
                             `s1 UNION s2 = frontier (c:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` (X_CHOOSE_THEN `Z:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c':real^3->bool`; `s1:real^3->bool`; `s2:real^3->bool`;
                          `Z:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`(c':real^3->bool) SUBSET x1`;
                             `x1 UNION x2 = (c:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`(c':real^3->bool) SUBSET x1`; `c' INTER d = {}:real^3->bool`;
                             `(s2:real^3->bool) SUBSET x2`; `x1 INTER x2 = (d:real^3->bool)`;
                             `s1 UNION s2 = frontier (c:real^3->bool)`;
                             `j SUBSET (d:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`frontier c' SUBSET (s1 DIFF j) UNION
                              ((W:real^3->bool) INTER (x1 DIFF d))`;
                             `x1 UNION x2 = (c:real^3->bool)`] THEN SET_TAC[]];
    MP_TAC(ISPECL [`x2:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `s2:real^3->bool`; `K:real^3->bool`; `W:real^3->bool`]
      MOI_S4N_PUSH) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MAP_EVERY UNDISCH_TAC [`(K:real^3->bool) SUBSET x2`;
                             `interior x2 = x2 DIFF frontier (x2:real^3->bool)`;
                             `frontier x2 = s2 UNION (d:real^3->bool)`;
                             `K INTER d = {}:real^3->bool`;
                             `(K:real^3->bool) SUBSET interior c`;
                             `interior (c:real^3->bool) = c DIFF frontier c`;
                             `s1 UNION s2 = frontier (c:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` (X_CHOOSE_THEN `Z:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c':real^3->bool`; `s2:real^3->bool`; `s1:real^3->bool`;
                          `Z:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`(c':real^3->bool) SUBSET x2`;
                             `x1 UNION x2 = (c:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`s1 UNION s2 = frontier (c:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`s1 INTER s2 = (j:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`(c':real^3->bool) SUBSET x2`; `c' INTER d = {}:real^3->bool`;
                             `(s1:real^3->bool) SUBSET x1`; `x1 INTER x2 = (d:real^3->bool)`;
                             `s1 UNION s2 = frontier (c:real^3->bool)`;
                             `j SUBSET (d:real^3->bool)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`frontier c' SUBSET (s2 DIFF j) UNION
                              ((W:real^3->bool) INTER (x2 DIFF d))`;
                             `x1 UNION x2 = (c:real^3->bool)`] THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Crossing charts: a ball chart from pl_crossing_at, the two sides of      *)
(* the chart, and the local form of a surface S crossing the frontier of c  *)
(* along the rim of a disk d of S inside c: near the rim, the surface meets *)
(* c only in d (MOI_S4N_CROSS_DISK).                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_BALL_CHART = prove
 (`!(s:real^3->bool) t y oo.
     pl_crossing_at s t y /\ open oo /\ y IN oo
     ==> ?U (phi:real^3->real^3) psi r.
           &0 < r /\ open U /\ y IN U /\ U SUBSET oo /\ phi y = vec 0 /\
           (!x. x IN U ==> phi x IN ball(vec 0,r) /\ psi (phi x) = x) /\
           (!z. z IN ball(vec 0,r) ==> psi z IN U /\ phi (psi z) = z) /\
           psi continuous_on ball(vec 0,r) /\
           (!z. z IN ball(vec 0,r) ==> (psi z IN s <=> z$1 = &0) /\
                                       (psi z IN t <=> z$2 = &0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u0:real^3->bool`
    (X_CHOOSE_THEN `phi:real^3->real^3` (X_CHOOSE_THEN `psi:real^3->real^3`
      STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphism"
    with Failure _ -> false)) THEN
  ABBREV_TAC `V = IMAGE (phi:real^3->real^3) u0` THEN
  SUBGOAL_THEN `open {z | z IN V /\ (psi:real^3->real^3) z IN oo}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN {z | z IN V /\ (psi:real^3->real^3) z IN oo}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `(phi:real^3->real^3) y = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`IMAGE (phi:real^3->real^3) u0 = V`; `(y:real^3) IN u0`;
                           `(y:real^3) IN oo`;
                           `!x. x IN u0 ==> (psi:real^3->real^3) (phi x) = x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{z | z IN V /\ (psi:real^3->real^3) z IN oo}` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[ASSUME `open {z | z IN V /\ (psi:real^3->real^3) z IN oo}`] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN
  REWRITE_TAC[ASSUME `(vec 0:real^3) IN {z | z IN V /\ (psi:real^3->real^3) z IN oo}`] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {x | x IN u0 /\ (phi:real^3->real^3) x IN ball(vec 0,r)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`{x | x IN u0 /\ (phi:real^3->real^3) x IN ball(vec 0,r)}`;
                        `phi:real^3->real^3`; `psi:real^3->real^3`; `r:real`] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) SUBSET V` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET {z | z IN V /\ (psi:real^3->real^3) z IN oo}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    MAP_EVERY UNDISCH_TAC
     [`ball(vec 0:real^3,r) SUBSET {z | z IN V /\ (psi:real^3->real^3) z IN oo}`;
      `!x. x IN u0 ==> (psi:real^3->real^3) (phi x) = x`] THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `!x. x IN u0 ==> (psi:real^3->real^3) (phi x) = x` THEN SIMP_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET V` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN V`; `(z:real^3) IN ball(vec 0,r)`;
                           `IMAGE (psi:real^3->real^3) V = u0`;
                           `!y. y IN V ==> (phi:real^3->real^3) (psi y) = y`] THEN
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET V` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN V`;
      `IMAGE (phi:real^3->real^3) (s INTER u0) = V INTER {y | y$1 = &0}`;
      `IMAGE (phi:real^3->real^3) (t INTER u0) = V INTER {y | y$2 = &0}`;
      `IMAGE (phi:real^3->real^3) u0 = V`; `IMAGE (psi:real^3->real^3) V = u0`;
      `!x. x IN u0 ==> (psi:real^3->real^3) (phi x) = x`;
      `!y. y IN V ==> (phi:real^3->real^3) (psi y) = y`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

(* One side of the chart: the open half ball, and the half disk in the     *)
(* second coordinate plane, are mapped by psi into one side of c, resp.     *)
(* into d or off d.                                                         *)

let MOI_S4N_CHART_SIDE = prove
 (`!c B S d E (U:real^3->bool) oo (phi:real^3->real^3) psi r sg.
     closed c /\ U SUBSET oo /\ B INTER oo SUBSET S /\
     closed d /\ closed E /\ S DIFF E SUBSET d /\ d INTER E SUBSET frontier c /\
     (!z. z IN ball(vec 0,r) ==> psi z IN U /\ phi (psi z) = z) /\
     psi continuous_on ball(vec 0,r) /\
     (!z. z IN ball(vec 0,r) ==> (psi z IN frontier c <=> z$1 = &0) /\
                                 (psi z IN B <=> z$2 = &0)) /\
     (sg = &1 \/ sg = -- &1)
     ==> (IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET interior c \/
          IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER c = {}) /\
         (IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET d \/
          IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} INTER d = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `convex {z:real^3 | &0 < sg * z$1}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0] THENL
     [REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected (IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}) /\
    connected (IMAGE (psi:real^3->real^3)
                {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `{z:real^3 | z IN ball(vec 0,r) /\ &0 < sg * z$1} =
                    ball(vec 0,r) INTER {z | &0 < sg * z$1}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
       [REWRITE_TAC[CONVEX_BALL]; FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `{z:real^3 | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} =
                    ball(vec 0,r) INTER {z | &0 < sg * z$1} INTER {z | z$2 = &0}`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
      MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER
    frontier c = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      can (find_term ((=) `frontier (c:real^3->bool)`)) (concl th) &&
      is_forall (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < sg * (z:real^3)$1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ABBREV_TAC `T0 = IMAGE (psi:real^3->real^3)
                       {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}` THEN
    MP_TAC(ISPECL [`T0:real^3->bool`; `c:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `frontier c = c DIFF interior (c:real^3->bool)` MP_TAC THENL
     [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED]; ALL_TAC] THEN
    UNDISCH_TAC `T0 INTER frontier c = {}:real^3->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = IMAGE (psi:real^3->real^3)
                    {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0}` THEN
  SUBGOAL_THEN `(Q:real^3->bool) SUBSET S /\ Q INTER frontier c = {}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        can (find_term ((=) `frontier (c:real^3->bool)`)) (concl th) &&
        is_forall (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        can (find_term ((=) `U:real^3->bool`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(U:real^3->bool) SUBSET oo`;
                             `(B:real^3->bool) INTER oo SUBSET S`] THEN
      SET_TAC[];
      UNDISCH_TAC
       `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER
        frontier c = {}` THEN
      EXPAND_TAC "Q" THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (Q:real^3->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`d:real^3->bool`; `E:real^3->bool`]) THEN
  REWRITE_TAC[ASSUME `closed (d:real^3->bool)`; ASSUME `closed (E:real^3->bool)`] THEN
  MAP_EVERY UNDISCH_TAC [`(Q:real^3->bool) SUBSET S`; `Q INTER frontier c = {}:real^3->bool`;
                         `S DIFF E SUBSET (d:real^3->bool)`;
                         `d INTER E SUBSET frontier (c:real^3->bool)`] THEN
  SET_TAC[]);;

(* Finishing the chart argument: if the half disk of side sg lies in d and  *)
(* the opposite half ball misses c, then near y the surface B meets c only  *)
(* in d (points on the crossing line are limits of the half disk).          *)

let MOI_S4N_CHART_FINISH = prove
 (`!c B d (U:real^3->bool) (phi:real^3->real^3) psi r sg sg'.
     closed d /\
     (!x. x IN U ==> phi x IN ball(vec 0,r) /\ psi (phi x) = x) /\
     (!z. z IN ball(vec 0,r) ==> psi z IN U /\ phi (psi z) = z) /\
     psi continuous_on ball(vec 0,r) /\
     (!z. z IN ball(vec 0,r) ==> (psi z IN B <=> z$2 = &0)) /\
     (sg = &1 \/ sg = -- &1) /\ sg' = --sg /\
     IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET d /\
     IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} INTER c = {}
     ==> U INTER c INTER B SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x IN ball(vec 0,r) /\ psi (phi x) = x`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!x. x IN U ==> (phi:real^3->real^3) x IN ball(vec 0,r) /\
                                         psi (phi x) = x`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z = (phi:real^3->real^3) x` THEN
  SUBGOAL_THEN `(z:real^3)$2 = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      can (find_term ((=) `B:real^3->bool`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg * sg = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < sg * (z:real^3)$1` THENL
   [UNDISCH_TAC
     `IMAGE (psi:real^3->real^3)
        {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET d` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `sg * (z:real^3)$1 < &0` THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN UNDISCH_TAC
     `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} INTER
      c = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[REAL_MUL_LNEG] THEN
      UNDISCH_TAC `sg * (z:real^3)$1 < &0` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$1 = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `sg * (z:real^3)$1 = &0` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(&0 < sg * (z:real^3)$1)`; `~(sg * (z:real^3)$1 < &0)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(sg = &0)` (fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN UNDISCH_TAC `sg * sg = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* x is a limit of points of the half disk *)
  MP_TAC(ISPECL
   [`IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0}`;
    `d:real^3->bool`] CLOSURE_MINIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `(psi:real^3->real^3) continuous_on ball(vec 0,r)` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ball(vec 0:real^3,r)` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = min del rho / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < del /\ t < rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MAP_EVERY UNDISCH_TAC [`&0 < del`; `&0 < rho`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z' = z + (t * sg) % basis 1:real^3` THEN
  SUBGOAL_THEN `dist(z':real^3,z) = t` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN REWRITE_TAC[dist; VECTOR_ARITH `(z + a) - z:real^3 = a`] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs sg = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN ball(vec 0,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,rho) SUBSET ball(vec 0,r)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(psi:real^3->real^3) z'` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `z':real^3` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "z'" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ARITH `sg * t * sg = t * (sg * sg)`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(ASSUME `!x'. x' IN ball(vec 0,r) /\ dist(x',z) < del
                               ==> dist((psi:real^3->real^3) x',x) < e`) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4N_CROSS_DISK = prove
 (`!c B S d E (y:real^3) oo.
     closed c /\ pl_crossing_at (frontier c) B y /\ y IN frontier c /\
     open oo /\ y IN oo /\ B INTER oo SUBSET S /\
     d SUBSET B /\ closed d /\ closed E /\ S DIFF E SUBSET d /\
     d INTER E SUBSET frontier c /\ y IN closure (d INTER interior c)
     ==> ?u. open u /\ y IN u /\ u INTER c INTER B SUBSET d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier c:real^3->bool`; `B:real^3->bool`; `y:real^3`;
                 `oo:real^3->bool`] MOI_S4N_BALL_CHART) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `phi:real^3->real^3`
    (X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `U:real^3->bool` THEN
  REWRITE_TAC[ASSUME `open (U:real^3->bool)`; ASSUME `(y:real^3) IN U`] THEN
  (* the two sides *)
  MP_TAC(ISPECL [`c:real^3->bool`; `B:real^3->bool`; `S:real^3->bool`; `d:real^3->bool`;
                 `E:real^3->bool`; `U:real^3->bool`; `oo:real^3->bool`;
                 `phi:real^3->real^3`; `psi:real^3->real^3`; `r:real`; `&1`]
    MOI_S4N_CHART_SIDE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `B:real^3->bool`; `S:real^3->bool`; `d:real^3->bool`;
                 `E:real^3->bool`; `U:real^3->bool`; `oo:real^3->bool`;
                 `phi:real^3->real^3`; `psi:real^3->real^3`; `r:real`; `-- &1`]
    MOI_S4N_CHART_SIDE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  (* not both half balls inside c *)
  SUBGOAL_THEN
   `~(IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < &1 * z$1} SUBSET c /\
      IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < -- &1 * z$1} SUBSET c)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(U:real^3->bool) SUBSET c` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(MP (SPEC `x:real^3` (ASSUME `!x. x IN U ==> (phi:real^3->real^3) x IN
                                           ball(vec 0,r) /\ psi (phi x) = x`))
                (ASSUME `(x:real^3) IN U`)) THEN
      STRIP_TAC THEN
      ASM_CASES_TAC `((phi:real^3->real^3) x)$1 = &0` THENL
       [SUBGOAL_THEN `(x:real^3) IN frontier c` MP_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `(phi:real^3->real^3) x` o check (fun th ->
            can (find_term ((=) `frontier (c:real^3->bool)`)) (concl th) &&
            is_forall (concl th))) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          MP_TAC(MATCH_MP FRONTIER_SUBSET_CLOSED (ASSUME `closed (c:real^3->bool)`)) THEN
          SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 * ((phi:real^3->real^3) x)$1 \/
                    &0 < -- &1 * ((phi:real^3->real^3) x)$1` MP_TAC THENL
       [UNDISCH_TAC `~(((phi:real^3->real^3) x)$1 = &0)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `IMAGE (psi:real^3->real^3)
                       {z | z IN ball(vec 0,r) /\ &0 < &1 * z$1} SUBSET c`;
        UNDISCH_TAC `IMAGE (psi:real^3->real^3)
                       {z | z IN ball(vec 0,r) /\ &0 < -- &1 * z$1} SUBSET c`] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(phi:real^3->real^3) x`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN frontier c` THEN REWRITE_TAC[frontier; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ y IN s ==> (y:real^3) IN t`) THEN
    EXISTS_TAC `U:real^3->bool` THEN REWRITE_TAC[ASSUME `(y:real^3) IN U`] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* a point of d inside c near y *)
  SUBGOAL_THEN `?x0:real^3. x0 IN U /\ x0 IN d /\ x0 IN interior c`
  (X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `d INTER interior c:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[ASSUME `open (U:real^3->bool)`] THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN U`;
                           `(y:real^3) IN closure (d INTER interior c)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x0 IN ball(vec 0,r) /\ psi (phi x0) = x0`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!x. x IN U ==> (phi:real^3->real^3) x IN ball(vec 0,r) /\
                                         psi (phi x) = x`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z0 = (phi:real^3->real^3) x0` THEN
  SUBGOAL_THEN `(z0:real^3)$2 = &0 /\ ~((z0:real^3)$1 = &0)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3` o check (fun th ->
      can (find_term ((=) `frontier (c:real^3->bool)`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x0:real^3) IN B /\ ~(x0 IN frontier c)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(x0:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET B` THEN
        SET_TAC[];
        UNDISCH_TAC `(x0:real^3) IN interior c` THEN REWRITE_TAC[frontier] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  (* the side of x0 *)
  SUBGOAL_THEN
   `!sg sg'. (sg = &1 \/ sg = -- &1) /\ sg' = --sg /\ &0 < sg * (z0:real^3)$1 /\
             (IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}
              SUBSET interior c \/
              IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER c = {}) /\
             (IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET d \/
              IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} INTER d =
              {}) /\
             (IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} SUBSET interior c \/
              IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} INTER c = {}) /\
             ~(IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET c /\
               IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} SUBSET c)
             ==> U INTER c INTER B SUBSET d`
  MATCH_MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`sg:real`; `sg':real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
    SUBGOAL_THEN `(x0:real^3) IN IMAGE (psi:real^3->real^3)
                    {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0}`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4N_CHART_FINISH THEN
    MAP_EVERY EXISTS_TAC [`phi:real^3->real^3`; `psi:real^3->real^3`; `r:real`;
                          `sg:real`; `sg':real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        can (find_term ((=) `frontier (c:real^3->bool)`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x0:real^3) IN IMAGE (psi:real^3->real^3)
           {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0}`;
        `(x0:real^3) IN d`;
        `IMAGE (psi:real^3->real^3)
           {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET d \/
         IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} INTER d = {}`] THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (psi:real^3->real^3)
                      {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0} SUBSET
                    IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x0:real^3) IN IMAGE (psi:real^3->real^3)
           {z | z IN ball(vec 0,r) /\ &0 < sg * z$1 /\ z$2 = &0}`;
        `(x0:real^3) IN interior c`;
        `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1}
           SUBSET interior c \/
         IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} INTER c = {}`;
        `IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1}
           SUBSET interior c \/
         IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} INTER c = {}`;
        `~(IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < sg * z$1} SUBSET c /\
           IMAGE psi {z | z IN ball(vec 0,r) /\ &0 < sg' * z$1} SUBSET c)`] THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (z0:real^3)$1` THENL
   [EXISTS_TAC `&1` THEN EXISTS_TAC `-- &1` THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC;
    EXISTS_TAC `-- &1` THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(&0 < (z0:real^3)$1)`; `~((z0:real^3)$1 = &0)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `~(IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < &1 * z$1} SUBSET c /\
        IMAGE (psi:real^3->real^3) {z | z IN ball(vec 0,r) /\ &0 < -- &1 * z$1} SUBSET c)` THEN
    CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* Near the compressing disk d the tube boundary meets the face ball         *)
(* only in d (MOI_S4N_KEY): off the rim, d is open in the vertex sphere     *)
(* (DISK_COMPLEMENT); on the rim, by the crossing charts (MOI_S4N_CROSS_DISK). *)
(* The open set W of the compression (MOI_S4N_W_CHOICE).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_KEY = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ d DIFF j SUBSET interior (cb s)
     ==> !y. y IN d ==> ?u. open u /\ y IN u /\
                            u INTER cb s INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s34_op1w tt kk (f1:real^N->real^3) cb s v d j` THEN
  REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `c = (cb:(real^N->bool)->real^3->bool) s` THEN
  ABBREV_TAC `B = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `Av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `S = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  (* y lies in no other vertex ball *)
  SUBGOAL_THEN `!w. {w} IN kk /\ ~(w = v)
                    ==> ~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
                   `y:real^3`] MOI_S4L_AV_NO_OTHER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET Av` THEN
      EXPAND_TAC "Av" THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_sd")) (concl th) &&
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN t`; `(y:real^3) IN d`] THEN
    REWRITE_TAC[ASSUME `t = IMAGE (f1:real^N->real^3)
                              (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the local form of B near y *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `y:real^3`]
    MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET Av` THEN
    EXPAND_TAC "Av" THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = B`;
              ASSUME `IMAGE (f1:real^N->real^3)
                        (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) = Av`] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the vertex sphere and the complementary disk *)
  SUBGOAL_THEN `(Av:real^3->bool) SUBSET S /\ pl_sphere 2 S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(S:real^3->bool) =
                   Av UNION UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                                    g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
      SET_TAC[];
      EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_S4L_BALL_FRONTIER_SPHERE THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET S /\ d SUBSET B` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(d:real^3->bool) SUBSET Av`; `(Av:real^3->bool) SUBSET S`;
                           `(Av:real^3->bool) SUBSET B`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`] DISK_COMPLEMENT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `E = ((S:real^3->bool) DIFF d) UNION j` THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (E:real^3->bool) /\ closed (d:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THENL
     [MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
        (ASSUME `pl_cell_with_boundary 2 (E:real^3->bool) j`)) THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) DIFF E SUBSET d /\ d INTER E = j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN UNDISCH_TAC `(j:real^3->bool) SUBSET d` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3) IN j` THENL
   [(* on the rim: the crossing chart *)
    MATCH_MP_TAC MOI_S4N_CROSS_DISK THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `E:real^3->bool`; `oo:real^3->bool`] THEN
    SUBGOAL_THEN `(y:real^3) IN frontier c` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(y:real^3) IN j`; `d INTER frontier c = (j:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c
                       ==> pl_crossing_at (frontier c) B x` THEN
      REWRITE_TAC[moi_s34_trace; ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = B`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTER; ASSUME `(y:real^3) IN frontier c`] THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN UNDISCH_TAC `(d:real^3->bool) SUBSET B` THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`B INTER oo SUBSET (Av:real^3->bool)`;
                             `(Av:real^3->bool) SUBSET S`] THEN
      SET_TAC[];
      UNDISCH_TAC `d INTER E = (j:real^3->bool)` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `d INTER frontier c = (j:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s. y IN s /\ s SUBSET t ==> (y:real^3) IN t`) THEN
      EXISTS_TAC `closure (d DIFF j:real^3->bool)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `(d:real^3->bool) SUBSET closure (d DIFF j)` THEN
        UNDISCH_TAC `(y:real^3) IN d` THEN SET_TAC[];
        MATCH_MP_TAC SUBSET_CLOSURE THEN
        UNDISCH_TAC `d DIFF j SUBSET interior (c:real^3->bool)` THEN SET_TAC[]]];
    (* off the rim: d is open in the sphere *)
    EXISTS_TAC `oo DIFF E:real^3->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                    ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      EXPAND_TAC "E" THEN
      MAP_EVERY UNDISCH_TAC [`(y:real^3) IN d`; `~((y:real^3) IN j)`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`B INTER oo SUBSET (Av:real^3->bool)`;
                             `(Av:real^3->bool) SUBSET S`;
                             `(S:real^3->bool) DIFF E SUBSET d`] THEN
      SET_TAC[]]]);;

let MOI_S4N_W_CHOICE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ d DIFF j SUBSET interior (cb s)
     ==> ?W. open W /\ d SUBSET W /\ W SUBSET car {v} /\
             W INTER cb s INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4N_KEY) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `uu:real^3->real^3->bool`) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_op1w] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_op1w")) (concl th))) THEN
  EXISTS_TAC `car {v:real^N} INTER UNIONS (IMAGE (uu:real^3->real^3->bool) d)` THEN
  SUBGOAL_THEN `open (car {v:real^N}:real^3->bool) /\
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `{v:real^N}` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_ball")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (find_term ((=) `uu:real^3->real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(d:real^3->bool) SUBSET IMAGE (f1:real^N->real^3)
                                  (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v}`] THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN EXISTS_TAC `(uu:real^3->real^3->bool) y` THEN
      CONJ_TAC THENL [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        can (find_term ((=) `uu:real^3->real^3->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!(c:real^3->bool) B (uu:real^3->real^3->bool) d a.
       (!y. y IN d ==> uu y INTER c INTER B SUBSET d)
       ==> (a INTER UNIONS (IMAGE uu d)) INTER c INTER B SUBSET d`) THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      can (find_term ((=) `uu:real^3->real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The new face ball: its trace is the old trace on the kept side minus      *)
(* the rim j (a component of the old trace), the frontier agrees with the   *)
(* old one near every new trace point, and the one-face invariant (without *)
(* the H_1 clause), the two-face invariant and the rank transfer.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_NEW_TRACE = prove
 (`!c c' B d j s1 s2 W Z:real^3->bool.
     frontier c SUBSET c /\ s1 UNION s2 = frontier c /\ s1 INTER s2 = j /\
     closed s2 /\ compact Z /\ Z SUBSET W /\ j SUBSET d /\ d INTER frontier c = j /\
     W INTER c INTER B SUBSET d /\
     frontier c' SUBSET (s1 DIFF j) UNION (W INTER (c DIFF d)) /\
     frontier c' DIFF Z = s1 DIFF Z
     ==> frontier c' INTER B = (s1 INTER frontier c INTER B) DIFF j /\
         (!x. x IN frontier c' INTER B
              ==> ?u. open u /\ x IN u /\ frontier c' INTER u = frontier c INTER u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier c' INTER B = (s1 INTER frontier c INTER B) DIFF (j:real^3->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`frontier c SUBSET (c:real^3->bool)`; `s1 UNION s2 = frontier (c:real^3->bool)`;
      `s1 INTER s2 = (j:real^3->bool)`; `(Z:real^3->bool) SUBSET W`;
      `d INTER frontier c = (j:real^3->bool)`;
      `W INTER c INTER B SUBSET (d:real^3->bool)`;
      `frontier c' SUBSET (s1 DIFF j) UNION ((W:real^3->bool) INTER (c DIFF d))`;
      `frontier c' DIFF Z = (s1:real^3->bool) DIFF Z`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `(:real^3) DIFF (Z UNION s2)` THEN
  SUBGOAL_THEN `~((x:real^3) IN W) /\ x IN s1 /\ ~(x IN j)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN frontier c' INTER B`;
      `frontier c' INTER B = (s1 INTER frontier c INTER B) DIFF (j:real^3->bool)`;
      `frontier c SUBSET (c:real^3->bool)`; `d INTER frontier c = (j:real^3->bool)`;
      `W INTER c INTER B SUBSET (d:real^3->bool)`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNION THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    MAP_EVERY UNDISCH_TAC [`~((x:real^3) IN W)`; `(x:real^3) IN s1`; `~((x:real^3) IN j)`;
                           `(Z:real^3->bool) SUBSET W`; `s1 INTER s2 = (j:real^3->bool)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`frontier c' DIFF Z = (s1:real^3->bool) DIFF Z`;
                           `s1 UNION s2 = frontier (c:real^3->bool)`] THEN
    SET_TAC[]]);;

let MOI_S4N_COMPONENTS_SIDE = prove
 (`!t s1 s2 j:real^3->bool.
     j IN components t /\ t SUBSET s1 UNION s2 /\ closed s1 /\ closed s2 /\
     s1 INTER s2 SUBSET j
     ==> components ((s1 INTER t) DIFF j) SUBSET components t DELETE j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DELETE] THEN
  X_GEN_TAC `k':real^3->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k':real^3->bool = {}) /\ k' SUBSET (s1 INTER t) DIFF j /\ connected k'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `k':real^3->bool`] EXISTS_COMPONENT_SUPERSET) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`~(k':real^3->bool = {})`;
                           `(k':real^3->bool) SUBSET (s1 INTER t) DIFF j`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `~(k:real^3->bool = j)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(k':real^3->bool = {})`; `(k':real^3->bool) SUBSET k`;
                           `(k':real^3->bool) SUBSET (s1 INTER t) DIFF j`;
                           `k:real^3->bool = j`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k INTER j = {}:real^3->bool` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET t /\ connected k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET s1` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (k:real^3->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`s1:real^3->bool`; `s2:real^3->bool`]) THEN
    REWRITE_TAC[ASSUME `closed (s1:real^3->bool)`; ASSUME `closed (s2:real^3->bool)`] THEN
    MAP_EVERY UNDISCH_TAC [`(k:real^3->bool) SUBSET t`; `(t:real^3->bool) SUBSET s1 UNION s2`;
                           `s1 INTER s2 SUBSET (j:real^3->bool)`;
                           `k INTER j = {}:real^3->bool`; `~(k':real^3->bool = {})`;
                           `(k':real^3->bool) SUBSET k`;
                           `(k':real^3->bool) SUBSET (s1 INTER t) DIFF j`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k:real^3->bool = k'` (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `(s1 INTER t) DIFF j:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC [`(k:real^3->bool) SUBSET t`; `(k:real^3->bool) SUBSET s1`;
                             `k INTER j = {}:real^3->bool`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`~(k':real^3->bool = {})`; `(k':real^3->bool) SUBSET k`] THEN
      SET_TAC[]];
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S4N_RIM_COMPONENT = prove
 (`!t j W:real^3->bool.
     compact j /\ connected j /\ ~(j = {}) /\ open W /\ j SUBSET t /\ t INTER W = j
     ==> j IN components t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (e:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `j:real^3->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `j = e INTER (W:real^3->bool)` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(j:real^3->bool) SUBSET e`; `(e:real^3->bool) SUBSET t`;
                               `t INTER W = (j:real^3->bool)`] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ASM_MESON_TAC[]]);;

(* h(Bd s) is compact, connected and off the tube boundary. *)

let MOI_S4N_KFACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep f1 car s.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ s IN moi_s34_simp kk (&2)
     ==> compact (IMAGE h (relative_frontier s)) /\
         connected (IMAGE h (relative_frontier s)) /\
         IMAGE h (relative_frontier s) INTER IMAGE f1 (moi_s34_bd tt kk) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^N->bool) /\ convex s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_S4L_TRI_FORM) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS tt /\ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S4L_TUBE_TUBE
      (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on relative_frontier s` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
      SIMP_TAC[moi_s34_emb];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      REWRITE_TAC[relative_frontier] THEN
      SUBGOAL_THEN `closure s = (s:real^N->bool)` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        FIRST_ASSUM ACCEPT_TAC;
        SET_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME `aff_dim (s:real^N->bool) = &2`] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
                interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET
                interior (IMAGE f1 (moi_s34_nb tt kk))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(MATCH_MP MOI_S4L_GRAPH_TUBE
      (ASSUME `moi_s34_tube tt (kk:(real^N->bool)->bool)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[moi_s34_ft] THEN DISCH_TAC THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_FRAME_F1
    (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
     interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`;
    `interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET
     interior (IMAGE f1 (moi_s34_nb tt kk))`] THEN
  SET_TAC[]);;

(* The compressed ball for Operation 1 (inside case), with the facts used   *)
(* for the invariants and the rank.                                         *)

let MOI_S4N_NEW_BALL = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v d j.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     moi_s34_op1w tt kk f1 cb s v d j /\ d DIFF j SUBSET interior (cb s)
     ==> ?c'. pl_ball 3 c' /\ c' SUBSET cb s /\
              IMAGE h (relative_frontier s) SUBSET interior c' /\
              frontier c' SUBSET car s /\
              moi_s34_trace tt kk f1 c' = moi_s34_trace tt kk f1 (cb s) INTER c' /\
              (!x. x IN moi_s34_trace tt kk f1 c'
                   ==> ?u. open u /\ x IN u /\
                           frontier c' INTER u = frontier (cb s) INTER u) /\
              components (moi_s34_trace tt kk f1 c') SUBSET
              components (moi_s34_trace tt kk f1 (cb s)) DELETE j /\
              j IN components (moi_s34_trace tt kk f1 (cb s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S4N_W_CHOICE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`] MOI_S4N_KFACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fb1") STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_s34_op1w tt kk (f1:real^N->real^3) cb s v d j` THEN
  REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN
  ABBREV_TAC `c = (cb:(real^N->bool)->real^3->bool) s` THEN
  ABBREV_TAC `B = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `K = IMAGE (h:real^N->real^3) (relative_frontier s)` THEN
  SUBGOAL_THEN `pl_ball 3 (c:real^3->bool) /\ K SUBSET interior c /\
                frontier c SUBSET (car:(real^N->bool)->real^3->bool) s`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "fb1" (MP_TAC o REWRITE_RULE[moi_s34_fb1]) THEN
    REWRITE_TAC[ASSUME `(cb:(real^N->bool)->real^3->bool) s = c`;
                ASSUME `IMAGE (h:real^N->real^3) (relative_frontier s) = K`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL2_TOPO
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4L_PL_CELL_FACTS
    (ASSUME `pl_cell_with_boundary 2 (d:real^3->bool) j`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET B` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^3->bool) SUBSET
                 IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    EXPAND_TAC "B" THEN MP_TAC(ISPECL [`f1:real^N->real^3`;
      `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`; `moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the compression *)
  MP_TAC(ISPECL [`c:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`; `K:real^3->bool`;
                 `W:real^3->bool`] MOI_S4N_COMPRESS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`K INTER B = {}:real^3->bool`; `(d:real^3->bool) SUBSET B`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` (X_CHOOSE_THEN `s1:real^3->bool`
    (X_CHOOSE_THEN `s2:real^3->bool` (X_CHOOSE_THEN `Z:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  (* the new trace *)
  MP_TAC(ISPECL [`c:real^3->bool`; `c':real^3->bool`; `B:real^3->bool`; `d:real^3->bool`;
                 `j:real^3->bool`; `s1:real^3->bool`; `s2:real^3->bool`; `W:real^3->bool`;
                 `Z:real^3->bool`] MOI_S4N_NEW_TRACE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) c = frontier c INTER B /\
                moi_s34_trace tt kk (f1:real^N->real^3) c' = frontier c' INTER B`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_trace] THEN EXPAND_TAC "B" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `j IN components (moi_s34_trace tt kk (f1:real^N->real^3) c)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_RIM_COMPONENT THEN EXISTS_TAC `W:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(j:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET B`;
                           `d INTER frontier c = (j:real^3->bool)`;
                           `(d:real^3->bool) SUBSET W`;
                           `W INTER c INTER B SUBSET (d:real^3->bool)`;
                           `frontier c SUBSET (c:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_TRACE_AT_V THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                          `h:real^N->real^3`; `f1:real^N->real^3`;
                          `car:(real^N->bool)->real^3->bool`; `c:real^3->bool`;
                          `j:real^3->bool`] THEN
    REWRITE_TAC[ASSUME `{v:real^N} IN kk`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "fb1" MP_TAC THEN
      REWRITE_TAC[ASSUME `(cb:(real^N->bool)->real^3->bool) s = c`];
      MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(j:real^3->bool) SUBSET d`;
        `(d:real^3->bool) SUBSET
         IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
      MP_TAC(ISPECL [`f1:real^N->real^3`;
        `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`; `moi_s34_vb tt kk (v:real^N)`]
        IMAGE_SUBSET) THEN
      REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(car:(real^N->bool)->real^3->bool) {v} SUBSET car s` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o CONJUNCT1 o
               funpow 5 CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[ASSUME `{v:real^N} IN kk`; NOT_INSERT_EMPTY; SING_SUBSET;
                ASSUME `(v:real^N) IN s`] THEN
    UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `c':real^3->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* frontier in the carrier *)
    MAP_EVERY UNDISCH_TAC
     [`frontier c' SUBSET (s1 DIFF j) UNION ((W:real^3->bool) INTER (c DIFF d))`;
      `s1 UNION s2 = frontier (c:real^3->bool)`;
      `frontier c SUBSET (car:(real^N->bool)->real^3->bool) s`;
      `(W:real^3->bool) SUBSET (car:(real^N->bool)->real^3->bool) {v}`;
      `(car:(real^N->bool)->real^3->bool) {v} SUBSET car s`] THEN
    SET_TAC[];
    (* the trace equation *)
    REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c' = frontier c' INTER B`;
                ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c = frontier c INTER B`] THEN
    MP_TAC(MATCH_MP FRONTIER_SUBSET_CLOSED (MATCH_MP COMPACT_IMP_CLOSED
      (CONJUNCT1(MATCH_MP MOI_S4L_PL_BALL_COMPACT
        (ASSUME `pl_ball 3 (c':real^3->bool)`))))) THEN
    MAP_EVERY UNDISCH_TAC
     [`frontier c' INTER B = (s1 INTER frontier c INTER B) DIFF (j:real^3->bool)`;
      `c' INTER frontier c SUBSET (s1:real^3->bool) DIFF j`] THEN
    SET_TAC[];
    (* locality *)
    REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c' = frontier c' INTER B`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    (* components *)
    REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c' = frontier c' INTER B`;
                ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c = frontier c INTER B`;
                ASSUME `frontier c' INTER B =
                        (s1 INTER frontier c INTER B) DIFF (j:real^3->bool)`] THEN
    MATCH_MP_TAC MOI_S4N_COMPONENTS_SIDE THEN EXISTS_TAC `s2:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `j IN components (moi_s34_trace tt kk (f1:real^N->real^3) c)` THEN
      REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3) c = frontier c INTER B`];
      UNDISCH_TAC `s1 UNION s2 = frontier (c:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `s1 INTER s2 = (j:real^3->bool)` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The invariants and the rank for the new face ball, and Operation 1       *)
(* (inside case) from the H_1 step MOI_S4N_H1_KEEP, the antecedent of       *)
(* OP1_IN_FROM_H1 (MOI_S4N_H1_KEEP_THM below, from the torus unit).         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_FB1_TRANSFER = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car s c c'.
     moi_s34_fb1 tt kk h f1 car s c /\ pl_ball 3 c' /\ c' SUBSET c /\
     IMAGE h (relative_frontier s) SUBSET interior c' /\ frontier c' SUBSET car s /\
     moi_s34_trace tt kk f1 c' SUBSET moi_s34_trace tt kk f1 c /\
     components (moi_s34_trace tt kk f1 c') SUBSET components (moi_s34_trace tt kk f1 c) /\
     (!x. x IN moi_s34_trace tt kk f1 c'
          ==> ?u. open u /\ x IN u /\ frontier c' INTER u = frontier c INTER u) /\
     carries_h1 (moi_s34_trace tt kk f1 c' INTER IMAGE f1 (moi_s34_ft tt kk s))
                (IMAGE f1 (moi_s34_ft tt kk s))
     ==> moi_s34_fb1 tt kk h f1 car s c'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!g. g IN moi_s34_simp kk (&1)
                    ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                        SUBSET IMAGE f1 (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_rims tt kk (f1:real^N->real^3) SUBSET IMAGE f1 (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_rims; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* vertex balls avoided *)
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c':real^3->bool) SUBSET c` THEN SET_TAC[];
    (* crossings at trace points *)
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open")) (concl th) &&
      is_forall (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`frontier c:real^3->bool`;
                          `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
                          `u:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_crossing_at"))
          (concl th))) THEN
      UNDISCH_TAC `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c'` THEN
      UNDISCH_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c' SUBSET
                   moi_s34_trace tt kk f1 c` THEN
      SET_TAC[];
      UNDISCH_TAC `frontier c' INTER u = frontier c INTER (u:real^3->bool)` THEN
      SET_TAC[];
      REWRITE_TAC[]];
    (* crossings with the rims *)
    MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c' /\
                  x IN moi_s34_trace tt kk f1 c`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(MP (SPEC `g:real^N->bool` (ASSUME
        `!g. g IN moi_s34_simp kk (&1)
             ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                 SUBSET IMAGE f1 (moi_s34_bd tt kk)`))
        (ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`)) THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier c' INTER
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
        `moi_s34_trace tt kk (f1:real^N->real^3) c' SUBSET moi_s34_trace tt kk f1 c`] THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `x:real^3` (ASSUME
      `!x. x IN moi_s34_trace tt kk (f1:real^N->real^3) c'
           ==> ?u. open u /\ x IN u /\ frontier c' INTER u = frontier c INTER u`))
      (ASSUME `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c'`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`moi_s34_trace tt kk (f1:real^N->real^3) c`;
                          `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER u`] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`g:real^N->bool`; `x:real^3`] (ASSUME
        `!g x. g IN moi_s34_simp kk (&1) /\
               x IN frontier c INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
               ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                     (moi_s34_trace tt kk f1 c)
                     (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[ASSUME `(g:real^N->bool) IN moi_s34_simp kk (&1)`] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN frontier c' INTER
         IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
        `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c`] THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN moi_s34_trace tt kk (f1:real^N->real^3) c'` THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[];
      REWRITE_TAC[moi_s34_trace] THEN
      UNDISCH_TAC `frontier c' INTER u = frontier c INTER (u:real^3->bool)` THEN
      SET_TAC[]];
    (* finitely many components *)
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3) c)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* finitely many rim crossings *)
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `frontier c INTER moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s34_rims tt kk (f1:real^N->real^3) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
      `moi_s34_trace tt kk (f1:real^N->real^3) c' SUBSET moi_s34_trace tt kk f1 c`] THEN
    REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]]);;

let MOI_S4N_RANK_DROP = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) c c' j.
     FINITE (components (moi_s34_trace tt kk f1 c)) /\
     FINITE (frontier c INTER moi_s34_rims tt kk f1) /\
     components (moi_s34_trace tt kk f1 c') SUBSET
     components (moi_s34_trace tt kk f1 c) DELETE j /\
     j IN components (moi_s34_trace tt kk f1 c) /\
     moi_s34_trace tt kk f1 c' SUBSET moi_s34_trace tt kk f1 c
     ==> moi_s34_rank tt kk f1 c' < moi_s34_rank tt kk f1 c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_rank] THEN
  MATCH_MP_TAC(ARITH_RULE `m1 < n1 /\ m2 <= n2 ==> m1 + m2 < n1 + n2:num`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
       [UNDISCH_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3) c') SUBSET
                     components (moi_s34_trace tt kk f1 c) DELETE j` THEN SET_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3) c') SUBSET
                     components (moi_s34_trace tt kk f1 c) DELETE j` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `j IN components (moi_s34_trace tt kk (f1:real^N->real^3) c)` THEN
        SET_TAC[]];
      FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBGOAL_THEN `moi_s34_rims tt kk (f1:real^N->real^3) SUBSET IMAGE f1 (moi_s34_bd tt kk)`
    MP_TAC THENL
     [REWRITE_TAC[moi_s34_rims; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c' SUBSET moi_s34_trace tt kk f1 c` THEN
    REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]]);;

let MOI_S4N_FBINV_UPDATE = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car cb s c'.
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     moi_s34_fb1 tt kk h f1 car s c' /\ c' SUBSET cb s
     ==> moi_s34_fbinv tt kk h f1 car (\s'. if s' = s then c' else cb s')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_fbinv; moi_s34_fb2] THEN BETA_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2"))
    STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s'':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s'':real^N->bool = s` THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN USE_THEN "inv1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MAP_EVERY X_GEN_TAC [`s1':real^N->bool`; `s2':real^N->bool`] THEN STRIP_TAC THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `s1':real^N->bool = s` THEN ASM_CASES_TAC `s2':real^N->bool = s` THENL
     [UNDISCH_TAC `~(s1':real^N->bool = s2')` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inv2" (MP_TAC o SPECL [`s:real^N->bool`; `s2':real^N->bool`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `~(s2':real^N->bool = s)` THEN MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(c':real^3->bool) SUBSET cb (s:real^N->bool)` THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inv2" (MP_TAC o SPECL [`s1':real^N->bool`; `s:real^N->bool`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(c':real^3->bool) SUBSET cb (s:real^N->bool)` THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inv2" (MP_TAC o SPECL [`s1':real^N->bool`; `s2':real^N->bool`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]]]);;

(* The H_1 step: a PL ball c' inside the face ball cb s, around h(Bd s),   *)
(* whose trace is the old trace inside c' and whose frontier agrees with   *)
(* the old frontier near its trace, still carries H_1 of the face torus.   *)
(* Proved below as MOI_S4N_H1_KEEP_THM with pc_moi_s34_torus               *)
(* (Mayer-Vietoris for the ball c' and the subsurface lemma for the torus  *)
(* frontier).                                                              *)

let MOI_S4N_H1_KEEP =
 `!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3) car
   (cb:(real^N->bool)->real^3->bool) s c'.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     pl_ball 3 c' /\ c' SUBSET cb s /\
     IMAGE h (relative_frontier s) SUBSET interior c' /\ frontier c' SUBSET car s /\
     moi_s34_trace tt kk f1 c' = moi_s34_trace tt kk f1 (cb s) INTER c' /\
     (!x. x IN moi_s34_trace tt kk f1 c'
          ==> ?u. open u /\ x IN u /\ frontier c' INTER u = frontier (cb s) INTER u) /\
     components (moi_s34_trace tt kk f1 c') SUBSET
     components (moi_s34_trace tt kk f1 (cb s))
     ==> carries_h1 (moi_s34_trace tt kk f1 c' INTER IMAGE f1 (moi_s34_ft tt kk s))
                    (IMAGE f1 (moi_s34_ft tt kk s))`;;

let MOI_S4N_OP1_FROM_H1 = prove
 (mk_imp(MOI_S4N_H1_KEEP,MOI_S34_OP1_IN),
  DISCH_THEN(LABEL_TAC "h1") THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`;
                       `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                       `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `d:real^3->bool`; `j:real^3->bool`]
    MOI_S4N_NEW_BALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk (h:real^N->real^3) f1 car s (cb s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_trace tt kk (f1:real^N->real^3) c' SUBSET
                moi_s34_trace tt kk f1 (cb (s:real^N->bool)) /\
                components (moi_s34_trace tt kk (f1:real^N->real^3) c') SUBSET
                components (moi_s34_trace tt kk f1 (cb (s:real^N->bool)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c' =
                   moi_s34_trace tt kk f1 (cb (s:real^N->bool)) INTER c'` THEN SET_TAC[];
      UNDISCH_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3) c') SUBSET
                   components (moi_s34_trace tt kk f1 (cb (s:real^N->bool))) DELETE j` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 (moi_s34_trace tt kk (f1:real^N->real^3) c' INTER
                            IMAGE f1 (moi_s34_ft tt kk s))
                           (IMAGE f1 (moi_s34_ft tt kk (s:real^N->bool)))` ASSUME_TAC THENL
   [USE_THEN "h1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`;
                          `cb:(real^N->bool)->real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk (h:real^N->real^3) f1 car s c'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_FB1_TRANSFER THEN
    EXISTS_TAC `(cb:(real^N->bool)->real^3->bool) s` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\s':real^N->bool. if s' = s then c' else (cb:(real^N->bool)->real^3->bool) s'` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4N_FBINV_UPDATE THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4N_RANK_DROP THEN
    EXISTS_TAC `j:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `moi_s34_fb1 tt kk (h:real^N->real^3) f1 car s (cb s)` THEN
    SIMP_TAC[moi_s34_fb1]]);;

(* ------------------------------------------------------------------------- *)
(* First half of the H_1 step: a PL ball c' inside the face ball, with      *)
(* h(Bd s) in its interior, meets the face torus T in a set whose part on  *)
(* the tube boundary carries H_1(T) (Mayer-Vietoris on the ball c' and the *)
(* push MOI_S4J_MV_PUSH of pc_moi_s34_h1, as in Step B of LEMMA4).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_BALL_CONTRACTIBLE = prove
 (`!c:real^3->bool. pl_ball 3 c ==> contractible c`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:M`] HOMEOMORPHIC_CONTRACTIBLE) THEN
  EXISTS_TAC `k:real^3->bool` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN MATCH_MP_TAC POLYTOPE_IMP_CONVEX THEN
    MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&3:int` THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* At a point of a carrier outside the vertex balls of the vertices not in  *)
(* s there is an open set around it missing all those vertex balls.        *)

let MOI_S4N_POINT_AVOID = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep f1 car s y.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     y IN UNIONS {car q | q | q IN kk /\ ~(q = {})} /\
     (!v. {v} IN kk /\ ~(v IN s) ==> ~(y IN IMAGE f1 (moi_s34_vb tt kk v)))
     ==> ?w. open w /\ y IN w /\
             !v. {v} IN kk /\ ~(v IN s) ==> DISJOINT w (IMAGE f1 (moi_s34_vb tt kk v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{y:real^3}`; `{v:real^N | {v} IN kk /\ ~(v IN s)}`;
                 `\v:real^N. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`]
    MOI_S4Q_AVOID) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING; FORALL_UNWIND_THM2; SING_SUBSET] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[]];
      MP_TAC(ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`) THEN
      REWRITE_TAC[moi_s34_frame] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT1 o funpow 11 CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (CHOICE:(real^N->bool)->real^N)
                    {q | q IN kk /\ ~(q = {}) /\
                         ~((car:(real^N->bool)->real^3->bool) q INTER u = {})}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN
      STRIP_TAC THEN EXISTS_TAC `{v:real^N}` THEN
      REWRITE_TAC[MOI_S4L_CHOICE_SING; NOT_INSERT_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER u = {})` THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v:real^N}` THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
      can (find_term ((=) `w:real^3->bool`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4N_W_CARRIES = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3) car
    (cb:(real^N->bool)->real^3->bool) s c'.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     pl_ball 3 c' /\ c' SUBSET cb s /\ IMAGE h (relative_frontier s) SUBSET interior c'
     ==> carries_h1 (c' INTER IMAGE f1 (moi_s34_ft tt kk s) INTER
                     IMAGE f1 (moi_s34_bd tt kk))
                    (IMAGE f1 (moi_s34_ft tt kk s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4J_SIMP2) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4J_T_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "avoid")))) THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
    interior (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) /\
    loops_carried (IMAGE h (relative_frontier s)) (IMAGE f1 (moi_s34_ft tt kk s))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. {v} IN kk /\ ~(v IN s)
                    ==> DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                                 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    REWRITE_TAC[ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tor = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  ABBREV_TAC `rr = IMAGE (h:real^N->real^3) (relative_frontier s)` THEN
  ABBREV_TAC `B = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `(rr:real^3->bool) SUBSET tor` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tor:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(rr:real^3->bool) SUBSET interior tor` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 rr (tor:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOOPS_CARRIED_IMP_CARRIES_H1 THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC MOI_S4J_LOOPS_PATH_CONNECTED THEN EXISTS_TAC `rr:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    EXPAND_TAC "rr" THEN MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
      SIMP_TAC[moi_s34_emb];
      UNDISCH_TAC `relative_frontier (s:real^N->bool) SUBSET s` THEN
      UNDISCH_TAC `(s:real^N->bool) IN kk` THEN
      UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S4J_BALL3_FACTS (ASSUME `pl_ball 3 (c':real^3->bool)`)) THEN
  STRIP_TAC THEN
  (* the points of c' on the frontier of the torus lie on the tube boundary *)
  SUBGOAL_THEN `c' INTER (tor DIFF interior tor) SUBSET (B:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `y:real^3`]
      MOI_S4N_POINT_AVOID) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [UNDISCH_TAC `(y:real^3) IN tor` THEN EXPAND_TAC "tor" THEN
        REWRITE_TAC[moi_s34_ft; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
            (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
        EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN CONJ_TAC THENL
         [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v:real^N}` THEN
        UNDISCH_TAC `(x:real^N) IN t` THEN UNDISCH_TAC `t = moi_s34_vb tt kk (v:real^N)` THEN
        UNDISCH_TAC `(y:real^3) = f1 (x:real^N)` THEN SET_TAC[];
        X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
          can (find_term ((=) `cb:(real^N->bool)->real^3->bool`)) (concl th) &&
          can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`(y:real^3) IN c'`;
                               `(c':real^3->bool) SUBSET cb (s:real^N->bool)`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "avoid" (MP_TAC o SPEC `w:real^3->bool`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) = tor`;
                ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) = B`] THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^3) IN w`; `(y:real^3) IN tor`;
                           `~((y:real^3) IN interior tor)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the pair retraction and the push *)
  MP_TAC(ISPECL [`c' INTER tor:real^3->bool`; `c' INTER tor INTER B:real^3->bool`]
    MOI_S4J_PAIR_RETRACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_INTER THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_POLYHEDRON_INTER THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_S4J_MV_PUSH THEN
  MAP_EVERY EXISTS_TAC [`c':real^3->bool`; `c' INTER interior tor:real^3->bool`;
                        `tor:real^3->bool`; `u:real^3->bool`; `rr:real^3->bool`;
                        `c' INTER tor:real^3->bool`; `g:real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR];
    MP_TAC(ISPEC `tor:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`c' INTER (tor DIFF interior tor) SUBSET (B:real^3->bool)`;
                           `c' INTER tor INTER B SUBSET (u:real^3->bool)`] THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S4J_H1_CONTRACTIBLE THEN MATCH_MP_TAC MOI_S4N_BALL_CONTRACTIBLE THEN
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`(rr:real^3->bool) SUBSET interior c'`;
                           `(rr:real^3->bool) SUBSET interior tor`] THEN
    MP_TAC(ISPEC `c':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    MP_TAC(ISPEC `tor:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    SET_TAC[];
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bridge facts for the H_1 step: a PL ball shrinks to a PL ball inside     *)
(* its interior around a compact set, and a ball inside the face ball meets *)
(* the face torus boundary only on the tube boundary.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_SHRINK_BALL = prove
 (`!c (K:real^3->bool).
     pl_ball 3 c /\ compact K /\ K SUBSET interior c
     ==> ?c''. pl_ball 3 c'' /\ K SUBSET interior c'' /\ c'' SUBSET interior c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_ball 3 (c:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `gg:real^3->real^3`
    (X_CHOOSE_THEN `ff:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(MATCH_MP MOI_S4N_SIMPLEX3_FACTS (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3->bool`; `gg:real^3->real^3`;
                 `ff:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `homeomorphism (k,c) (gg:real^3->real^3,ff)` MP_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (k,c) (gg:real^3->real^3,ff)`) THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  (* an interior point z0 of k and a bound B *)
  SUBGOAL_THEN `?z0:real^3. z0 IN interior k` (X_CHOOSE_TAC `z0:real^3`) THENL
   [UNDISCH_TAC `~(interior (k:real^3->bool) = {})` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN interior k` THEN
    UNDISCH_TAC `interior (k:real^3->bool) SUBSET k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\ !y:real^3. y IN k ==> norm y <= B`
  (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `compact (k:real^3->bool)` THEN
    MESON_TAC[BOUNDED_POS; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  (* the image of K under ff is compact inside interior k *)
  SUBGOAL_THEN `compact (IMAGE (ff:real^3->real^3) K) /\ IMAGE ff K SUBSET interior k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `c:real^3->bool` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(K:real^3->bool) SUBSET interior c` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(K:real^3->bool) SUBSET interior c`;
        `interior c = IMAGE (gg:real^3->real^3) (interior k)`;
        `interior (k:real^3->bool) SUBSET k`;
        `!x. x IN k ==> (ff:real^3->real^3) (gg x) = x`] THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (ff:real^3->real^3) K`; `(:real^3) DIFF interior k`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (ff:real^3->real^3) K SUBSET interior k` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `del = min (&1 / &2) ((e2 / &2) / (&4 * B))` THEN
  SUBGOAL_THEN `&0 < del /\ del <= &1 / &2 /\ del * (&4 * B) <= e2 / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e2 / &2 /\ &0 < &4 * B` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < e2`; `&0 < B`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (e2 / &2) / (&4 * B)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `del <= (e2 / &2) / (&4 * B) /\ &0 < del /\ del <= &1 / &2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "del" THEN UNDISCH_TAC `&0 < (e2 / &2) / (&4 * B)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `del <= (e2 / &2) / (&4 * B)` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `lam = &1 - del` THEN
  SUBGOAL_THEN `&0 < lam /\ lam < &1 /\ &1 / &2 <= lam /\ &1 - lam = del`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN MAP_EVERY UNDISCH_TAC [`&0 < del`; `del <= &1 / &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the smaller simplex kl about z0 *)
  MP_TAC(ISPECL [`\x:real^3. lam % x`; `(&1 - lam) % (z0:real^3)`; `&3:int`;
                 `k:real^3->bool`] MOI_S27_INJ_AFFINE_SIMPLEX) THEN
  REWRITE_TAC[LINEAR_SCALING] THEN BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBGOAL_THEN `~(lam = &0)` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LCANCEL]) THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kl = IMAGE (\y. lam % y + (&1 - lam) % z0) (k:real^3->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `(kl:real^3->bool) SUBSET interior k` ASSUME_TAC THENL
   [EXPAND_TAC "kl" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `lam % y + (&1 - lam) % z0 = y - (&1 - lam) % (y - z0:real^3)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_INTERIOR_CONVEX_SHRINK THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`&0 < lam`; `lam < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interior kl = IMAGE (\y. lam % y + (&1 - lam) % z0) (interior k:real^3->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "kl" THEN
    SUBGOAL_THEN `!s. IMAGE (\y. lam % y + (&1 - lam) % (z0:real^3)) s =
                      IMAGE (\y:real^3. (&1 - lam) % z0 + y) (IMAGE (\y. lam % y) s)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN BETA_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INTERIOR_TRANSLATION] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
    REWRITE_TAC[LINEAR_SCALING] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `~(lam = &0)` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LCANCEL]) THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the new ball *)
  SUBGOAL_THEN `pl_homeomorphism (kl,IMAGE (gg:real^3->real^3) kl) (gg,ff)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4N_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `c:real^3->bool`] THEN
    SUBGOAL_THEN `pl_polyhedron (kl:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&3:int` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(kl:real^3->bool) SUBSET interior k` THEN SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ASSUME `pl_homeomorphism (k,c) (gg:real^3->real^3,ff)`) THEN
        SIMP_TAC[pl_homeomorphism];
        MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(kl:real^3->bool) SUBSET interior k` THEN SET_TAC[];
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `c'' = IMAGE (gg:real^3->real^3) kl` THEN
  MP_TAC(ISPECL [`kl:real^3->bool`; `c'':real^3->bool`; `gg:real^3->real^3`;
                 `ff:real^3->real^3`] MOI_S4N_BALL_INTERIOR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  EXISTS_TAC `c'':real^3->bool` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`kl:real^3->bool`; `gg:real^3->real^3`; `ff:real^3->real^3`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* K inside the new interior *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z0':real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^3->real^3) z0' IN interior k` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (ff:real^3->real^3) K SUBSET interior k` THEN
      UNDISCH_TAC `(z0':real^3) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gg:real^3->real^3) (ff z0') = z0'` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        concl th = `!y. y IN c ==> (gg:real^3->real^3) (ff y) = y`)) THEN
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(K:real^3->bool) SUBSET interior c` THEN
      UNDISCH_TAC `(z0':real^3) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `z0:real^3`; `(ff:real^3->real^3) z0'`; `lam:real`;
                   `e2:real`; `B:real`] MOI_S4N_RATIO_INTERIOR) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(ff:real^3->real^3) z0' IN interior k` THEN
        UNDISCH_TAC `interior (k:real^3->bool) SUBSET k` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `e2:real`)) (concl th) && is_forall (concl th))) THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
         [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z0':real^3` THEN
          CONJ_TAC THENL [REFL_TAC; FIRST_ASSUM ACCEPT_TAC];
          FIRST_ASSUM ACCEPT_TAC];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[ASSUME `&1 - lam = del`] THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `z' = z0 + inv lam % ((ff:real^3->real^3) z0' - z0)` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(ff:real^3->real^3) z0' IN interior kl` ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `interior kl =
        IMAGE (\y. lam % y + (&1 - lam) % z0) (interior (k:real^3->bool))`] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z':real^3` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(gg:real^3->real^3) (ff z0') = z0'`;
                           `(ff:real^3->real^3) z0' IN interior kl`;
                           `interior c'' = IMAGE (gg:real^3->real^3) (interior kl)`] THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    (* c'' inside interior c *)
    MAP_EVERY UNDISCH_TAC [`IMAGE (gg:real^3->real^3) kl = c''`;
                           `(kl:real^3->bool) SUBSET interior k`;
                           `interior c = IMAGE (gg:real^3->real^3) (interior k)`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The H_1 step MOI_S4N_H1_KEEP via the torus unit (pc_moi_s34_torus):      *)
(* the trace of the old face ball lies on the boundary torus Theta of the   *)
(* face torus T; T1 gives a carrying trace circle C; if C meets the new     *)
(* ball it is a trace circle of the new ball; otherwise the new ball, shrunk*)
(* (MOI_S4N_SHRINK_BALL) and fed to MOI_S4N_W_CARRIES, gives a carrying     *)
(* open piece of Theta inside the new ball, and SEP (Mayer-Vietoris on      *)
(* Theta) with a retracting neighbourhood of Theta INTER frontier c'        *)
(* (MOI_S4J_PAIR_RETRACT) shows that the new trace carries.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4N_CARRIES_EMPTY = prove
 (`!s:real^N->bool.
     carries_h1 {} s ==> trivial_group (homology_group(&1,subtopology euclidean s))`,
  GEN_TAC THEN REWRITE_TAC[carries_h1; group_image] THEN
  SUBGOAL_THEN `trivial_group (homology_group(&1,subtopology euclidean ({}:real^N->bool)))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_S4J_H1_CONTRACTIBLE THEN REWRITE_TAC[CONTRACTIBLE_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[trivial_group] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;

(* The face torus: a PL solid torus whose frontier is a polyhedral torus   *)
(* surface containing its points on the tube boundary.                     *)

let MOI_S4N_FACE_TORUS_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep f1 car s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ s IN moi_s34_simp kk (&2)
     ==> pl_solid_torus (IMAGE f1 (moi_s34_ft tt kk s)) /\
         compact (IMAGE f1 (moi_s34_ft tt kk s)) /\
         torus_surface (frontier (IMAGE f1 (moi_s34_ft tt kk s))) /\
         frontier (IMAGE f1 (moi_s34_ft tt kk s)) SUBSET IMAGE f1 (moi_s34_ft tt kk s) /\
         pl_polyhedron (frontier (IMAGE f1 (moi_s34_ft tt kk s))) /\
         ~trivial_group (homology_group(&1,subtopology euclidean
                                           (IMAGE f1 (moi_s34_ft tt kk s)))) /\
         IMAGE f1 (moi_s34_ft tt kk s) INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET
         frontier (IMAGE f1 (moi_s34_ft tt kk s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_solid_torus (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4U_PL_SOLID_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s34_ft tt kk (s:real^N->bool) SUBSET moi_s34_nb tt kk` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_ft; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
      MOI_S4L_GRAPH_TUBE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_FRAME_F1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)`] SUBSET_INTERIOR) THEN
  ANTS_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
               interior (IMAGE f1 (moi_s34_nb tt kk)) = {}` THEN
  SET_TAC[]);;
(* A set inside the face ball meets the tube boundary only on the frontier *)
(* of the face torus, and meets that frontier only on the tube boundary.   *)

let MOI_S4N_BALL_FACE_TORUS = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep f1 car cb s c.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\ c SUBSET cb s
     ==> c INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET
         frontier (IMAGE f1 (moi_s34_ft tt kk s)) /\
         c INTER frontier (IMAGE f1 (moi_s34_ft tt kk s)) SUBSET
         IMAGE f1 (moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4N_FACE_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4J_T_FACTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "avoid")))) THEN
  SUBGOAL_THEN `!v. {v} IN kk /\ ~(v IN s)
                    ==> DISJOINT ((cb:(real^N->bool)->real^3->bool) s)
                                 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk (h:real^N->real^3) f1 car cb` THEN
    REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    REWRITE_TAC[ASSUME `(s:real^N->bool) IN moi_s34_simp kk (&2)`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* points of c on a vertex ball lie on a vertex ball of s *)
  SUBGOAL_THEN
   `!y v. y IN c /\ {v} IN kk /\ y IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)
          ==> y IN IMAGE f1 (moi_s34_ft tt kk s) /\ v IN s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
        can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(y:real^3) IN c`; `(c:real^3->bool) SUBSET cb (s:real^N->bool)`;
                             `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
    REWRITE_TAC[moi_s34_ft; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `moi_s34_vb tt kk (v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fun th ->
        UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^N`] o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_ft"))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) INTER
                  IMAGE f1 (moi_s34_bd tt kk) SUBSET
                  frontier (IMAGE f1 (moi_s34_ft tt kk s))`)) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  (* points of c on the frontier of the face torus are on the tube boundary *)
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) /\
                ~(y IN interior (IMAGE f1 (moi_s34_ft tt kk s)))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))` THEN
    UNDISCH_TAC `frontier (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) SUBSET
                 IMAGE f1 (moi_s34_ft tt kk s)` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `y:real^3`]
    MOI_S4N_POINT_AVOID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
      REWRITE_TAC[moi_s34_ft; IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
      EXISTS_TAC `(car:(real^N->bool)->real^3->bool) {v}` THEN CONJ_TAC THENL
       [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET car {v:real^N}` THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN UNDISCH_TAC `t = moi_s34_vb tt kk (v:real^N)` THEN
      UNDISCH_TAC `(y:real^3) = f1 (x:real^N)` THEN SET_TAC[];
      X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
        can (find_term ((=) `cb:(real^N->bool)->real^3->bool`)) (concl th) &&
        can (find_term ((=) `DISJOINT:(real^3->bool)->(real^3->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(y:real^3) IN c`;
                             `(c:real^3->bool) SUBSET cb (s:real^N->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "avoid" (MP_TAC o SPEC `w:real^3->bool`) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`(y:real^3) IN w`;
                         `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)`;
                         `~((y:real^3) IN interior (IMAGE (f1:real^N->real^3)
                                                      (moi_s34_ft tt kk s)))`] THEN
  SET_TAC[]);;
(* A component of the old trace meeting the new ball is a component of the *)
(* new trace.                                                               *)

let MOI_S4N_COMPONENT_KEPT = prove
 (`!(z:real^3->bool) z' c' k.
     z' = z INTER c' /\ components z' SUBSET components z /\
     k IN components z /\ ~(k INTER c' = {})
     ==> k SUBSET z'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN z'` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `z':real^3->bool = z INTER c'`; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z:real^3->bool`; `k:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component z' (x:real^3) IN components z` ASSUME_TAC THENL
   [UNDISCH_TAC `components (z':real^3->bool) SUBSET components z` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component z' (x:real^3) = k` (SUBST1_TAC o SYM) THENL
   [MP_TAC(ISPECL [`z:real^3->bool`; `connected_component z' (x:real^3)`; `k:real^3->bool`]
      COMPONENTS_EQ) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]]);;

(* The case of a carrying trace circle k outside the new ball. *)

let MOI_S4N_KEEP_OUTSIDE = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3) car
    (cb:(real^N->bool)->real^3->bool) s c' k.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\
     pl_ball 3 c' /\ c' SUBSET cb s /\ IMAGE h (relative_frontier s) SUBSET interior c' /\
     k SUBSET frontier (IMAGE f1 (moi_s34_ft tt kk s)) /\
     k homeomorphic sphere(vec 0:real^2,&1) /\
     carries_h1 k (IMAGE f1 (moi_s34_ft tt kk s)) /\ k INTER c' = {}
     ==> carries_h1 (moi_s34_trace tt kk f1 c' INTER IMAGE f1 (moi_s34_ft tt kk s))
                    (IMAGE f1 (moi_s34_ft tt kk s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4N_FACE_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4J_BALL3_FACTS (ASSUME `pl_ball 3 (c':real^3->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4J_SIMP2) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* shrink the new ball around h(Bd s) and use the first half of the step *)
  SUBGOAL_THEN `compact (IMAGE (h:real^N->real^3) (relative_frontier s))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN SIMP_TAC[moi_s34_emb];
      UNDISCH_TAC `relative_frontier (s:real^N->bool) SUBSET s` THEN
      UNDISCH_TAC `(s:real^N->bool) IN kk` THEN
      UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c':real^3->bool`; `IMAGE (h:real^N->real^3) (relative_frontier s)`]
    MOI_S4N_SHRINK_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c'':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c'':real^3->bool) SUBSET cb (s:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c':real^3->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`(c'':real^3->bool) SUBSET interior c'`;
                           `(c':real^3->bool) SUBSET cb (s:real^N->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `c'':real^3->bool`] MOI_S4N_W_CARRIES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `c'':real^3->bool`] MOI_S4N_BALL_FACE_TORUS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `c':real^3->bool`] MOI_S4N_BALL_FACE_TORUS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `tor = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  ABBREV_TAC `B = IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
  ABBREV_TAC `th = frontier (tor:real^3->bool)` THEN
  (* a retracting neighbourhood of th INTER frontier c', missing k *)
  MP_TAC(ISPECL [`th:real^3->bool`; `th INTER frontier c':real^3->bool`]
    MOI_S4J_PAIR_RETRACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC PL_POLYHEDRON_INTER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `r:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (k:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  ABBREV_TAC `u1 = u INTER ((:real^3) DIFF k)` THEN
  SUBGOAL_THEN `open (u1:real^3->bool) /\ th INTER frontier c' SUBSET u1 /\
                u1 SUBSET u /\ u1 INTER k = {}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed];
      MAP_EVERY UNDISCH_TAC [`th INTER frontier c' SUBSET (u:real^3->bool)`;
                             `(k:real^3->bool) INTER c' = {}`;
                             `frontier c' SUBSET (c':real^3->bool)`] THEN
      SET_TAC[];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  (* SEP on the open cover of th *)
  MP_TAC(ISPECL [`th:real^3->bool`; `tor:real^3->bool`; `k:real^3->bool`;
                 `th INTER (interior c' UNION u1):real^3->bool`;
                 `th INTER (((:real^3) DIFF c') UNION u1):real^3->bool`] MOI_S4U_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_UNION THEN
      ASM_REWRITE_TAC[OPEN_INTERIOR];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_UNION THEN
      ASM_REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC [`th INTER frontier c' SUBSET (u1:real^3->bool)`;
                             `(c':real^3->bool) DIFF interior c' SUBSET frontier c'`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`(k:real^3->bool) SUBSET th`;
                             `(k:real^3->bool) INTER c' = {}`] THEN
      SET_TAC[];
      MP_TAC(ISPEC `c':real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`(u1:real^3->bool) INTER k = {}`;
                             `(k:real^3->bool) INTER c' = {}`] THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S4J_CARRIES_MONO THEN
      EXISTS_TAC `c'' INTER tor INTER B:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`c'' INTER B SUBSET (th:real^3->bool)`;
                               `(c'':real^3->bool) SUBSET interior c'`] THEN
        SET_TAC[];
        UNDISCH_TAC `(th:real^3->bool) SUBSET tor` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(th INTER (interior c' UNION u1)) INTER
                (th INTER (((:real^3) DIFF c') UNION u1)) = th INTER u1:real^3->bool`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `c':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; DISCH_TAC] THEN
  (* push to th INTER frontier c' by the retraction *)
  MP_TAC(ISPECL [`th INTER u1:real^3->bool`; `th INTER frontier c':real^3->bool`;
                 `tor:real^3->bool`; `r:real^3->real^3`] MOI_S4J_CARRIES_HOMOTOPIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(th:real^3->bool) SUBSET tor` THEN SET_TAC[];
      UNDISCH_TAC `(th:real^3->bool) SUBSET tor` THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `th INTER u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u1:real^3->bool) SUBSET u` THEN SET_TAC[];
      MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN EXISTS_TAC `th:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
      EXISTS_TAC `th INTER u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u1:real^3->bool) SUBSET u` THEN SET_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC MOI_S4J_CARRIES_MONO THEN
  EXISTS_TAC `th INTER frontier c':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s34_trace] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`c' INTER th SUBSET (B:real^3->bool)`;
                         `frontier c' SUBSET (c':real^3->bool)`;
                         `(th:real^3->bool) SUBSET tor`] THEN
  SET_TAC[]);;
(* The H_1 step and Operation 1 (inside case). *)

let MOI_S4N_H1_KEEP_THM = prove
 (MOI_S4N_H1_KEEP,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4N_FACE_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `(cb:(real^N->bool)->real^3->bool) s`]
    MOI_S4N_BALL_FACE_TORUS) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `tor = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  ABBREV_TAC `z = moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s)` THEN
  (* the old trace lies on the boundary torus and carries *)
  SUBGOAL_THEN `(z:real^3->bool) SUBSET frontier tor` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(z:real^3->bool) SUBSET cb (s:real^N->bool)`;
      `(z:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `(cb:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)
       SUBSET frontier tor`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 (z:real^3->bool) tor` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fb1 tt kk (h:real^N->real^3) f1 car s (cb s)` THEN
    REWRITE_TAC[moi_s34_fb1] THEN
    REWRITE_TAC[ASSUME `moi_s34_trace tt kk (f1:real^N->real^3)
                          ((cb:(real^N->bool)->real^3->bool) s) = z`;
                ASSUME `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) = tor`] THEN
    SUBGOAL_THEN `(z:real^3->bool) INTER tor = z` (fun th -> SIMP_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3->bool) SUBSET frontier tor`;
                           `frontier tor SUBSET (tor:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~trivial_group (homology_group(&1,subtopology euclidean (tor:real^3->bool)))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4N_CARRIES_EMPTY THEN
    UNDISCH_TAC `carries_h1 (z:real^3->bool) tor` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a carrying trace circle *)
  MP_TAC(ISPECL [`frontier tor:real^3->bool`; `tor:real^3->bool`; `z:real^3->bool`]
    MOI_S4U_T1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET z` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(k:real^3->bool) INTER c' = {}` THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `c':real^3->bool`; `k:real^3->bool`]
      MOI_S4N_KEEP_OUTSIDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(k:real^3->bool) SUBSET z`;
                             `(z:real^3->bool) SUBSET frontier tor`] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* k meets the new ball, hence is a circle of the new trace *)
  MP_TAC(ISPECL [`z:real^3->bool`;
                 `moi_s34_trace tt kk (f1:real^N->real^3) c'`;
                 `c':real^3->bool`; `k:real^3->bool`] MOI_S4N_COMPONENT_KEPT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4J_CARRIES_MONO THEN EXISTS_TAC `k:real^3->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  MAP_EVERY UNDISCH_TAC [`(k:real^3->bool) SUBSET z INTER c'`;
                         `(k:real^3->bool) SUBSET z`; `(z:real^3->bool) SUBSET frontier tor`;
                         `frontier tor SUBSET (tor:real^3->bool)`] THEN
  SET_TAC[]);;

let OP1_IN = prove
 (MOI_S34_OP1_IN,
  ACCEPT_TAC(MP MOI_S4N_OP1_FROM_H1 MOI_S4N_H1_KEEP_THM));;

