(* ========================================================================= *)
(* pc_moi_s33_sorient: side orientation for Moise 33.1 Lemma 13 (parts O3   *)
(* and O4 of the route of pc_moi_s33_match).  Main theorems                 *)
(* MOI_S3SO_DICHOT, MOI_S3SO_CONST and MOI_S3SO_DIR, the statements         *)
(* MOI_S3MT_SORIENT_DICHOT_TERM, MOI_S3MT_SORIENT_CONST_TERM and            *)
(* MOI_S3MT_SORIENT_DIR_TERM of pc_moi_s33_sorstmt.ml:                      *)
(*   DICHOT  a PL homeomorphism between pieces of two two-sided surfaces in *)
(*           real^3 is side-preserving, or becomes so after the model       *)
(*           reflection of the holed disk model;                             *)
(*   CONST   side preservation spreads from a nonempty open part;           *)
(*   DIR     two side-preserving piece maps agreeing setwise on a common    *)
(*           boundary circle differ there by an orientation-preserving      *)
(*           circle map.                                                     *)
(* The side sign of a flat triangle (a,b,c) in a two-sided surface: the     *)
(* normal half-ball of (b - a) cross (c - a) at a relative interior point  *)
(* lies in the inner side (moi_s3so_pos).                                    *)
(* The circle orientation facts (cyclic order moi_s3ci_cyc3, CYCPRES and    *)
(* CYCREV, ORIENT, LOCAL) come from pc_moi_s33_circ.                        *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_sides.ml";;
needs "src/pc_moi_lt_sphere.ml";;
needs "src/pc_moi_s28_tria.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_s33_char.ml";;
needs "src/pc_moi_s33_sorstmt.ml";;
needs "src/pc_moi_s33_circ.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the side sign of flat triangles in a two-sided surface.          *)
(* A flat triangle in a combinatorial surface is the surface near each of   *)
(* its relative interior points (invariance of domain against a plane chart *)
(* of the surface); hence one normal half-ball lies in the inner side and   *)
(* the other misses it, uniformly along the relative interior.              *)
(* ------------------------------------------------------------------------- *)

let moi_s3so_pos = new_definition
 `moi_s3so_pos (i:real^3->bool) (a:real^3) (b:real^3) (c:real^3) <=>
    ?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
          !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p) ==> z IN i`;;

let moi_s3so_sided = new_definition
 `moi_s3so_sided (s:real^3->bool) (i:real^3->bool) <=>
    (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = s) /\
    (?e. open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF s /\
         frontier i = s /\ frontier e = s)`;;

(* Non-collinear triples and their normals. *)

let MOI_S3SO_NONCOL_CROSS = prove
 (`!a b c:real^3. ~collinear {a,b,c} <=> ~((b - a) cross (c - a) = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CROSS_EQ_0] THEN
  MP_TAC(ISPECL [`b:real^3`; `a:real^3`; `c:real^3`] COLLINEAR_3) THEN
  SUBGOAL_THEN `{b:real^3,a,c} = {a,b,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let MOI_S3SO_COLLINEAR_CROSS = prove
 (`!a b c:real^3. collinear {a,b,c} <=> (b - a) cross (c - a) = vec 0`,
  MESON_TAC[MOI_S3SO_NONCOL_CROSS]);;

(* Every point of a closed combinatorial surface has a plane chart. *)

let MOI_S3SO_SURF_R2 = prove
 (`!(m:(real^3->bool)->bool) y.
     FINITE m /\ combinatorial_manifold 2 m /\ y IN UNIONS m
     ==> moi_s28_locally_r2 (UNIONS m) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `m:(real^3->bool)->bool` SURF_CHARTS) THEN
  ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `y:real^3`) (K ALL_TAC)) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `m:(real^3->bool)->bool` SURF_CHARTS) THEN
  ASM_SIMP_TAC[MOI_S8TA_CM_CMB; NOT_IN_EMPTY]);;

(* A flat triangle in a closed combinatorial surface is the surface near    *)
(* each relative interior point.                                            *)

let MOI_S3SO_FLAT = prove
 (`!(m:(real^3->bool)->bool) a b c p.
     FINITE m /\ combinatorial_manifold 2 m /\
     ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET UNIONS m /\
     p IN relative_interior(convex hull {a,b,c})
     ==> ?r. &0 < r /\ UNIONS m INTER ball(p,r) SUBSET convex hull {a,b,c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN convex hull {a,b,c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS m` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`m:(real^3->bool)->bool`; `p:real^3`] MOI_S3SO_SURF_R2) THEN
  ASM_REWRITE_TAC[moi_s28_locally_r2; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `phi:real^3->real^2`
      (X_CHOOSE_TAC `phi':real^2->real^3`))))) THEN
  (* the plane map *)
  ABBREV_TAC `L = \x:real^2. p + x$1 % (b - a) + x$2 % (c - a:real^3)` THEN
  SUBGOAL_THEN `~((b - a) cross (c - a:real^3) = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM MOI_S3SO_NONCOL_CROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. (L:real^2->real^3) x = L y ==> x = y` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `p + x1 % u + x2 % v = p + y1 % u + y2 % v <=>
                              (x1 - y1) % u + (x2 - y2) % v = vec 0:real^3`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `((x:real^2)$1 - (y:real^2)$1) % ((b - a) cross (c - a:real^3)) = vec 0 /\
                  ((x:real^2)$2 - (y:real^2)$2) % ((c - a) cross (b - a:real^3)) = vec 0`
    MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w cross (c - a:real^3)`);
        FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w cross (b - a:real^3)`)] THEN
      REWRITE_TAC[CROSS_LADD; CROSS_LMUL; CROSS_REFL; CROSS_0; VECTOR_MUL_RZERO;
                  VECTOR_ADD_RID; VECTOR_ADD_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((c - a) cross (b - a:real^3) = vec 0)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[CROSS_SKEW] THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^2->real^3) continuous_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
    SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  (* a small disk of the plane in the relative interior and in u *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^3) IN o1` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "relative_interior"))
        (concl th))) THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def] o check (fun th ->
    concl th = `open (o1:real^3->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?del. &0 < del /\
                      !x:real^2. x IN ball(vec 0,del)
                                 ==> (L:real^2->real^3) x IN ball(p,min e1 e2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(L:real^2->real^3) continuous (at (vec 0))` MP_TAC THENL
     [UNDISCH_TAC `(L:real^2->real^3) continuous_on (:real^2)` THEN
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `min e1 e2`) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `del:real` THEN ASM_REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `(L:real^2->real^3) (vec 0) = p` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[VEC_COMPONENT] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `del:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. (L:real^2->real^3) x IN affine hull {a,b,c}` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `(p:real^3) IN affine hull {a,b,c}` MP_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `v1:real`
      (X_CHOOSE_THEN `w1:real` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u1 - (x:real^2)$1 - x$2`; `v1 + (x:real^2)$1`; `w1 + (x:real^2)$2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (L:real^2->real^3) (ball(vec 0,del)) SUBSET u` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(L:real^2->real^3) x IN ball(p,e1) INTER affine hull {a,b,c} /\
                  (L:real^2->real^3) x IN ball(p,e2)` MP_TAC THENL
     [ASM_SIMP_TAC[IN_INTER] THEN
      SUBGOAL_THEN `(L:real^2->real^3) x IN ball(p,min e1 e2)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(L:real^2->real^3) x IN o1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `e2:real`)) (concl th))) THEN
      UNDISCH_TAC `(L:real^2->real^3) x IN ball(p,e2)` THEN
      REWRITE_TAC[IN_BALL] THEN MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    UNDISCH_TAC `(L:real^2->real^3) x IN ball(p,e1) INTER affine hull {a,b,c}` THEN
    UNDISCH_TAC `ball(p:real^3,e1) INTER affine hull {a,b,c} SUBSET convex hull {a,b,c}` THEN
    UNDISCH_TAC `convex hull {a,b,c} SUBSET UNIONS (m:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `u = UNIONS (m:(real^3->bool)->bool) INTER o1` THEN
    UNDISCH_TAC `(L:real^2->real^3) x IN o1` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `u:real^3->bool`; `phi:real^3->real^2`;
                 `phi':real^2->real^3`; `L:real^2->real^3`; `ball(vec 0:real^2,del)`]
    MOI_S8TA_EMB_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S8TA_HOMEO_IMAGE];
      CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o2:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^3) IN o2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^3) IN IMAGE (L:real^2->real^3) (ball(vec 0,del))` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[VEC_COMPONENT] THEN VECTOR_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def] o check (fun th ->
    concl th = `open (o2:real^3->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (L:real^2->real^3) (ball(vec 0,del)) SUBSET convex hull {a,b,c}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `e1:real`)) (concl th) &&
      is_comb (concl th) && fst(strip_comb(concl th)) = `(SUBSET):(real^3->bool)->(real^3->bool)->bool`)) THEN
    SUBGOAL_THEN `(L:real^2->real^3) x IN ball(p,min e1 e2)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(p:real^3,r) SUBSET o2` MP_TAC THENL
   [UNDISCH_TAC `!x:real^3. dist(x,p) < r ==> x IN o2` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (L:real^2->real^3) (ball(vec 0,del)) = UNIONS m INTER o2` THEN
  SET_TAC[]);;

(* The normal of (a,b,c) is orthogonal to the plane of the triangle. *)

let MOI_S3SO_NORMAL_PLANE = prove
 (`!a b c x y:real^3.
     x IN affine hull {a,b,c} /\ y IN affine hull {a,b,c}
     ==> ((b - a) cross (c - a)) dot (y - x) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `v1:real` (X_CHOOSE_THEN `w1:real`
      STRIP_ASSUME_TAC)))
    (X_CHOOSE_THEN `u2:real` (X_CHOOSE_THEN `v2:real` (X_CHOOSE_THEN `w2:real`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(y:real^3) - x = (v2 - v1) % (b - a) + (w2 - w1) % (c - a)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u1 = &1 - v1 - w1 /\ u2 = &1 - v2 - w2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF] THEN REAL_ARITH_TAC]);;

(* The side sign at any relative interior point. *)

let MOI_S3SO_POS_AT = prove
 (`!(s:real^3->bool) i a b c p.
     moi_s3so_sided s i /\ ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET s /\
     p IN relative_interior(convex hull {a,b,c})
     ==> ?d. &0 < d /\
             (moi_s3so_pos i a b c
              ==> (!z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                       ==> z IN i) /\
                  (!z. z IN ball(p,d) /\ ((b - a) cross (c - a)) dot (z - p) < &0
                       ==> ~(z IN i))) /\
             (~moi_s3so_pos i a b c
              ==> (!z. z IN ball(p,d) /\ ((b - a) cross (c - a)) dot (z - p) < &0
                       ==> z IN i) /\
                  (!z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                       ==> ~(z IN i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3so_sided] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `n:real^3 = (b - a) cross (c - a)` THEN
  SUBGOAL_THEN `~(n:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[GSYM MOI_S3SO_NONCOL_CROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `?R. &0 < R /\ convex hull {a,b,c} SUBSET ball(p:real^3,R)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET_BALL THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    SIMP_TAC[FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `e:real^3->bool`; `p:real^3`; `R:real`]
    MOI_FSD_SIDES_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `p:real^3`; `R:real`; `i INTER ball(p:real^3,R)`;
                 `e INTER ball(p:real^3,R)`; `convex hull {a,b,c:real^3}`; `n:real^3`]
    MOI_FSTR_POSN_UNIFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      EXPAND_TAC "n" THEN MATCH_MP_TAC MOI_S3SO_NORMAL_PLANE THEN
      ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`; `q:real^3`]
      MOI_S3SO_FLAT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "n" THEN
    MATCH_MP_TAC MOI_S3SO_NORMAL_PLANE THEN
    SUBGOAL_THEN `(z:real^3) IN convex hull {a,b,c} /\ q IN convex hull {a,b,c}` MP_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
      MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
  ASM_SIMP_TAC[MOI_FSD_POSN_GLOBAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s3so_pos] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
  UNDISCH_TAC `DISJOINT (i:real^3->bool) e` THEN SET_TAC[]);;

(* Two triangles of the surface with a common relative interior point and  *)
(* proportional normals: the side signs agree iff the factor is positive.   *)

let MOI_S3SO_POS_CMP = prove
 (`!(s:real^3->bool) i a b c a' b' c' p lam.
     moi_s3so_sided s i /\
     ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET s /\
     ~collinear {a',b',c'} /\ convex hull {a',b',c'} SUBSET s /\
     p IN relative_interior(convex hull {a,b,c}) /\
     p IN relative_interior(convex hull {a',b',c'}) /\
     (b' - a') cross (c' - a') = lam % ((b - a) cross (c - a))
     ==> (moi_s3so_pos i a' b' c' <=> (moi_s3so_pos i a b c <=> &0 < lam))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                 `p:real^3`] MOI_S3SO_POS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `a':real^3`; `b':real^3`; `c':real^3`;
                 `p:real^3`] MOI_S3SO_POS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `n:real^3 = (b - a) cross (c - a)` THEN
  SUBGOAL_THEN `~(n:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[GSYM MOI_S3SO_NONCOL_CROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(lam = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {a':real^3,b',c'}` THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_CROSS; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  ABBREV_TAC `t = min d1 d2 / (&2 * norm(n:real^3))` THEN
  SUBGOAL_THEN `&0 < norm(n:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    UNDISCH_TAC `&0 < norm(n:real^3)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = p + t % n` THEN
  SUBGOAL_THEN `(z:real^3) IN ball(p,d1) /\ z IN ball(p,d2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[IN_BALL; NORM_ARITH `dist(p,p + x:real^3) = norm x`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_FIELD
      `&0 < x ==> m / (&2 * x) * x = m / &2`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d1`; `&0 < d2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n dot (z - p:real^3) /\
                ((b' - a') cross (c' - a')) dot (z - p) = lam * (t * (n dot n))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_ARITH `(p + x) - p:real^3 = x`] THEN
    ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL; DOT_POS_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n dot (n:real^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < lam` THENL
   [SUBGOAL_THEN `&0 < ((b' - a') cross (c' - a')) dot (z - p:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `((b' - a') cross (c' - a')) dot (z - p:real^3) < &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < --x ==> x < &0`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(&0 < lam)`; `~(lam = &0)`] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Antisymmetry of the side sign. *)

let MOI_S3SO_POS_SWAP = prove
 (`!(s:real^3->bool) i a b c.
     moi_s3so_sided s i /\ ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET s
     ==> (moi_s3so_pos i b a c <=> ~moi_s3so_pos i a b c) /\
         (moi_s3so_pos i a c b <=> ~moi_s3so_pos i a b c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^3. p IN relative_interior(convex hull {a,b,c})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{b:real^3,a,c} = {a,b,c} /\ {a:real^3,c,b} = {a,b,c}` STRIP_ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                   `b:real^3`; `a:real^3`; `c:real^3`; `p:real^3`; `-- &1`] MOI_S3SO_POS_CMP);
    MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                   `a:real^3`; `c:real^3`; `b:real^3`; `p:real^3`; `-- &1`] MOI_S3SO_POS_CMP)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [VEC3_TAC; ALL_TAC]) THEN
  REWRITE_TAC[REAL_ARITH `~(&0 < -- &1)`] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: planar orientation and affine images.  The planar sign of        *)
(* a triangle (u,v,w) in real^2 is the determinant of (v - u, w - u); an    *)
(* affine map x |-> l x + y into real^3 multiplies the normal of the image  *)
(* triangle by it.  A triangulation of the model on which a PL map is       *)
(* affine and maps each simplex into a simplex of a given complex.          *)
(* ------------------------------------------------------------------------- *)

let moi_s3so_det = new_definition
 `moi_s3so_det (u:real^2) (v:real^2) (w:real^2) =
    (v - u)$1 * (w - u)$2 - (v - u)$2 * (w - u)$1`;;

let MOI_S3SO_R2_EXPAND = prove
 (`!x:real^2. x = x$1 % basis 1 + x$2 % basis 2`,
  GEN_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let MOI_S3SO_CROSS_COMB = prove
 (`!p1 p2 q1 q2 (x:real^3) y.
     (p1 % x + p2 % y) cross (q1 % x + q2 % y) = (p1 * q2 - p2 * q1) % (x cross y)`,
  VEC3_TAC);;

let MOI_S3SO_LINEAR_R2 = prove
 (`!l:real^2->real^3. linear l ==> !x. l x = x$1 % l(basis 1) + x$2 % l(basis 2)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MOI_S3SO_R2_EXPAND] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]));;

let MOI_S3SO_AFF_CROSS = prove
 (`!(l:real^2->real^3) y u v w.
     linear l
     ==> ((l v + y) - (l u + y)) cross ((l w + y) - (l u + y)) =
         moi_s3so_det u v w % (l(basis 1) cross l(basis 2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(x + y) - (z + y):real^3 = x - z`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_SUB th)]) THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP MOI_S3SO_LINEAR_R2 th]) THEN
  REWRITE_TAC[MOI_S3SO_CROSS_COMB; moi_s3so_det] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LZERO; REAL_SUB_RZERO; VECTOR_MUL_LID]);;

(* Planar collinearity is the vanishing of the determinant. *)

let MOI_S3SO_COLLINEAR_DET = prove
 (`!u v w:real^2. collinear {u,v,w} <=> moi_s3so_det u v w = &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`v:real^2`; `u:real^2`; `w:real^2`] COLLINEAR_3) THEN
  SUBGOAL_THEN `{v:real^2,u,w} = {u,v,w}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; moi_s3so_det] THEN
  ABBREV_TAC `p:real^2 = v - u` THEN ABBREV_TAC `q:real^2 = w - u` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    ASM_CASES_TAC `(p:real^2)$1 = &0 /\ p$2 = &0` THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    ASM_CASES_TAC `(p:real^2)$1 = &0` THENL
     [EXISTS_TAC `(q:real^2)$2 / (p:real^2)$2` THEN
      SUBGOAL_THEN `~((p:real^2)$2 = &0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(p:real^2)$1 * (q:real^2)$2 - p$2 * q$1 = &0` THEN
      UNDISCH_TAC `~((p:real^2)$2 = &0)` THEN UNDISCH_TAC `(p:real^2)$1 = &0` THEN
      CONV_TAC REAL_FIELD;
      EXISTS_TAC `(q:real^2)$1 / (p:real^2)$1` THEN
      UNDISCH_TAC `(p:real^2)$1 * (q:real^2)$2 - p$2 * q$1 = &0` THEN
      UNDISCH_TAC `~((p:real^2)$1 = &0)` THEN CONV_TAC REAL_FIELD]]);;

(* A triangulation of the domain on which a PL map is affine and maps each *)
(* nonempty simplex into a member of a finite family of polytopes covering  *)
(* the image.                                                               *)

let MOI_S3SO_REFINE = prove
 (`!(c:(real^2->bool)->bool) (m:(real^3->bool)->bool) (g:real^2->real^3).
     simplicial_complex c /\ pl_map_on (UNIONS c) g /\ FINITE m /\
     (!k. k IN m ==> polytope k) /\ IMAGE g (UNIONS c) SUBSET UNIONS m
     ==> ?t. simplicial_complex t /\ UNIONS t = UNIONS c /\
             (!s. s IN t ==> ?l y. linear l /\ !x. x IN s ==> g x = l x + y) /\
             (!s. s IN t /\ ~(s = {}) ==> ?k. k IN m /\ IMAGE g s SUBSET k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^2->bool)->bool`; `g:real^2->real^3`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(real^2->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "aff"))))) THEN
  ABBREV_TAC `d = {{x | x IN s /\ (g:real^2->real^3) x IN k} |
                   s IN t1 /\ (k:real^3->bool) IN m}` THEN
  SUBGOAL_THEN `FINITE (t1:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (d:(real^2->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^2->bool. k IN d ==> polytope k /\ k SUBSET UNIONS t1`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^2->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (X_CHOOSE_THEN `k:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    USE_THEN "aff" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:real^2->bool) IN t1`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{x | x IN s /\ (g:real^2->real^3) x IN k} =
                  s INTER {x | (l:real^2->real^3) x IN IMAGE (\z. --y + z) k}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN ASM_CASES_TAC `(x:real^2) IN s` THEN
      ASM_SIMP_TAC[] THEN
      MESON_TAC[VECTOR_ARITH `(l:real^3) = --y + z <=> z = l + y`];
      ALL_TAC] THEN
    MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
    MATCH_MP_TAC POLYHEDRON_LINEAR_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYHEDRON_TRANSLATION_EQ] THEN
    ASM_MESON_TAC[POLYTOPE_IMP_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:(real^2->bool)->bool`; `d:(real^2->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^2->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "new")))))) THEN
  EXISTS_TAC `t:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
    USE_THEN "sub" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:real^2->bool) IN t`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "aff" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s1:real^2->bool) IN t1`))) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^2. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  USE_THEN "sub" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:real^2->bool) IN t`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k:real^3->bool. k IN m /\ (g:real^2->real^3) x IN k` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN UNIONS c` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^3) (UNIONS c) SUBSET UNIONS m` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{y | y IN s1 /\ (g:real^2->real^3) y IN k} IN d` MP_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`s1:real^2->bool`; `k:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "new" (MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?s':real^2->bool. s' IN f /\ (x:real^2) IN s'` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN {y | y IN s1 /\ (g:real^2->real^3) y IN k}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET s'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s' INTER s) face_of (s:real^2->bool)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        GEN_REWRITE_RULE I [simplicial_complex] o
        check (fun th -> concl th = `simplicial_complex (t:(real^2->bool)->bool)`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`s':real^2->bool`; `s:real^2->bool`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s' INTER s:real^2->bool`; `s:real^2->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `{y | y IN s1 /\ (g:real^2->real^3) y IN k} = UNIONS f` THEN
  UNDISCH_TAC `(s':real^2->bool) IN f` THEN UNDISCH_TAC `(s:real^2->bool) SUBSET s'` THEN
  REWRITE_TAC[EXTENSION; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIONS] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: triangles sharing an edge.  If the third vertices lie on        *)
(* the same side of the common edge, the two triangles share a relative    *)
(* interior point; in a simplicial complex they therefore lie on opposite  *)
(* sides (opposite planar signs).                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_NONCOL_FACTS = prove
 (`!x y z:real^N.
     ~collinear {x,y,z}
     ==> ~(x = y) /\ ~(x = z) /\ ~(y = z) /\ ~affine_dependent {x,y,z}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x:real^N = y) /\ ~(x = z) /\ ~(y = z)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~collinear {x:real^N,y,z}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~collinear {x:real^N,y,z}` THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]);;

let MOI_S3SO_RELINT_BARY = prove
 (`!x y z p:real^N.
     ~collinear {x,y,z}
     ==> (p IN relative_interior(convex hull {x,y,z}) <=>
          ?u1 u2 u3. &0 < u1 /\ &0 < u2 /\ &0 < u3 /\ u1 + u2 + u3 = &1 /\
                     p = u1 % x + u2 % y + u3 % z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_RELINT_3 THEN
  ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]);;

(* Third vertices on the same side: a common relative interior point. *)

let MOI_S3SO_SAME_SIDE = prove
 (`!x y z1 z2:real^N al be.
     ~collinear {x,y,z1} /\ ~collinear {x,y,z2} /\
     z1 = x + al % (y - x) + be % (z2 - x) /\ &0 < be
     ==> ?p. p IN relative_interior(convex hull {x,y,z1}) /\
             p IN relative_interior(convex hull {x,y,z2})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ep = &1 / (&4 * (&1 + abs al + be))` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * (&1 + abs al + be) = &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN
    SUBGOAL_THEN `&0 < &1 + abs al + be` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &1 + abs al + be` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ep * abs al /\ &0 < ep * be` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_MUL; REAL_ABS_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `ep * (abs al + be) < &1 / &4 /\ ep < &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `((&1 - ep) / &2) % x + ((&1 - ep) / &2) % y + ep % (z1:real^N)` THEN
  ASM_SIMP_TAC[MOI_S3SO_RELINT_BARY] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(&1 - ep) / &2`; `(&1 - ep) / &2`; `ep:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&1 - ((&1 - ep) / &2 + ep * al) - ep * be`;
                        `(&1 - ep) / &2 + ep * al`; `ep * be`] THEN
  SUBGOAL_THEN `abs(ep * al) <= ep * abs al` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ep * be` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `ep * abs al + ep * be < &1 / &4` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* Two triangles of a simplicial complex in the plane with a common edge   *)
(* have opposite planar signs.                                              *)

let MOI_S3SO_CRAMER = prove
 (`!x y z1 z2:real^2.
     ~(moi_s3so_det x y z2 = &0)
     ==> z1 = x + (moi_s3so_det x z1 z2 / moi_s3so_det x y z2) % (y - x) +
                  (moi_s3so_det x y z1 / moi_s3so_det x y z2) % (z2 - x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3so_det] THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT] THEN
  UNDISCH_TAC `~(((y:real^2) - x)$1 * ((z2:real^2) - x)$2 -
                 (y - x)$2 * (z2 - x)$1 = &0)` THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_FIELD);;

let MOI_S3SO_DIV_POS = prove
 (`!a b. &0 < a * b ==> &0 < a / b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(b = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&0 < a * b` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a / b = (a * b) * inv b pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `~(b = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_POW_2; REAL_INV_EQ_0]);;

let MOI_S3SO_OPP_DET = prove
 (`!(t:(real^2->bool)->bool) x y z1 z2.
     simplicial_complex t /\
     convex hull {x,y,z1} IN t /\ convex hull {x,y,z2} IN t /\
     ~collinear {x,y,z1} /\ ~collinear {x,y,z2} /\ ~(z1 = z2)
     ==> moi_s3so_det x y z1 * moi_s3so_det x y z2 < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(moi_s3so_det x y z1 = &0) /\ ~(moi_s3so_det x y z2 = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_COLLINEAR_DET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> x < &0`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < moi_s3so_det x y z1 / moi_s3so_det x y z2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_DIV_POS THEN REWRITE_TAC[REAL_LT_LE] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2`; `y:real^2`; `z1:real^2`; `z2:real^2`;
                 `moi_s3so_det x z1 z2 / moi_s3so_det x y z2`;
                 `moi_s3so_det x y z1 / moi_s3so_det x y z2`] MOI_S3SO_SAME_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3SO_CRAMER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t1 = convex hull {x:real^2,y,z1}` THEN
  ABBREV_TAC `t2 = convex hull {x:real^2,y,z2}` THEN
  SUBGOAL_THEN `(t1 INTER t2) face_of (t1:real^2->bool) /\ (t1 INTER t2) face_of t2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(t1:real^2->bool) = t2` ASSUME_TAC THENL
   [SUBGOAL_THEN `t1 INTER t2 = (t1:real^2->bool) /\ t1 INTER t2 = t2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
       [MP_TAC(ISPECL [`t1 INTER t2:real^2->bool`; `t1:real^2->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR);
        MP_TAC(ISPECL [`t1 INTER t2:real^2->bool`; `t2:real^2->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR)] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t1:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `t2:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z1:real^2 = x) /\ ~(z1 = y) /\ ~affine_dependent {x:real^2,y,z1} /\
                ~affine_dependent {x:real^2,y,z2}` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^2) IN {x,y,z2}` MP_TAC THENL
   [SUBGOAL_THEN `(z1:real^2) extreme_point_of convex hull {x,y,z2}` MP_TAC THENL
     [SUBGOAL_THEN `convex hull {x:real^2,y,z2} = convex hull {x,y,z1}` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               ASSUME `~affine_dependent {x:real^2,y,z1}`] THEN
      SET_TAC[];
      SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               ASSUME `~affine_dependent {x:real^2,y,z2}`]];
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: triangles of the surface inside one or two triangles of its      *)
(* complex.  Plane coordinates in a triangle (a,b,c); two triangles in one  *)
(* 2-simplex of m that share an edge and no relative interior point have    *)
(* opposite side signs; so do two triangles with an edge on the common edge *)
(* of two adjacent 2-simplices of m (edge rule of pc_moi_fnd_sgn, made     *)
(* global by pc_moi_fnd_sides).                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_IN_PLANE = prove
 (`!a b c x:real^3.
     x IN affine hull {a,b,c} <=> ?x1 x2. x = a + x1 % (b - a) + x2 % (c - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
      STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`v:real`; `w:real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u = &1 - v - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `x2:real` SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`&1 - x1 - x2`; `x1:real`; `x2:real`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]]);;

let MOI_S3SO_PLANE_CROSS = prove
 (`!a b c:real^3 x1 x2 y1 y2 z1 z2.
     ((a + y1 % (b - a) + y2 % (c - a)) - (a + x1 % (b - a) + x2 % (c - a))) cross
     ((a + z1 % (b - a) + z2 % (c - a)) - (a + x1 % (b - a) + x2 % (c - a))) =
     ((y1 - x1) * (z2 - x2) - (y2 - x2) * (z1 - x1)) % ((b - a) cross (c - a))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(a + y1 % u + y2 % v) - (a + x1 % u + x2 % v):real^3 =
                            (y1 - x1) % u + (y2 - x2) % v`] THEN
  REWRITE_TAC[MOI_S3SO_CROSS_COMB]);;

let MOI_S3SO_PLANE_REP = prove
 (`!a b c:real^3 p1 p2 q1 q2 r1 r2 s1 s2.
     ~((q1 - p1) * (s2 - p2) - (q2 - p2) * (s1 - p1) = &0)
     ==> ?al. a + r1 % (b - a) + r2 % (c - a) =
              (a + p1 % (b - a) + p2 % (c - a)) +
              al % ((a + q1 % (b - a) + q2 % (c - a)) - (a + p1 % (b - a) + p2 % (c - a))) +
              (((q1 - p1) * (r2 - p2) - (q2 - p2) * (r1 - p1)) /
               ((q1 - p1) * (s2 - p2) - (q2 - p2) * (s1 - p1))) %
              ((a + s1 % (b - a) + s2 % (c - a)) - (a + p1 % (b - a) + p2 % (c - a)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `dd = (q1 - p1) * (s2 - p2) - (q2 - p2) * (s1 - p1)` THEN
  EXISTS_TAC `((r1 - p1) * (s2 - p2) - (r2 - p2) * (s1 - p1)) / dd` THEN
  ABBREV_TAC `al = ((r1 - p1) * (s2 - p2) - (r2 - p2) * (s1 - p1)) / dd` THEN
  ABBREV_TAC `be = ((q1 - p1) * (r2 - p2) - (q2 - p2) * (r1 - p1)) / dd` THEN
  SUBGOAL_THEN `r1 = p1 + al * (q1 - p1) + be * (s1 - p1) /\
                r2 = p2 + al * (q2 - p2) + be * (s2 - p2)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"; "be"] THEN UNDISCH_TAC `~(dd = &0)` THEN
    EXPAND_TAC "dd" THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
    [th]) o check (fun th -> lhs(concl th) = `r2:real`)) THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
    [th]) o check (fun th -> lhs(concl th) = `r1:real`)) THEN
  VECTOR_ARITH_TAC);;

(* Non-collinear triples span planes. *)

let MOI_S3SO_NONCOL_DIM = prove
 (`!a b c:real^N. ~collinear {a,b,c} ==> aff_dim(convex hull {a,b,c}) = &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_AFF_DIM; AFF_DIM_CONVEX_HULL] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `{a:real^N,b,c}` AFF_DIM_LE_CARD) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {a:real^N,b,c} <= 3` MP_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_INT_ARITH_TAC);;

(* A non-degenerate triangle inside another: relative interiors nest. *)

let MOI_S3SO_SUB_RELINT = prove
 (`!a b c p q r:real^N.
     ~collinear {a,b,c} /\ ~collinear {p,q,r} /\
     convex hull {p,q,r} SUBSET convex hull {a,b,c}
     ==> relative_interior(convex hull {p,q,r}) SUBSET
         relative_interior(convex hull {a,b,c})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
  ASM_SIMP_TAC[MOI_S3SO_NONCOL_DIM; INT_LE_REFL]);;

(* The complex of a closed combinatorial surface. *)

let MOI_S3SO_M_FACTS = prove
 (`!m:(real^3->bool)->bool.
     FINITE m /\ combinatorial_manifold 2 m
     ==> simplicial_complex m /\ !s. s IN m ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TB_DIM THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC MOI_S3SO_SURF_R2 THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3SO_M_TRI = prove
 (`!(m:(real^3->bool)->bool) t p q r.
     FINITE m /\ combinatorial_manifold 2 m /\ t IN m /\
     p IN t /\ q IN t /\ r IN t /\ ~collinear {p,q,r}
     ==> ?a b c. t = convex hull {a,b,c} /\ ~collinear {a,b,c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `m:(real^3->bool)->bool` MOI_S3SO_M_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (t:real^3->bool) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= aff_dim (t:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim {p:real^3,q,r}` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~collinear {p:real^3,q,r}` THEN REWRITE_TAC[COLLINEAR_AFF_DIM] THEN
      INT_ARITH_TAC;
      MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:int) = &2` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `aff_dim (t:real^3->bool) <= &2` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 <= aff_dim (t:real^3->bool)` THEN
    UNDISCH_TAC `aff_dim (t:real^3->bool) = n` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex] o check (fun th ->
    concl th = `&2 simplex (t:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^3->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; INT_OF_NUM_EQ;
                  INT_ARITH `&2 + &1:int = &3`];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`; `c:real^3`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COLLINEAR_AFF_DIM] THEN
  SUBGOAL_THEN `aff_dim {a:real^3,b,c} = &2` (fun th -> REWRITE_TAC[th] THEN INT_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_CONVEX_HULL] THEN
  UNDISCH_TAC `aff_dim (t:real^3->bool) = &2` THEN ASM_REWRITE_TAC[]);;

(* The edge rule for two adjacent triangles of the complex, globally. *)

let MOI_S3SO_M_EDGE = prove
 (`!(m:(real^3->bool)->bool) i a b c c'.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     convex hull {a,b,c} IN m /\ aff_dim(convex hull {a,b,c}) = &2 /\
     convex hull {a,b,c'} IN m /\ aff_dim(convex hull {a,b,c'}) = &2 /\ ~(c = c')
     ==> (moi_s3so_pos i a b c' <=> ~moi_s3so_pos i a b c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3so_sided] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `m:(real^3->bool)->bool` MOI_FSD_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^3) IN UNIONS m /\ convex hull {a,b,c} SUBSET UNIONS m /\
                convex hull {a,b,c'} SUBSET UNIONS m` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^3) IN convex hull {a,b,c}` MP_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    UNDISCH_TAC `convex hull {a:real^3,b,c} IN m` THEN
    UNDISCH_TAC `convex hull {a:real^3,b,c'} IN m` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET ball(a,R) /\
                convex hull {a:real^3,b,c'} SUBSET ball(a,R)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `e:real^3->bool`;
                 `a:real^3`; `R:real`] MOI_FSD_SIDES_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `R:real`;
                 `i INTER ball(a:real^3,R)`; `e INTER ball(a:real^3,R)`;
                 `a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`] MOI_FSTR_SG_EDGE) THEN
  ASM_SIMP_TAC[MOI_FSD_SG_GLOBAL] THEN
  REWRITE_TAC[GSYM moi_s3so_pos] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S3SO_SIGN_OPP = prove
 (`!x y. x * y < &0 ==> (&0 < y <=> ~(&0 < x))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 < x` THEN ASM_CASES_TAC `&0 < y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_NOT_LT] THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH `x * y = --x * --y`] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC]);;

(* Two triangles in one triangle (a,b,c) of the surface, with a common edge *)
(* and no common relative interior point: opposite side signs.             *)

let MOI_S3SO_IM_SAME = prove
 (`!(s:real^3->bool) i a b c p q r1 r2.
     moi_s3so_sided s i /\ convex hull {a,b,c} SUBSET s /\ ~collinear {a,b,c} /\
     p IN convex hull {a,b,c} /\ q IN convex hull {a,b,c} /\
     r1 IN convex hull {a,b,c} /\ r2 IN convex hull {a,b,c} /\
     ~collinear {p,q,r1} /\ ~collinear {p,q,r2} /\
     ~(?x. x IN relative_interior(convex hull {p,q,r1}) /\
           x IN relative_interior(convex hull {p,q,r2}))
     ==> (moi_s3so_pos i p q r2 <=> ~moi_s3so_pos i p q r1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN convex hull {a,b,c}
                           ==> ?x1 x2. x = a + x1 % (b - a) + x2 % (c - a)`
  (LABEL_TAC "co") THENL
   [REWRITE_TAC[GSYM MOI_S3SO_IN_PLANE] THEN
    MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    ALL_TAC] THEN
  USE_THEN "co" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:real^3) IN convex hull {a,b,c}`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real` (X_CHOOSE_THEN `p2:real` (ASSUME_TAC o SYM))) THEN
  USE_THEN "co" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(q:real^3) IN convex hull {a,b,c}`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real` (X_CHOOSE_THEN `q2:real` (ASSUME_TAC o SYM))) THEN
  USE_THEN "co" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(r1:real^3) IN convex hull {a,b,c}`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `x2:real` (ASSUME_TAC o SYM))) THEN
  USE_THEN "co" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(r2:real^3) IN convex hull {a,b,c}`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real` (X_CHOOSE_THEN `y2:real` (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `l1 = (q1 - p1) * (x2 - p2) - (q2 - p2) * (x1 - p1)` THEN
  ABBREV_TAC `l2 = (q1 - p1) * (y2 - p2) - (q2 - p2) * (y1 - p1)` THEN
  SUBGOAL_THEN `(q - p) cross (r1 - p) = l1 % ((b - a) cross (c - a:real^3)) /\
                (q - p) cross (r2 - p) = l2 % ((b - a) cross (c - a:real^3))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l1"; "l2"] THEN
    MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rand(concl th) = v)))
      [`p:real^3`; `q:real^3`; `r1:real^3`; `r2:real^3`] THEN
    REWRITE_TAC[MOI_S3SO_PLANE_CROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l1 = &0) /\ ~(l2 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~collinear {p:real^3,q,r1}`; UNDISCH_TAC `~collinear {p:real^3,q,r2}`] THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_CROSS; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  (* opposite sides of the line pq *)
  SUBGOAL_THEN `l1 * l2 < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> x < &0`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      is_exists (rand (concl th)))) THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `p1:real`; `p2:real`; `q1:real`;
                   `q2:real`; `x1:real`; `x2:real`; `y1:real`; `y2:real`] MOI_S3SO_PLANE_REP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `al:real`) THEN
    MATCH_MP_TAC MOI_S3SO_SAME_SIDE THEN
    MAP_EVERY EXISTS_TAC [`al:real`; `l1 / l2`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3SO_DIV_POS THEN REWRITE_TAC[REAL_LT_LE] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[REAL_ENTIRE];
    ALL_TAC] THEN
  (* compare with the triangle (a,b,c) *)
  SUBGOAL_THEN
   `!r l. ~collinear {p:real^3,q,r} /\ r IN convex hull {a,b,c} /\
          (q - p) cross (r - p) = l % ((b - a) cross (c - a))
          ==> (moi_s3so_pos i p q r <=> (moi_s3so_pos i a b c <=> &0 < l))`
  (LABEL_TAC "cmp") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex hull {p:real^3,q,r} SUBSET convex hull {a,b,c}` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^3. x IN relative_interior(convex hull {p,q,r})` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3SO_POS_CMP THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `p:real^3`; `q:real^3`; `r:real^3`]
      MOI_S3SO_SUB_RELINT) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "cmp" (fun th -> MP_TAC(SPECL [`r1:real^3`; `l1:real`] th) THEN
                               MP_TAC(SPECL [`r2:real^3`; `l2:real`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(SPECL [`l1:real`; `l2:real`] MOI_S3SO_SIGN_OPP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

(* A triangle inside a triangle (a,b,c) of the surface, compared with it. *)

let MOI_S3SO_SUBTRI_POS = prove
 (`!(s:real^3->bool) i a b c p q r l.
     moi_s3so_sided s i /\ convex hull {a,b,c} SUBSET s /\ ~collinear {a,b,c} /\
     p IN convex hull {a,b,c} /\ q IN convex hull {a,b,c} /\ r IN convex hull {a,b,c} /\
     ~collinear {p,q,r} /\ (q - p) cross (r - p) = l % ((b - a) cross (c - a))
     ==> (moi_s3so_pos i p q r <=> (moi_s3so_pos i a b c <=> &0 < l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {p:real^3,q,r} SUBSET convex hull {a,b,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN relative_interior(convex hull {p,q,r})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3SO_POS_CMP THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`; `p:real^3`; `q:real^3`; `r:real^3`]
    MOI_S3SO_SUB_RELINT) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3SO_EDGE_CROSS = prove
 (`!a b c:real^3 s t v w.
     ((a + t % (b - a)) - (a + s % (b - a))) cross
     ((a + v % (b - a) + w % (c - a)) - (a + s % (b - a))) =
     ((t - s) * w) % ((b - a) cross (c - a))`,
  VEC3_TAC);;

(* Two triangles with an edge on the common edge of two adjacent triangles *)
(* of the complex: opposite side signs.                                     *)

let MOI_S3SO_IM_ADJ = prove
 (`!(m:(real^3->bool)->bool) i a b c c' p q r1 r2.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     convex hull {a,b,c} IN m /\ ~collinear {a,b,c} /\
     convex hull {a,b,c'} IN m /\ ~collinear {a,b,c'} /\ ~(c = c') /\
     p IN convex hull {a,b} /\ q IN convex hull {a,b} /\
     r1 IN convex hull {a,b,c} /\ r2 IN convex hull {a,b,c'} /\
     ~collinear {p,q,r1} /\ ~collinear {p,q,r2}
     ==> (moi_s3so_pos i p q r2 <=> ~moi_s3so_pos i p q r1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`;
                 `c:real^3`; `c':real^3`] MOI_S3SO_M_EDGE) THEN
  ASM_SIMP_TAC[MOI_S3SO_NONCOL_DIM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {a:real^3,b} SUBSET convex hull {a,b,c} /\
                convex hull {a:real^3,b} SUBSET convex hull {a,b,c'}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?s1 t w1 w2. &0 <= w1 /\ &0 <= w2 /\
       (q - p) cross (r1 - p) = ((t - s1) * w1) % ((b - a) cross (c - a:real^3)) /\
       (q - p) cross (r2 - p) = ((t - s1) * w2) % ((b - a) cross (c' - a:real^3))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(p:real^3) IN convex hull {a,b}`) THEN
    MP_TAC(ASSUME `(q:real^3) IN convex hull {a,b}`) THEN
    MP_TAC(ASSUME `(r1:real^3) IN convex hull {a,b,c}`) THEN
    MP_TAC(ASSUME `(r2:real^3) IN convex hull {a,b,c'}`) THEN
    REWRITE_TAC[CONVEX_HULL_2; CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real` (X_CHOOSE_THEN `v2:real` (X_CHOOSE_THEN `w2:real`
      STRIP_ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `v1:real` (X_CHOOSE_THEN `w1:real`
      STRIP_ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`s1:real`; `t:real`; `w1:real`; `w2:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u1 = &1 - s1 /\ u0 = &1 - t /\ x1 = &1 - v1 - w1 /\ x2 = &1 - v2 - w2`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN VEC3_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((t - s1) * w1 = &0) /\ ~((t - s1) * w2 = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~collinear {p:real^3,q,r1}`; UNDISCH_TAC `~collinear {p:real^3,q,r2}`] THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_CROSS; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < w1 /\ &0 < w2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= w /\ ~(w = &0) ==> &0 < w`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((t - s1) * w1 = &0)` THEN UNDISCH_TAC `~((t - s1) * w2 = &0)` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET UNIONS m /\
                convex hull {a:real^3,b,c'} SUBSET UNIONS m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN m ==> x SUBSET UNIONS m`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN convex hull {a,b,c} /\ q IN convex hull {a,b,c} /\
                p IN convex hull {a,b,c'} /\ q IN convex hull {a,b,c'}` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`;
                 `c':real^3`; `p:real^3`; `q:real^3`; `r2:real^3`; `(t - s1) * w2`]
    MOI_S3SO_SUBTRI_POS) THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`;
                 `c:real^3`; `p:real^3`; `q:real^3`; `r1:real^3`; `(t - s1) * w1`]
    MOI_S3SO_SUBTRI_POS) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Part 5: maps that agree on a triangle with an affine map x |-> l x       *)
(* + y.  Images of hulls, the barycentric form and back, non-degeneracy of  *)
(* injective images, inverses, relative interiors, and disjointness of the  *)
(* relative interiors of two triangles of a complex with a common edge.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_AFF_IMAGE_HULL = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ (!x. x IN convex hull s ==> f x = l x + y)
     ==> IMAGE f (convex hull s) = convex hull (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t SUBSET convex hull s
                    ==> IMAGE (f:real^M->real^N) t = IMAGE (\x. l x + y) t`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[HULL_SUBSET; SUBSET_REFL; MOI_REAL_AFFINE_IMAGE_CONVEX_HULL]);;

let MOI_S3SO_AFF_BARY = prove
 (`!(f:real^M->real^N) l y a b c.
     linear l /\ (!x. x IN convex hull {a,b,c} ==> f x = l x + y)
     ==> !u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                 ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^M) IN convex hull {a,b,c} /\ b IN convex hull {a,b,c} /\
                c IN convex hull {a,b,c} /\ u % a + v % b + w % c IN convex hull {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT] THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`; `w:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  SUBGOAL_THEN `u = &1 - v - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_S3SO_BARY_AFF = prove
 (`!(f:real^M->real^N) a b c.
     ~collinear {a,b,c} /\
     (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
              ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c)
     ==> ?l y. linear l /\ !x. x IN convex hull {a,b,c} ==> f x = l x + y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bary")) THEN
  MP_TAC(ISPECL [`{a:real^M,b,c}`; `f:real^M->real^N`] MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)))) THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
    STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "bary" (MP_TAC o SPECL [`u:real`; `v:real`; `w:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  SUBGOAL_THEN `u = &1 - v - w` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

(* An injective map that is affine on a triangle keeps it non-degenerate. *)

let MOI_S3SO_AFF_NONCOL = prove
 (`!(f:real^M->real^N) l y a b c.
     linear l /\ (!x. x IN convex hull {a,b,c} ==> f x = l x + y) /\
     (!x x'. x IN convex hull {a,b,c} /\ x' IN convex hull {a,b,c} /\ f x = f x'
             ==> x = x') /\
     ~collinear {a,b,c}
     ==> ~collinear {f a,f b,f c}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") ASSUME_TAC))) THEN
  SUBGOAL_THEN `!p q r. &0 <= p /\ &0 <= q /\ &0 <= r /\ p + q + r = &1
                        ==> p % a + q % b + r % c IN convex hull {a:real^M,b,c}`
  (LABEL_TAC "mem") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`p:real`; `q:real`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^M) IN convex hull {a,b,c} /\ b IN convex hull {a,b,c} /\
                c IN convex hull {a,b,c}` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) b - f a = l(b - a) /\ f c - f a = l(c - a)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB] THEN CONJ_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^M->real^N) b`; `(f:real^M->real^N) a`; `(f:real^M->real^N) c`]
    COLLINEAR_3) THEN
  SUBGOAL_THEN `{(f:real^M->real^N) b,f a,f c} = {f a,f b,f c}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `b:real^M = a` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f:real^M->real^N) b - f a = l(b - a)` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `~collinear {a:real^M,b,c}` THEN ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    DISCH_TAC THEN
    SUBGOAL_THEN `c:real^M = a` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f:real^M->real^N) c - f a = l(c - a)` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ];
      ALL_TAC] THEN
    UNDISCH_TAC `~collinear {a:real^M,b,c}` THEN ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ABBREV_TAC `mu = &1 / (&4 * (&1 + abs t))` THEN
  SUBGOAL_THEN `&0 < mu /\ mu * (&1 + abs t) = &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `&0 < &1 + abs t` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &1 + abs t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(mu * t) = &1 / &4 - mu` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 / &2 + mu * t - mu /\ &0 <= &1 / &2 - mu * t`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 / &2 + mu * t - mu) % a + (&1 / &2 - mu * t) % b + mu % c IN
      convex hull {a:real^M,b,c} /\
    (&1 / &2) % a + (&1 / &2) % b + &0 % c IN convex hull {a:real^M,b,c}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "mem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^M->real^N)(mu % ((c - a) - t % (b - a))) = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `!z1 z2:real^M. (l:real^M->real^N)(mu % (z1 - t % z2)) =
                                 mu % (l z1 - t % l z2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th; MATCH_MP LINEAR_SUB th]);
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 / &2 + mu * t - mu) % a + (&1 / &2 - mu * t) % b + mu % c:real^M =
    (&1 / &2) % a + (&1 / &2) % b + &0 % c`
  MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `(&1 / &2 + mu * t - mu) % a + (&1 / &2 - mu * t) % b + mu % c:real^M =
      ((&1 / &2) % a + (&1 / &2) % b + &0 % c) + mu % ((c - a) - t % (b - a))`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (VECTOR_ARITH
    `(&1 / &2 + m * t - m) % a + (&1 / &2 - m * t) % b + m % c:real^N =
     (&1 / &2) % a + (&1 / &2) % b + &0 % c
     ==> m % ((c - a) - t % (b - a)) = vec 0`)) THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ] THEN DISCH_TAC THEN
  UNDISCH_TAC `~collinear {a:real^M,b,c}` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`b:real^M`; `a:real^M`; `c:real^M`] COLLINEAR_3) THEN
  SUBGOAL_THEN `{b:real^M,a,c} = {a,b,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]);;

(* The inverse of an injective map that is affine on a triangle is affine  *)
(* on the image triangle.                                                   *)

let MOI_S3SO_INV_AFF = prove
 (`!(f:real^M->real^N) g l y a b c.
     linear l /\ (!x. x IN convex hull {a,b,c} ==> f x = l x + y) /\
     (!x. x IN convex hull {a,b,c} ==> g(f x) = x) /\ ~collinear {a,b,c}
     ==> ~collinear {f a,f b,f c} /\
         IMAGE f (convex hull {a,b,c}) = convex hull {f a,f b,f c} /\
         ?l' y'. linear l' /\ !x. x IN convex hull {f a,f b,f c} ==> g x = l' x + y'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~collinear {(f:real^M->real^N) a,f b,f c}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) (convex hull {a,b,c}) = convex hull {f a,f b,f c}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `{a:real^M,b,c}`]
      MOI_S3SO_AFF_IMAGE_HULL) THEN
    ASM_SIMP_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3SO_BARY_AFF THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `a:real^M`; `b:real^M`;
                 `c:real^M`] MOI_S3SO_AFF_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`u:real`; `v:real`; `w:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(a:real^M) IN convex hull {a,b,c} /\ b IN convex hull {a,b,c} /\
                c IN convex hull {a,b,c} /\ u % a + v % b + w % c IN convex hull {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT] THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u:real`; `v:real`; `w:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* Relative interior points of the image triangle come from relative        *)
(* interior points.                                                          *)

let MOI_S3SO_AFF_RELINT = prove
 (`!(f:real^M->real^N) l y a b c q.
     linear l /\ (!x. x IN convex hull {a,b,c} ==> f x = l x + y) /\
     ~collinear {a,b,c} /\ ~collinear {f a,f b,f c} /\
     q IN relative_interior(convex hull {f a,f b,f c})
     ==> ?p. p IN relative_interior(convex hull {a,b,c}) /\ q = f p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `q IN relative_interior(convex hull {(f:real^M->real^N) a,f b,f c})` THEN
  ASM_SIMP_TAC[MOI_S3SO_RELINT_BARY] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
    STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u % a + v % b + w % c:real^M` THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real`; `v:real`; `w:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `a:real^M`; `b:real^M`;
                 `c:real^M`] MOI_S3SO_AFF_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`u:real`; `v:real`; `w:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* Two triangles of a complex with a common edge have disjoint relative     *)
(* interiors.                                                                *)

let MOI_S3SO_RELINT_DISJ = prove
 (`!(t:(real^N->bool)->bool) x y z1 z2.
     simplicial_complex t /\
     convex hull {x,y,z1} IN t /\ convex hull {x,y,z2} IN t /\
     ~collinear {x,y,z1} /\ ~collinear {x,y,z2} /\ ~(z1 = z2)
     ==> relative_interior(convex hull {x,y,z1}) INTER
         relative_interior(convex hull {x,y,z2}) = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_EMPTY; SUBSET; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
  ABBREV_TAC `t1 = convex hull {x:real^N,y,z1}` THEN
  ABBREV_TAC `t2 = convex hull {x:real^N,y,z2}` THEN
  SUBGOAL_THEN `(t1 INTER t2) face_of (t1:real^N->bool) /\ (t1 INTER t2) face_of t2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(t1:real^N->bool) = t2` ASSUME_TAC THENL
   [SUBGOAL_THEN `t1 INTER t2 = (t1:real^N->bool) /\ t1 INTER t2 = t2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
       [MP_TAC(ISPECL [`t1 INTER t2:real^N->bool`; `t1:real^N->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR);
        MP_TAC(ISPECL [`t1 INTER t2:real^N->bool`; `t2:real^N->bool`]
          FACE_OF_DISJOINT_RELATIVE_INTERIOR)] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t1:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `t2:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z1:real^N = x) /\ ~(z1 = y) /\ ~affine_dependent {x:real^N,y,z1} /\
                ~affine_dependent {x:real^N,y,z2}` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^N) IN {x,y,z2}` MP_TAC THENL
   [SUBGOAL_THEN `(z1:real^N) extreme_point_of convex hull {x,y,z2}` MP_TAC THENL
     [SUBGOAL_THEN `convex hull {x:real^N,y,z2} = convex hull {x,y,z1}` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               ASSUME `~affine_dependent {x:real^N,y,z1}`] THEN
      SET_TAC[];
      SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               ASSUME `~affine_dependent {x:real^N,y,z2}`]];
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]]);;

(* Signs of a quotient. *)

let MOI_S3SO_SIGN_DIV = prove
 (`!d e. ~(d = &0) /\ ~(e = &0) ==> (&0 < e <=> (&0 < d <=> &0 < e / d))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN
  SUBGOAL_THEN `e / d = --e / --d` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SO_HAS_SIZE3 = prove
 (`!a b c:real^N. ~collinear {a,b,c} ==> {a,b,c} HAS_SIZE 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3SO_NONCOL_FACTS) THEN
  STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Part 6: the planar sign of a map g from the plane into the surface.      *)
(* For a non-degenerate planar triangle (u,v,w) on which g is affine, the   *)
(* boolean (POS of the image <=> det u v w > 0) does not change when the    *)
(* triangle is replaced by a sub-triangle, nor across a common edge of two  *)
(* triangles of a refinement adapted to g and to the complex m.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_EPS_SUB = prove
 (`!(s:real^3->bool) i (g:real^2->real^3) l y u v w u' v' w'.
     moi_s3so_sided s i /\ linear l /\
     (!x. x IN convex hull {u,v,w} ==> g x = l x + y) /\
     IMAGE g (convex hull {u,v,w}) SUBSET s /\
     ~collinear {u,v,w} /\ ~collinear {g u,g v,g w} /\
     u' IN convex hull {u,v,w} /\ v' IN convex hull {u,v,w} /\
     w' IN convex hull {u,v,w} /\
     ~collinear {u',v',w'} /\ ~collinear {g u',g v',g w'}
     ==> ((moi_s3so_pos i (g u') (g v') (g w') <=> &0 < moi_s3so_det u' v' w') <=>
          (moi_s3so_pos i (g u) (g v) (g w) <=> &0 < moi_s3so_det u v w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2) IN convex hull {u,v,w} /\ v IN convex hull {u,v,w} /\
                w IN convex hull {u,v,w}` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) (convex hull {u,v,w}) = convex hull {g u,g v,g w}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^2->real^3`; `l:real^2->real^3`; `y:real^3`; `{u:real^2,v,w}`]
      MOI_S3SO_AFF_IMAGE_HULL) THEN
    ASM_SIMP_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r:real^2. p IN convex hull {u,v,w} /\ q IN convex hull {u,v,w} /\
                   r IN convex hull {u,v,w}
                   ==> ((g:real^2->real^3) q - g p) cross (g r - g p) =
                       moi_s3so_det p q r % ((l:real^2->real^3)(basis 1) cross l(basis 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3SO_AFF_CROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s3so_det u v w = &0) /\ ~(moi_s3so_det u' v' w' = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_COLLINEAR_DET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^2->real^3) v' - g u') cross (g w' - g u') =
    (moi_s3so_det u' v' w' / moi_s3so_det u v w) % ((g v - g u) cross (g w - g u))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_RMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `(g:real^2->real^3) u`;
                 `(g:real^2->real^3) v`; `(g:real^2->real^3) w`; `(g:real^2->real^3) u'`;
                 `(g:real^2->real^3) v'`; `(g:real^2->real^3) w'`;
                 `moi_s3so_det u' v' w' / moi_s3so_det u v w`] MOI_S3SO_SUBTRI_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^3) (convex hull {u,v,w}) SUBSET s` THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^3) (convex hull {u,v,w}) =
                 convex hull {g u,g v,g w}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(u':real^2) IN convex hull {u,v,w}` THEN
    UNDISCH_TAC `(v':real^2) IN convex hull {u,v,w}` THEN
    UNDISCH_TAC `(w':real^2) IN convex hull {u,v,w}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`moi_s3so_det u v w`; `moi_s3so_det u' v' w'`] MOI_S3SO_SIGN_DIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

let MOI_S3SO_M_DIM2 = prove
 (`!(m:(real^3->bool)->bool) t p q r.
     FINITE m /\ combinatorial_manifold 2 m /\ t IN m /\
     p IN t /\ q IN t /\ r IN t /\ ~collinear {p,q,r}
     ==> aff_dim t = &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3SO_M_TRI) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
    STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[MOI_S3SO_NONCOL_DIM]);;

(* Adjacent triangles of a refinement adapted to g and m. *)

let MOI_S3SO_EPS_ADJ = prove
 (`!(m:(real^3->bool)->bool) i (t:(real^2->bool)->bool) (g:real^2->real^3) u v w1 w2.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     simplicial_complex t /\
     (!s. s IN t ==> ?l y. linear l /\ !x. x IN s ==> g x = l x + y) /\
     (!s. s IN t /\ ~(s = {}) ==> ?k. k IN m /\ IMAGE g s SUBSET k) /\
     (!x x'. x IN UNIONS t /\ x' IN UNIONS t /\ g x = g x' ==> x = x') /\
     convex hull {u,v,w1} IN t /\ convex hull {u,v,w2} IN t /\
     ~collinear {u,v,w1} /\ ~collinear {u,v,w2} /\ ~(w1 = w2)
     ==> ((moi_s3so_pos i (g u) (g v) (g w2) <=> &0 < moi_s3so_det u v w2) <=>
          (moi_s3so_pos i (g u) (g v) (g w1) <=> &0 < moi_s3so_det u v w1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "img")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `u:real^2`; `v:real^2`; `w1:real^2`; `w2:real^2`]
    MOI_S3SO_OPP_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `convex hull {u:real^2,v,w1} IN t`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `convex hull {u:real^2,v,w2} IN t`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex hull {u:real^2,v,w1} SUBSET UNIONS t /\
                convex hull {u:real^2,v,w2} SUBSET UNIONS t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(x:real^2->bool) IN t ==> x SUBSET UNIONS t`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {(g:real^2->real^3) u,g v,g w1} /\
                ~collinear {(g:real^2->real^3) u,g v,g w2}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `y1:real^3`];
      MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `y2:real^3`]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  USE_THEN "img" (MP_TAC o SPEC `convex hull {u:real^2,v,w1}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "img" (MP_TAC o SPEC `convex hull {u:real^2,v,w2}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^2->real^3) u IN k1 /\ g v IN k1 /\ g w1 IN k1 /\
                g u IN k2 /\ g v IN k2 /\ g w2 IN k2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{u:real^2,v,w1}`] HULL_SUBSET) THEN
    MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{u:real^2,v,w2}`] HULL_SUBSET) THEN
    MP_TAC(ASSUME `IMAGE (g:real^2->real^3) (convex hull {u,v,w1}) SUBSET k1`) THEN
    MP_TAC(ASSUME `IMAGE (g:real^2->real^3) (convex hull {u,v,w2}) SUBSET k2`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(?x:real^3. x IN relative_interior(convex hull {(g:real^2->real^3) u,g v,g w1}) /\
                 x IN relative_interior(convex hull {g u,g v,g w2}))`
  ASSUME_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`g:real^2->real^3`; `l1:real^2->real^3`; `y1:real^3`; `u:real^2`;
                   `v:real^2`; `w1:real^2`; `z:real^3`] MOI_S3SO_AFF_RELINT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:real^2` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    MP_TAC(ISPECL [`g:real^2->real^3`; `l2:real^2->real^3`; `y2:real^3`; `u:real^2`;
                   `v:real^2`; `w2:real^2`; `z:real^3`] MOI_S3SO_AFF_RELINT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:real^2` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    SUBGOAL_THEN `q1:real^2 = q2` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `convex hull {u:real^2,v,w1}` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `convex hull {u:real^2,v,w2}` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `u:real^2`; `v:real^2`; `w1:real^2`; `w2:real^2`]
      MOI_S3SO_RELINT_DISJ) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3so_pos i ((g:real^2->real^3) u) (g v) (g w2) <=>
                ~moi_s3so_pos i (g u) (g v) (g w1)` ASSUME_TAC THENL
   [ASM_CASES_TAC `k1:real^3->bool = k2` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k2:real^3->bool`; `(g:real^2->real^3) u`;
                     `(g:real^2->real^3) v`; `(g:real^2->real^3) w1`] MOI_S3SO_M_TRI) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
      MATCH_MP_TAC MOI_S3SO_IM_SAME THEN
      MAP_EVERY EXISTS_TAC [`UNIONS m:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN m ==> x SUBSET UNIONS m`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(k1:real^3->bool) = &2 /\ aff_dim(k2:real^3->bool) = &2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_S3SO_M_DIM2 THEN
      EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^2->real^3) u = g v)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k1:real^3->bool`; `k2:real^3->bool`;
                   `(g:real^2->real^3) u`; `(g:real^2->real^3) v`] MOI_SCF_INTER_DIM1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(k1 INTER k2:real^3->bool) IN m` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k1 INTER k2:real^3->bool`] MOI_SCF_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `k1:real^3->bool`]
      MOI_SCF_TRIANGLE_ON_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `k2:real^3->bool`]
      MOI_SCF_TRIANGLE_ON_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S3SO_IM_ADJ THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                          `c':real^3`] THEN
    SUBGOAL_THEN `~collinear {a:real^3,b,c} /\ ~collinear {a:real^3,b,c'}` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(c:real^3 = c')` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(k1:real^3->bool = k2)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN
    UNDISCH_TAC `(k1:real^3->bool) = convex hull {a,b,c}` THEN
    UNDISCH_TAC `(k2:real^3->bool) = convex hull {a,b,c'}` THEN
    REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`moi_s3so_det u v w1`; `moi_s3so_det u v w2`] MOI_S3SO_SIGN_OPP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Part 7: sub-triangles.  A non-degenerate triangle covered by             *)
(* finitely many convex sets has a non-degenerate sub-triangle inside one   *)
(* of them (measure: finitely many convex sets with empty interior are      *)
(* negligible), first in the plane, then in real^3 through an affine chart  *)
(* of the plane of the triangle.  A PL map is affine on some sub-triangle   *)
(* of any triangle in its domain.  Side comparison of a triangle with its   *)
(* sub-triangles under a map that is affine on it.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_PLANAR_COVER = prove
 (`!(c:(real^2->bool)->bool) u v w.
     FINITE c /\ (!k. k IN c ==> convex k) /\ ~collinear {u,v,w} /\
     convex hull {u,v,w} SUBSET UNIONS c
     ==> ?k u' v' w'. k IN c /\ &0 < moi_s3so_det u' v' w' /\
                      convex hull {u',v',w'} SUBSET k INTER convex hull {u,v,w}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior(convex hull {u:real^2,v,w}) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{u:real^2,v,w}` INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
    ASM_SIMP_TAC[DIMINDEX_2; ARITH; MOI_S3SO_HAS_SIZE3] THEN
    ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k:real^2->bool. k IN c /\ ~(interior(k INTER convex hull {u,v,w}) = {})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
    SUBGOAL_THEN `negligible(convex hull {u:real^2,v,w})` MP_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `UNIONS (IMAGE (\k. k INTER convex hull {u:real^2,v,w}) c)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `k:real^2->bool` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_INTERIOR; CONVEX_INTER; CONVEX_CONVEX_HULL];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_INTERIOR; CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  UNDISCH_TAC `~(interior(k INTER convex hull {u:real^2,v,w}) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `x0:real^2`; `x0 + (r / &2) % basis 1:real^2`;
                        `x0 + (r / &2) % basis 2:real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s3so_det; VECTOR_ARITH `(x + y) - x:real^N = y`] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,r)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_BALL] THEN
  REWRITE_TAC[NORM_ARITH `dist(x:real^N,x) = &0`;
              NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SO_SPACE_COVER = prove
 (`!(cc:(real^3->bool)->bool) a b c.
     FINITE cc /\ (!k. k IN cc ==> convex k) /\ ~collinear {a,b,c} /\
     convex hull {a,b,c} SUBSET UNIONS cc
     ==> ?k a' b' c'. k IN cc /\ ~collinear {a',b',c'} /\
                      convex hull {a',b',c'} SUBSET k INTER convex hull {a,b,c}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `l = \x:real^2. x$1 % (b - a) + x$2 % (c - a:real^3)` THEN
  SUBGOAL_THEN `linear (l:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^2->real^3) (basis 1) = b - a /\ l (basis 2) = c - a /\
                l (vec 0) = vec 0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH; VEC_COMPONENT] THEN
    REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^2. (l:real^2->real^3) x + a)
                      (convex hull {vec 0,basis 1,basis 2}) = convex hull {a,b,c}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL; IMAGE_CLAUSES; VECTOR_ADD_LID;
                 VECTOR_SUB_ADD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\k. {x:real^2 | (l:real^2->real^3) x + a IN k})
                        (cc:(real^3->bool)->bool)`; `vec 0:real^2`; `basis 1:real^2`;
                 `basis 2:real^2`] MOI_S3SO_PLANAR_COVER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `{x:real^2 | (l:real^2->real^3) x + a IN k} =
                    {x | l x IN IMAGE (\z. --a + z) k}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
        MESON_TAC[VECTOR_ARITH `(y:real^3) = --a + z <=> z = y + a`];
        ALL_TAC] THEN
      MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN ASM_SIMP_TAC[CONVEX_TRANSLATION_EQ];
      REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; moi_s3so_det; VECTOR_SUB_RZERO] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      UNDISCH_TAC `convex hull {a:real^3,b,c} SUBSET UNIONS cc` THEN
      UNDISCH_TAC `IMAGE (\x:real^2. (l:real^2->real^3) x + a)
                         (convex hull {vec 0,basis 1,basis 2}) = convex hull {a,b,c}` THEN
      UNDISCH_TAC `(x:real^2) IN convex hull {vec 0,basis 1,basis 2}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':real^2->bool` (X_CHOOSE_THEN `u:real^2`
    (X_CHOOSE_THEN `v:real^2` (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)))) THEN
  UNDISCH_TAC `(k':real^2->bool) IN IMAGE (\k. {x:real^2 | (l:real^2->real^3) x + a IN k})
                                           (cc:(real^3->bool)->bool)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `(l:real^2->real^3) u + a`;
                        `(l:real^2->real^3) v + a`; `(l:real^2->real^3) w + a`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_S3SO_NONCOL_CROSS; MOI_S3SO_AFF_CROSS; VECTOR_MUL_EQ_0;
                 REAL_LT_IMP_NZ] THEN
    ASM_MESON_TAC[MOI_S3SO_NONCOL_CROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(l:real^2->real^3) u + a,l v + a,l w + a} =
                IMAGE (\x. l x + a) (convex hull {u,v,w})` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL; IMAGE_CLAUSES]; ALL_TAC] THEN
  UNDISCH_TAC `convex hull {u:real^2,v,w} SUBSET
               {x | (l:real^2->real^3) x + a IN k} INTER
               convex hull {vec 0,basis 1,basis 2}` THEN
  UNDISCH_TAC `IMAGE (\x:real^2. (l:real^2->real^3) x + a)
                     (convex hull {vec 0,basis 1,basis 2}) = convex hull {a,b,c}` THEN
  SET_TAC[]);;

(* A PL map is affine on a non-degenerate sub-triangle of any triangle in  *)
(* its domain (inside a small homothetic copy at a vertex).                 *)

let MOI_S3SO_PL_SUBTRI = prove
 (`!(A:real^3->bool) (h:real^3->real^N) a b c.
     pl_map_on A h /\ ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A
     ==> ?a' b' c' l y. ~collinear {a',b',c'} /\
                        convex hull {a',b',c'} SUBSET convex hull {a,b,c} /\
                        linear l /\ !x. x IN convex hull {a',b',c'} ==> h x = l x + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^3) IN convex hull {a,b,c}` ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  UNDISCH_TAC `pl_map_on (A:real^3->bool) (h:real^3->real^N)` THEN
  REWRITE_TAC[pl_map_on] THEN DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `u:real^3->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D = r + norm(b - a:real^3) + norm(c - a:real^3)` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MP_TAC(ISPEC `b - a:real^3` NORM_POS_LE) THEN
    MP_TAC(ISPEC `c - a:real^3` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ep = r / D` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * D = r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `ep * r + ep * norm(b - a:real^3) + ep * norm(c - a:real^3) = r /\
                &0 < ep * r /\ &0 <= ep * norm(b - a:real^3) /\
                &0 <= ep * norm(c - a:real^3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ep * D = r` THEN EXPAND_TAC "D" THEN REWRITE_TAC[REAL_ADD_LDISTRIB];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ep <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `ep * r <= &1 * r` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `b1 = a + ep % (b - a):real^3` THEN
  ABBREV_TAC `c1 = a + ep % (c - a):real^3` THEN
  SUBGOAL_THEN `convex hull {a:real^3,b1,c1} SUBSET convex hull {a,b,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET;
      EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["b1"; "c1"] THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 - ep`; `ep:real`; `&0`];
      MAP_EVERY EXISTS_TAC [`&1 - ep`; `&0`; `ep:real`]] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^3,b1,c1} SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET;
      EMPTY_SUBSET; IN_BALL] THEN
    MAP_EVERY EXPAND_TAC ["b1"; "c1"] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^N,x) = &0`;
                NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {a:real^3,b1,c1}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3SO_NONCOL_CROSS] THEN MAP_EVERY EXPAND_TAC ["b1"; "c1"] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^3 = x`; CROSS_LMUL; CROSS_RMUL;
                VECTOR_MUL_ASSOC; VECTOR_MUL_EQ_0; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[MOI_S3SO_NONCOL_CROSS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `a:real^3`; `b1:real^3`; `c1:real^3`]
    MOI_S3SO_SPACE_COVER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
    UNDISCH_TAC `A INTER u SUBSET UNIONS (cc:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `ball(a:real^3,r) SUBSET u` THEN
    UNDISCH_TAC `convex hull {a:real^3,b,c} SUBSET A` THEN
    UNDISCH_TAC `convex hull {a:real^3,b1,c1} SUBSET convex hull {a,b,c}` THEN
    UNDISCH_TAC `convex hull {a:real^3,b1,c1} SUBSET ball(a,r)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `a':real^3`
    (X_CHOOSE_THEN `b':real^3` (X_CHOOSE_THEN `c':real^3` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "k" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `l:real^3->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a':real^3`; `b':real^3`; `c':real^3`; `l:real^3->real^N`;
                        `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* Side comparison: a map affine on a triangle of s with image in s', and  *)
(* a sub-triangle with non-degenerate image.                                *)

let MOI_S3SO_SP_SUB = prove
 (`!(s:real^3->bool) i s' i' (f:real^3->real^3) l y a b c a' b' c'.
     moi_s3so_sided s i /\ moi_s3so_sided s' i' /\ linear l /\
     (!x. x IN convex hull {a,b,c} ==> f x = l x + y) /\
     convex hull {a,b,c} SUBSET s /\ IMAGE f (convex hull {a,b,c}) SUBSET s' /\
     ~collinear {a,b,c} /\ ~collinear {f a,f b,f c} /\
     a' IN convex hull {a,b,c} /\ b' IN convex hull {a,b,c} /\
     c' IN convex hull {a,b,c} /\
     ~collinear {a',b',c'} /\ ~collinear {f a',f b',f c'}
     ==> ((moi_s3so_pos i' (f a') (f b') (f c') <=> moi_s3so_pos i a' b' c') <=>
          (moi_s3so_pos i' (f a) (f b) (f c) <=> moi_s3so_pos i a b c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^3) IN convex hull {a,b,c} /\ b IN convex hull {a,b,c} /\
                c IN convex hull {a,b,c}` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (convex hull {a,b,c}) = convex hull {f a,f b,f c}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `l:real^3->real^3`; `y:real^3`; `{a:real^3,b,c}`]
      MOI_S3SO_AFF_IMAGE_HULL) THEN
    ASM_SIMP_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?lam. (b' - a') cross (c' - a') = lam % ((b - a) cross (c - a:real^3)) /\
          ((f:real^3->real^3) b' - f a') cross (f c' - f a') =
          lam % ((f b - f a) cross (f c - f a))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x:real^3. x IN convex hull {a,b,c}
                 ==> ?x1 x2. x = a + x1 % (b - a) + x2 % (c - a) /\
                             (f:real^3->real^3) x = f a + x1 % (f b - f a) + x2 % (f c - f a)`
    (LABEL_TAC "co") THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?x1 x2. x = a + x1 % (b - a) + x2 % (c - a:real^3)` MP_TAC THENL
       [REWRITE_TAC[GSYM MOI_S3SO_IN_PLANE] THEN
        ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
        ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN DISCH_TAC THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th;
                                        MATCH_MP LINEAR_SUB th]) THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "co" (MP_TAC o C MATCH_MP (ASSUME `(a':real^3) IN convex hull {a,b,c}`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real` (X_CHOOSE_THEN `p2:real` (CONJUNCTS_THEN ASSUME_TAC))) THEN
    USE_THEN "co" (MP_TAC o C MATCH_MP (ASSUME `(b':real^3) IN convex hull {a,b,c}`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:real` (X_CHOOSE_THEN `q2:real` (CONJUNCTS_THEN ASSUME_TAC))) THEN
    USE_THEN "co" (MP_TAC o C MATCH_MP (ASSUME `(c':real^3) IN convex hull {a,b,c}`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN ASSUME_TAC))) THEN
    EXISTS_TAC `(q1 - p1) * (r2 - p2) - (q2 - p2) * (r1 - p1)` THEN
    ASM_REWRITE_TAC[MOI_S3SO_PLANE_CROSS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `i:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                 `a':real^3`; `b':real^3`; `c':real^3`; `lam:real`] MOI_S3SO_SUBTRI_POS) THEN
  MP_TAC(ISPECL [`s':real^3->bool`; `i':real^3->bool`; `(f:real^3->real^3) a`;
                 `(f:real^3->real^3) b`; `(f:real^3->real^3) c`; `(f:real^3->real^3) a'`;
                 `(f:real^3->real^3) b'`; `(f:real^3->real^3) c'`; `lam:real`]
    MOI_S3SO_SUBTRI_POS) THEN
  SUBGOAL_THEN `convex hull {(f:real^3->real^3) a,f b,f c} SUBSET s' /\
                f a' IN convex hull {f a,f b,f c} /\ f b' IN convex hull {f a,f b,f c} /\
                f c' IN convex hull {f a,f b,f c}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) (convex hull {a,b,c}) SUBSET s'` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (convex hull {a,b,c}) =
                 convex hull {f a,f b,f c}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(a':real^3) IN convex hull {a,b,c}` THEN
    UNDISCH_TAC `(b':real^3) IN convex hull {a,b,c}` THEN
    UNDISCH_TAC `(c':real^3) IN convex hull {a,b,c}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Part 8: the planar sign of a PL embedding of the holed disk model        *)
(* into a two-sided surface is constant: one boolean b such that for every  *)
(* non-degenerate planar triangle on which the map is affine, POS of the    *)
(* image triangle holds iff (det > 0 <=> b).  Proof: a refinement t of a    *)
(* triangulation of the model adapted to the map and to m; its triangles   *)
(* form an edge-connected family (MOI_FSB_ABS_DCONN), the sign is constant  *)
(* across common edges (EPS_ADJ) and under sub-triangles (EPS_SUB2), and    *)
(* every triangle shares a sub-triangle with a triangle of t.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_SIZE3_EDGE = prove
 (`!(V:A->bool) x y. V HAS_SIZE 3 /\ x IN V /\ y IN V /\ ~(x = y)
     ==> ?z. V = {x,y,z} /\ ~(z = x) /\ ~(z = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V DIFF {x:A,y}) HAS_SIZE 1` MP_TAC THENL
   [UNDISCH_TAC `(V:A->bool) HAS_SIZE 3` THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FINITE_DIFF; CARD_DIFF; INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:A`) THEN EXISTS_TAC `z:A` THEN
  UNDISCH_TAC `(V DIFF {x:A,y}) = {z}` THEN
  UNDISCH_TAC `(x:A) IN V` THEN UNDISCH_TAC `(y:A) IN V` THEN SET_TAC[]);;

let MOI_S3SO_VS_FACTS = prove
 (`!(t:(real^N->bool)->bool) s.
     simplicial_complex t /\ s IN t /\ aff_dim s = &2
     ==> moi_fsa_vs s HAS_SIZE 3 /\ ~affine_dependent (moi_fsa_vs s) /\
         convex hull (moi_fsa_vs s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  UNDISCH_TAC `&(CARD (moi_fsa_vs (s:real^N->bool))):int = &2 + &1` THEN
  REWRITE_TAC[INT_ARITH `&2 + &1:int = &3`; INT_OF_NUM_EQ]);;

let MOI_S3SO_VS_HULL3 = prove
 (`!u v w:real^N. ~collinear {u,v,w} ==> moi_fsa_vs (convex hull {u,v,w}) = {u,v,w}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_vs; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT THEN
  ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]);;

(* The sign under sub-triangles, for an injective map on a domain D.       *)

let MOI_S3SO_EPS_SUB2 = prove
 (`!(s:real^3->bool) i (g:real^2->real^3) D l y u v w u' v' w'.
     moi_s3so_sided s i /\ IMAGE g D SUBSET s /\
     (!x x'. x IN D /\ x' IN D /\ g x = g x' ==> x = x') /\
     linear l /\ (!x. x IN convex hull {u,v,w} ==> g x = l x + y) /\
     convex hull {u,v,w} SUBSET D /\ ~collinear {u,v,w} /\
     u' IN convex hull {u,v,w} /\ v' IN convex hull {u,v,w} /\
     w' IN convex hull {u,v,w} /\ ~collinear {u',v',w'}
     ==> ((moi_s3so_pos i (g u') (g v') (g w') <=> &0 < moi_s3so_det u' v' w') <=>
          (moi_s3so_pos i (g u) (g v) (g w) <=> &0 < moi_s3so_det u v w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {u':real^2,v',w'} SUBSET convex hull {u,v,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3SO_EPS_SUB THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `l:real^2->real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET]]);;

(* All triangles of an edge-connected refinement have the same sign. *)

let MOI_S3SO_EPS_T_CONST = prove
 (`!(m:(real^3->bool)->bool) i (t:(real^2->bool)->bool) (g:real^2->real^3).
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     simplicial_complex t /\ FINITE t /\ combinatorial_manifold_with_boundary 2 t /\
     connected (UNIONS t) /\
     (!s. s IN t ==> ?l y. linear l /\ !x. x IN s ==> g x = l x + y) /\
     (!s. s IN t /\ ~(s = {}) ==> ?k. k IN m /\ IMAGE g s SUBSET k) /\
     (!x x'. x IN UNIONS t /\ x' IN UNIONS t /\ g x = g x' ==> x = x')
     ==> !u1 v1 w1 u2 v2 w2.
           convex hull {u1,v1,w1} IN t /\ ~collinear {u1,v1,w1} /\
           convex hull {u2,v2,w2} IN t /\ ~collinear {u2,v2,w2}
           ==> ((moi_s3so_pos i (g u2) (g v2) (g w2) <=> &0 < moi_s3so_det u2 v2 w2) <=>
                (moi_s3so_pos i (g u1) (g v1) (g w1) <=> &0 < moi_s3so_det u1 v1 w1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "inj")))))))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) (UNIONS t) SUBSET UNIONS m` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "img" (MP_TAC o SPEC `s:real^2->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v w u' v' w'.
       convex hull {u,v,w} IN t /\ ~collinear {u,v,w} /\
       u' IN convex hull {u,v,w} /\ v' IN convex hull {u,v,w} /\
       w' IN convex hull {u,v,w} /\ ~collinear {u',v',w'}
       ==> ((moi_s3so_pos i ((g:real^2->real^3) u') (g v') (g w') <=>
             &0 < moi_s3so_det u' v' w') <=>
            (moi_s3so_pos i (g u) (g v) (g w) <=> &0 < moi_s3so_det u v w))`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `convex hull {u:real^2,v,w} IN t`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S3SO_EPS_SUB2 THEN
    MAP_EVERY EXISTS_TAC [`UNIONS m:real^3->bool`; `UNIONS t:real^2->bool`;
                          `l:real^2->real^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^2->bool) IN t ==> x SUBSET UNIONS t`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v w:real^2. convex hull {u,v,w} IN t /\ ~collinear {u,v,w}
                               ==> {u,v,w} IN moi_fsa_abs t`
  (LABEL_TAC "abs") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull {u:real^2,v,w}` THEN
    ASM_SIMP_TAC[MOI_S3SO_NONCOL_DIM; MOI_S3SO_VS_HULL3];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_dconn (moi_fsa_abs (t:(real^2->bool)->bool))` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSB_ABS_DCONN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_dconn] THEN
  DISCH_THEN(MP_TAC o SPEC
    `{V | V IN moi_fsa_abs (t:(real^2->bool)->bool) /\
          !u v w. V = {u,v,w} /\ ~collinear {u,v,w}
                  ==> ((moi_s3so_pos i ((g:real^2->real^3) u) (g v) (g w) <=>
                        &0 < moi_s3so_det u v w) <=>
                       (moi_s3so_pos i (g u1) (g v1) (g w1) <=>
                        &0 < moi_s3so_det u1 v1 w1))}`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `{u1:real^2,v1,w1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [USE_THEN "abs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`; `w:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(u:real^2) IN convex hull {u1,v1,w1} /\ v IN convex hull {u1,v1,w1} /\
                    w IN convex hull {u1,v1,w1}` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{u1:real^2,v1,w1}`] HULL_SUBSET) THEN
        UNDISCH_TAC `{u1:real^2,v1,w1} = {u,v,w}` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`V:real^2->bool`; `V':real^2->bool`; `e:real^2->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "VX"))
      STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^2->bool) HAS_SIZE 2` THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `y:real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
    UNDISCH_TAC `(V:real^2->bool) IN moi_fsa_abs t` THEN
    REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^2->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `V:real^2->bool`)) THEN
    UNDISCH_TAC `(V':real^2->bool) IN moi_fsa_abs t` THEN
    REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real^2->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `V':real^2->bool`)) THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `s1:real^2->bool`] MOI_S3SO_VS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `s2:real^2->bool`] MOI_S3SO_VS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_fsa_vs (s1:real^2->bool)`; `x:real^2`; `y:real^2`]
      MOI_S3SO_SIZE3_EDGE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`moi_fsa_vs (s2:real^2->bool)`; `x:real^2`; `y:real^2`]
      MOI_S3SO_SIZE3_EDGE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z2:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~collinear {x:real^2,y,z1} /\ ~collinear {x:real^2,y,z2} /\
                  convex hull {x:real^2,y,z1} IN t /\ convex hull {x:real^2,y,z2} IN t`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`; `w:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^2) IN convex hull {x,y,z2} /\ v IN convex hull {x,y,z2} /\
                  w IN convex hull {x,y,z2}` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{x:real^2,y,z2}`] HULL_SUBSET) THEN
      UNDISCH_TAC `moi_fsa_vs (s2:real^2->bool) = {u,v,w}` THEN
      UNDISCH_TAC `moi_fsa_vs (s2:real^2->bool) = {x,y,z2}` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "sub" (MP_TAC o SPECL [`x:real^2`; `y:real^2`; `z2:real^2`; `u:real^2`;
                                    `v:real^2`; `w:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_CASES_TAC `z1:real^2 = z2` THENL
     [USE_THEN "VX" (MP_TAC o SPECL [`x:real^2`; `y:real^2`; `z2:real^2`]) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `t:(real^2->bool)->bool`;
                   `g:real^2->real^3`; `x:real^2`; `y:real^2`; `z1:real^2`; `z2:real^2`]
      MOI_S3SO_EPS_ADJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "VX" (MP_TAC o SPECL [`x:real^2`; `y:real^2`; `z1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `{u2:real^2,v2,w2} IN moi_fsa_abs t` MP_TAC THENL
   [USE_THEN "abs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`u2:real^2`; `v2:real^2`; `w2:real^2`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* The planar sign of a PL embedding of the holed disk model. *)

let MOI_S3SO_MODEL_SIGN = prove
 (`!(m:(real^3->bool)->bool) i k (g:real^2->real^3).
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     pl_map_on (holed_disk_model k) g /\ IMAGE g (holed_disk_model k) SUBSET UNIONS m /\
     (!x x'. x IN holed_disk_model k /\ x' IN holed_disk_model k /\ g x = g x' ==> x = x')
     ==> ?b. !u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                         linear l /\ (!x. x IN convex hull {u,v,w} ==> g x = l x + y)
                         ==> ((moi_s3so_pos i (g u) (g v) (g w) <=>
                               &0 < moi_s3so_det u v w) <=> b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(CONJUNCT1(SPEC `k:num` MOI_FSB_HD_POLY)) THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^2->bool)->bool`; `m:(real^3->bool)->bool`; `g:real^2->real^3`]
    MOI_S3SO_REFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS t = holed_disk_model k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `t:(real^2->bool)->bool`] MOI_S3KC_HD_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `t:(real^2->bool)->bool`;
                 `g:real^2->real^3`] MOI_S3SO_EPS_T_CONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MOI_S3KC_HD_CONNECTED]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "const") THEN
  SUBGOAL_THEN
   `!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                linear l /\ (!x. x IN convex hull {u,v,w} ==> (g:real^2->real^3) x = l x + y)
                ==> ?u0 v0 w0. convex hull {u0,v0,w0} IN t /\ ~collinear {u0,v0,w0} /\
                      ((moi_s3so_pos i (g u) (g v) (g w) <=> &0 < moi_s3so_det u v w) <=>
                       (moi_s3so_pos i (g u0) (g v0) (g w0) <=> &0 < moi_s3so_det u0 v0 w0))`
  (LABEL_TAC "B") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `u:real^2`; `v:real^2`; `w:real^2`]
      MOI_S3SO_PLANAR_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (X_CHOOSE_THEN `u':real^2`
      (X_CHOOSE_THEN `v':real^2` (X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `~collinear {u':real^2,v',w'}` ASSUME_TAC THENL
     [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(u':real^2) IN s /\ v' IN s /\ w' IN s /\
                  u' IN convex hull {u,v,w} /\ v' IN convex hull {u,v,w} /\
                  w' IN convex hull {u,v,w}` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{u':real^2,v',w'}`] HULL_SUBSET) THEN
      UNDISCH_TAC `convex hull {u':real^2,v',w'} SUBSET s INTER convex hull {u,v,w}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^2->bool) = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(INT_ARITH `a <= &2 /\ &2 <= a ==> a:int = &2`) THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `s:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2];
        MP_TAC(ISPECL [`u':real^2`; `v':real^2`; `w':real^2`] MOI_S3SO_NONCOL_DIM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `s:real^2->bool`] MOI_S3SO_VS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `u0:real^2` (X_CHOOSE_THEN `v0:real^2` (X_CHOOSE_THEN `w0:real^2`
      STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `convex hull {u0:real^2,v0,w0} = s /\ ~collinear {u0:real^2,v0,w0}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[];
        REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u0:real^2`; `v0:real^2`; `w0:real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real^2->bool) IN t`) o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "s" &&
          is_exists(rand(snd(dest_forall(concl th)))) with Failure _ -> false)) THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:real^2->real^3` (X_CHOOSE_THEN `y0:real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `g:real^2->real^3`;
                   `holed_disk_model k`; `l:real^2->real^3`; `y:real^3`; `u:real^2`;
                   `v:real^2`; `w:real^2`; `u':real^2`; `v':real^2`; `w':real^2`]
      MOI_S3SO_EPS_SUB2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `g:real^2->real^3`;
                   `holed_disk_model k`; `l0:real^2->real^3`; `y0:real^3`; `u0:real^2`;
                   `v0:real^2`; `w0:real^2`; `u':real^2`; `v':real^2`; `w':real^2`]
      MOI_S3SO_EPS_SUB2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      CONV_TAC TAUT];
    ALL_TAC] THEN
  ASM_CASES_TAC `?u0 v0 w0:real^2. convex hull {u0,v0,w0} IN t /\ ~collinear {u0,v0,w0}`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `u0:real^2` (X_CHOOSE_THEN `v0:real^2`
      (X_CHOOSE_THEN `w0:real^2` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `moi_s3so_pos i ((g:real^2->real^3) u0) (g v0) (g w0) <=>
                &0 < moi_s3so_det u0 v0 w0` THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "B" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l:real^2->real^3`;
                                  `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^2` (X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `w1:real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
    USE_THEN "const" (MP_TAC o SPECL [`u0:real^2`; `v0:real^2`; `w0:real^2`; `u1:real^2`;
                                      `v1:real^2`; `w1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC TAUT;
    EXISTS_TAC `T` THEN REPEAT STRIP_TAC THEN
    USE_THEN "B" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l:real^2->real^3`;
                                  `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 9: DICHOT.  A map phi of a piece A of the surface (A = G(model)      *)
(* for a PL embedding G of the holed disk model) is side-preserving when    *)
(* phi o G has the same planar sign as G (SP_CRIT: reduce a triangle to a   *)
(* sub-triangle on which G' is affine, then compare both signs on its       *)
(* planar preimage).  The model reflection y |-> 4 - y negates the planar   *)
(* sign, so f or f o G o refl o G' is side-preserving.                       *)
(* ------------------------------------------------------------------------- *)

let moi_s3so_sp = new_definition
 `moi_s3so_sp (i:real^3->bool) (i':real^3->bool) (A:real^3->bool) (f:real^3->real^3) <=>
    !a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
            (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                     ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c) /\
            ~collinear {f a,f b,f c}
            ==> (moi_s3so_pos i' (f a) (f b) (f c) <=> moi_s3so_pos i a b c)`;;

let moi_s3so_refl = new_definition
 `moi_s3so_refl (x:real^2) = vector[x$1; &4 - x$2]:real^2`;;

let MOI_S3SO_REFL_INVOL = prove
 (`!x. moi_s3so_refl(moi_s3so_refl x) = x`,
  REWRITE_TAC[moi_s3so_refl; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S3SO_REFL_AFF = prove
 (`?R. linear R /\ !x. moi_s3so_refl x = R x + vector[&0; &4]`,
  EXISTS_TAC `\x:real^2. vector[x$1; --(x$2)]:real^2` THEN
  REWRITE_TAC[linear; moi_s3so_refl; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_S3SO_REFL_MODEL = prove
 (`!k x. x IN holed_disk_model k ==> moi_s3so_refl x IN holed_disk_model k`,
  REWRITE_TAC[MOI_S3KC_IN_HD; moi_s3so_refl; VECTOR_2] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SO_REFL_DET = prove
 (`!u v w. moi_s3so_det (moi_s3so_refl u) (moi_s3so_refl v) (moi_s3so_refl w) =
           --(moi_s3so_det u v w)`,
  REWRITE_TAC[moi_s3so_det; moi_s3so_refl; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  CONV_TAC REAL_RING);;

(* A sign constant for h gives the opposite constant for h o refl. *)

let MOI_S3SO_REFL_SIGN = prove
 (`!(i':real^3->bool) k (h:real^2->real^3) bH.
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> h x = l x + y)
                  ==> ((moi_s3so_pos i' (h u) (h v) (h w) <=> &0 < moi_s3so_det u v w) <=>
                       bH))
     ==> (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                      linear l /\ (!x. x IN convex hull {u,v,w} ==> h(moi_s3so_refl x) = l x + y)
                      ==> ((moi_s3so_pos i' (h(moi_s3so_refl u)) (h(moi_s3so_refl v))
                              (h(moi_s3so_refl w)) <=> &0 < moi_s3so_det u v w) <=> ~bH))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "s") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hr")))) THEN
  X_CHOOSE_THEN `R:real^2->real^2` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Raff"))
    MOI_S3SO_REFL_AFF THEN
  SUBGOAL_THEN `IMAGE moi_s3so_refl (convex hull {u,v,w}) =
                convex hull {moi_s3so_refl u,moi_s3so_refl v,moi_s3so_refl w}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s3so_refl`; `R:real^2->real^2`; `vector[&0; &4]:real^2`;
                   `{u:real^2,v,w}`] MOI_S3SO_AFF_IMAGE_HULL) THEN
    USE_THEN "Raff" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    USE_THEN "Raff" (fun th -> REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s3so_det u v w = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_COLLINEAR_DET]; ALL_TAC] THEN
  USE_THEN "s" (MP_TAC o SPECL [`moi_s3so_refl u`; `moi_s3so_refl v`; `moi_s3so_refl w`;
                                `(l:real^2->real^3) o (R:real^2->real^2)`;
                                `(l:real^2->real^3)(vector[&0; &4]) + y`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; MOI_S3SO_REFL_DET] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `IMAGE moi_s3so_refl (convex hull {u,v,w}) =
                convex hull {moi_s3so_refl u,moi_s3so_refl v,moi_s3so_refl w}`)] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[SUBSET; MOI_S3SO_REFL_MODEL];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "hr" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM; VECTOR_ADD_ASSOC] THEN
    REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD (ASSUME `linear (l:real^2->real^3)`))] THEN
    USE_THEN "Raff" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[MOI_S3SO_REFL_INVOL];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S3SO_REFL_DET] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(d = &0) ==> (&0 < --d <=> ~(&0 < d))`] THEN
  CONV_TAC TAUT);;

let MOI_S3SO_PLH_FACTS = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g)
     ==> pl_map_on s f /\ pl_map_on t g /\ IMAGE f s = t /\ IMAGE g t = s /\
         (!x. x IN s ==> f x IN t) /\ (!x. x IN s ==> g(f x) = x) /\
         (!y. y IN t ==> g y IN s) /\ (!y. y IN t ==> f(g y) = y) /\
         (!x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x')`,
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The criterion: equal planar signs of G and phi o G give side            *)
(* preservation of phi on A = G(model).                                     *)

let MOI_S3SO_SP_CRIT = prove
 (`!(m:(real^3->bool)->bool) m' i i' k (G:real^2->real^3) G' (A:real^3->bool) A'
    (phi:real^3->real^3) bb.
     moi_s3so_sided (UNIONS m) i /\ moi_s3so_sided (UNIONS m') i' /\
     A SUBSET UNIONS m /\ A' SUBSET UNIONS m' /\
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     (!x. x IN A ==> phi x IN A') /\
     (!x x'. x IN A /\ x' IN A /\ phi x = phi x' ==> x = x') /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G x = l x + y)
                  ==> ((moi_s3so_pos i (G u) (G v) (G w) <=> &0 < moi_s3so_det u v w) <=>
                       bb)) /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> phi(G x) = l x + y)
                  ==> ((moi_s3so_pos i' (phi(G u)) (phi(G v)) (phi(G w)) <=>
                        &0 < moi_s3so_det u v w) <=> bb))
     ==> moi_s3so_sp i i' A phi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MOI_S3SO_PLH_FACTS)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pinj")
    (CONJUNCTS_THEN2 (LABEL_TAC "sG") (LABEL_TAC "sH"))))))))) THEN
  REWRITE_TAC[moi_s3so_sp] THEN MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `c:real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bary") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `a:real^3`; `b:real^3`; `c:real^3`] MOI_S3SO_BARY_AFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lf:real^3->real^3` (X_CHOOSE_THEN `yf:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `G':real^3->real^2`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_S3SO_PL_SUBTRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real^3` (X_CHOOSE_THEN `b':real^3` (X_CHOOSE_THEN `c':real^3`
    (X_CHOOSE_THEN `l0:real^3->real^2` (X_CHOOSE_THEN `y0:real^2` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(a':real^3) IN convex hull {a,b,c} /\ b' IN convex hull {a,b,c} /\
                c' IN convex hull {a,b,c}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{a':real^3,b',c'}`] HULL_SUBSET) THEN
    UNDISCH_TAC `convex hull {a':real^3,b',c'} SUBSET convex hull {a,b,c}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a':real^3,b',c'} SUBSET A` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {(phi:real^3->real^3) a',phi b',phi c'}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`lf:real^3->real^3`; `yf:real^3`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "pinj" MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET UNIONS m /\
                IMAGE (phi:real^3->real^3) (convex hull {a,b,c}) SUBSET UNIONS m'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS m:real^3->bool`; `i:real^3->bool`; `UNIONS m':real^3->bool`;
                 `i':real^3->bool`; `phi:real^3->real^3`; `lf:real^3->real^3`; `yf:real^3`;
                 `a:real^3`; `b:real^3`; `c:real^3`; `a':real^3`; `b':real^3`; `c':real^3`]
    MOI_S3SO_SP_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`G':real^3->real^2`; `G:real^2->real^3`; `l0:real^3->real^2`; `y0:real^2`;
                 `a':real^3`; `b':real^3`; `c':real^3`] MOI_S3SO_INV_AFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!x. x IN convex hull {(G':real^3->real^2) a',G' b',G' c'}
                    ==> (G:real^2->real^3) x IN convex hull {a',b',c'}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `IMAGE (G':real^3->real^2) (convex hull {a',b',c'}) =
                             convex hull {G' a',G' b',G' c'}`)] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(G':real^3->real^2) a',G' b',G' c'} SUBSET holed_disk_model k`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `IMAGE (G':real^3->real^2) (convex hull {a',b',c'}) =
                             convex hull {G' a',G' b',G' c'}`)] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  USE_THEN "sG" (MP_TAC o SPECL [`(G':real^3->real^2) a'`; `(G':real^3->real^2) b'`;
                                 `(G':real^3->real^2) c'`; `l1:real^2->real^3`; `y1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sH" (MP_TAC o SPECL [`(G':real^3->real^2) a'`; `(G':real^3->real^2) b'`;
                                 `(G':real^3->real^2) c'`;
                                 `(lf:real^3->real^3) o (l1:real^2->real^3)`;
                                 `(lf:real^3->real^3) y1 + yf`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G:real^2->real^3) x IN convex hull {a,b,c} /\ G x = l1 x + y1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3)((G:real^2->real^3) x) = lf(G x) + yf` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (lf:real^3->real^3)`)] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^3)(G' a') = a' /\ G(G' b') = b' /\ G(G' c') = c'`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  CONV_TAC TAUT);;

let MOI_S3SO_DICHOT_INT = prove
 (`!(m:(real^3->bool)->bool) m' i i' k (G:real^2->real^3) G' (A:real^3->bool) A'
    (f:real^3->real^3) f' (r:real^3->real^3).
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     FINITE m' /\ combinatorial_manifold 2 m' /\ moi_s3so_sided (UNIONS m') i' /\
     A SUBSET UNIONS m /\ A' SUBSET UNIONS m' /\
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\ pl_homeomorphism (A,A') (f,f') /\
     (!x. r x = f (G (moi_s3so_refl (G' x))))
     ==> moi_s3so_sp i i' A f \/ moi_s3so_sp i i' A r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (holed_disk_model k,A')
                  ((f:real^3->real^3) o (G:real^2->real^3),
                   (G':real^3->real^2) o (f':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A:real^3->bool`; `G:real^2->real^3`;
                 `G':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `A':real^3->bool`; `f:real^3->real^3`;
                 `f':real^3->real^3`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A':real^3->bool`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `(G':real^3->real^2) o (f':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k:num`; `G:real^2->real^3`]
    MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bG:bool` (LABEL_TAC "sG")) THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k:num`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`] MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bH:bool` (LABEL_TAC "sH")) THEN
  ASM_CASES_TAC `bH:bool = bG` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC MOI_S3SO_SP_CRIT THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `k:num`;
                          `G:real^2->real^3`; `G':real^3->real^2`; `A':real^3->bool`;
                          `bG:bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `!x. x IN holed_disk_model k
                    ==> (r:real^3->real^3) (G x) = f (G (moi_s3so_refl x))`
  (LABEL_TAC "rG") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN A ==> (r:real^3->real^3) x IN A'` (LABEL_TAC "rin") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S3SO_REFL_MODEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN A /\ x' IN A /\ (r:real^3->real^3) x = r x' ==> x = x'`
  (LABEL_TAC "rinj") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G':real^3->real^2) x IN holed_disk_model k /\
                  G' x' IN holed_disk_model k` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(G:real^2->real^3)(moi_s3so_refl((G':real^3->real^2) x)) =
                  G(moi_s3so_refl(G' x'))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(r:real^3->real^3) x = r x'` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_S3SO_REFL_MODEL];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s3so_refl((G':real^3->real^2) x) = moi_s3so_refl(G' x')` MP_TAC THENL
     [ASM_MESON_TAC[MOI_S3SO_REFL_MODEL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `moi_s3so_refl`) THEN REWRITE_TAC[MOI_S3SO_REFL_INVOL] THEN
    DISCH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i':real^3->bool`; `k:num`; `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `bH:bool`] MOI_S3SO_REFL_SIGN) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [USE_THEN "sH" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "sR") THEN
  UNDISCH_THEN `!x. (r:real^3->real^3) x =
                    (f:real^3->real^3) ((G:real^2->real^3) (moi_s3so_refl (G' x)))`
    (K ALL_TAC) THEN
  MATCH_MP_TAC MOI_S3SO_SP_CRIT THEN
  MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `k:num`;
                        `G:real^2->real^3`; `G':real^3->real^2`; `A':real^3->bool`;
                        `bG:bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2) IN holed_disk_model k /\ v IN holed_disk_model k /\
                w IN holed_disk_model k` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{u:real^2,v,w}`] HULL_SUBSET) THEN
    UNDISCH_TAC `convex hull {u:real^2,v,w} SUBSET holed_disk_model k` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "rG" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u:real^2) IN holed_disk_model k`);
                                     MATCH_MP th (ASSUME `(v:real^2) IN holed_disk_model k`);
                                     MATCH_MP th (ASSUME `(w:real^2) IN holed_disk_model k`)]) THEN
  SUBGOAL_THEN `bG <=> ~bH` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "sR" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN holed_disk_model k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "rG" (MP_TAC o C MATCH_MP (ASSUME `(z:real^2) IN holed_disk_model k`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* O3 DICHOT: the statement MOI_S3MT_SORIENT_DICHOT_TERM. *)

let MOI_S3SO_DICHOT = prove
 (MOI_S3MT_SORIENT_DICHOT_TERM,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "e'") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_s3so_sided s i /\ moi_s3so_sided s' i'` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3so_sided] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (let l = lhs(concl th) in is_comb l && fst(dest_const(rator l)) = "UNIONS")))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `i:real^3->bool`;
                 `i':real^3->bool`; `k:num`; `G:real^2->real^3`; `G':real^3->real^2`;
                 `A:real^3->bool`; `A':real^3->bool`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `r:real^3->real^3`] MOI_S3SO_DICHOT_INT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s3so_refl]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_sp; moi_s3so_pos]);;

(* ------------------------------------------------------------------------- *)
(* Part 10: CONST.  Near any point of the model there is a small            *)
(* non-degenerate triangle on which three given PL maps are affine; on such *)
(* a triangle inside G^-1(U) the maps f o G and g o G agree, so they have   *)
(* the same planar sign, and side preservation of g forces that sign to be  *)
(* the sign of G.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_PL_SUBTRI2 = prove
 (`!(D:real^2->bool) (h:real^2->real^N) u v w.
     pl_map_on D h /\ ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET D
     ==> ?u' v' w' l y. ~collinear {u',v',w'} /\
                        convex hull {u',v',w'} SUBSET convex hull {u,v,w} /\
                        linear l /\ !x. x IN convex hull {u',v',w'} ==> h x = l x + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2) IN convex hull {u,v,w}` ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  UNDISCH_TAC `pl_map_on (D:real^2->bool) (h:real^2->real^N)` THEN
  REWRITE_TAC[pl_map_on] THEN DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^2->bool)->bool` (X_CHOOSE_THEN `U:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `U:real^2->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D0 = r + norm(v - u:real^2) + norm(w - u:real^2)` THEN
  SUBGOAL_THEN `&0 < D0` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MP_TAC(ISPEC `v - u:real^2` NORM_POS_LE) THEN
    MP_TAC(ISPEC `w - u:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ep = r / D0` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * D0 = r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `ep * r + ep * norm(v - u:real^2) + ep * norm(w - u:real^2) = r /\
                &0 < ep * r /\ &0 <= ep * norm(v - u:real^2) /\
                &0 <= ep * norm(w - u:real^2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ep * D0 = r` THEN EXPAND_TAC "D0" THEN REWRITE_TAC[REAL_ADD_LDISTRIB];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ep <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `ep * r <= &1 * r` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `v1 = u + ep % (v - u):real^2` THEN
  ABBREV_TAC `w1 = u + ep % (w - u):real^2` THEN
  SUBGOAL_THEN `convex hull {u:real^2,v1,w1} SUBSET convex hull {u,v,w}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET;
      EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["v1"; "w1"] THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 - ep`; `ep:real`; `&0`];
      MAP_EVERY EXISTS_TAC [`&1 - ep`; `&0`; `ep:real`]] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {u:real^2,v1,w1} SUBSET ball(u,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET;
      EMPTY_SUBSET; IN_BALL] THEN
    MAP_EVERY EXPAND_TAC ["v1"; "w1"] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^N,x) = &0`;
                NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {u:real^2,v1,w1}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET] THEN MAP_EVERY EXPAND_TAC ["v1"; "w1"] THEN
    SUBGOAL_THEN `moi_s3so_det u (u + ep % (v - u)) (u + ep % (w - u)) =
                  (ep * ep) * moi_s3so_det u v w` SUBST1_TAC THENL
     [REWRITE_TAC[moi_s3so_det; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[MOI_S3SO_COLLINEAR_DET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `u:real^2`; `v1:real^2`; `w1:real^2`]
    MOI_S3SO_PLANAR_COVER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
    UNDISCH_TAC `D INTER U SUBSET UNIONS (cc:(real^2->bool)->bool)` THEN
    UNDISCH_TAC `ball(u:real^2,r) SUBSET U` THEN
    UNDISCH_TAC `convex hull {u:real^2,v,w} SUBSET D` THEN
    UNDISCH_TAC `convex hull {u:real^2,v1,w1} SUBSET convex hull {u,v,w}` THEN
    UNDISCH_TAC `convex hull {u:real^2,v1,w1} SUBSET ball(u,r)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `u':real^2`
    (X_CHOOSE_THEN `v':real^2` (X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2->bool` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "k" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`u':real^2`; `v':real^2`; `w':real^2`; `l:real^2->real^N`;
                        `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET] THEN ASM_REAL_ARITH_TAC;
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* A small triangle of the model near z0, mapped by G into U, on which G,   *)
(* h1 and h2 are affine.                                                     *)

let MOI_S3SO_TRI_NEAR = prove
 (`!k (G:real^2->real^3) (h1:real^2->real^3) (h2:real^2->real^3) U z0.
     pl_map_on (holed_disk_model k) G /\ pl_map_on (holed_disk_model k) h1 /\
     pl_map_on (holed_disk_model k) h2 /\
     open U /\ z0 IN holed_disk_model k /\ G z0 IN U
     ==> ?u v w l y l1 y1 l2 y2.
           ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
           IMAGE G (convex hull {u,v,w}) SUBSET U /\
           linear l /\ (!x. x IN convex hull {u,v,w} ==> G x = l x + y) /\
           linear l1 /\ (!x. x IN convex hull {u,v,w} ==> h1 x = l1 x + y1) /\
           linear l2 /\ (!x. x IN convex hull {u,v,w} ==> h2 x = l2 x + y2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ !z. z IN holed_disk_model k /\ dist(z,z0) < d
                                  ==> (G:real^2->real^3) z IN U` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `U:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(G:real^2->real^3) z0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`holed_disk_model k`; `G:real^2->real^3`] PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    ASM_REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `ball((G:real^2->real^3) z0,e) SUBSET U` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT1(SPEC `k:num` MOI_FSB_HD_POLY)) THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `c0:(real^2->bool)->bool`] MOI_S3KC_HD_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s:real^2->bool. s IN c0 /\ z0 IN s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:(real^2->bool)->bool`; `s:real^2->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^2->bool)->bool`; `tau:real^2->bool`] MOI_S3SO_VS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2` (X_CHOOSE_THEN `r:real^2`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex hull {p:real^2,q,r} = tau /\ ~collinear {p:real^2,q,r}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^2) IN convex hull {p,q,r} /\
                convex hull {p:real^2,q,r} SUBSET holed_disk_model k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `D0 = d + norm(p - z0:real^2) + norm(q - z0:real^2) + norm(r - z0:real^2)` THEN
  SUBGOAL_THEN `&0 < D0` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MP_TAC(ISPEC `p - z0:real^2` NORM_POS_LE) THEN
    MP_TAC(ISPEC `q - z0:real^2` NORM_POS_LE) THEN MP_TAC(ISPEC `r - z0:real^2` NORM_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ep = d / D0` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * D0 = d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `ep * d + ep * norm(p - z0:real^2) + ep * norm(q - z0:real^2) +
                ep * norm(r - z0:real^2) = d /\
                &0 < ep * d /\ &0 <= ep * norm(p - z0:real^2) /\
                &0 <= ep * norm(q - z0:real^2) /\ &0 <= ep * norm(r - z0:real^2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ep * D0 = d` THEN EXPAND_TAC "D0" THEN REWRITE_TAC[REAL_ADD_LDISTRIB];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ep <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `ep * d <= &1 * d` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `p1 = z0 + ep % (p - z0):real^2` THEN
  ABBREV_TAC `q1 = z0 + ep % (q - z0):real^2` THEN
  ABBREV_TAC `r1 = z0 + ep % (r - z0):real^2` THEN
  SUBGOAL_THEN `convex hull {p1:real^2,q1,r1} SUBSET convex hull {p,q,r}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET;
      EMPTY_SUBSET] THEN
    MAP_EVERY EXPAND_TAC ["p1"; "q1"; "r1"] THEN
    SUBGOAL_THEN `!x:real^2. x IN convex hull {p,q,r}
                             ==> z0 + ep % (x - z0) IN convex hull {p,q,r}`
    (fun th -> REPEAT CONJ_TAC THEN MATCH_MP_TAC th THEN SIMP_TAC[HULL_INC; IN_INSERT]) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `z0 + ep % (x - z0):real^2 = (&1 - ep) % z0 + ep % x` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[convex] (ISPEC `{p:real^2,q,r}` CONVEX_CONVEX_HULL)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p1:real^2,q1,r1} SUBSET ball(z0,d)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_BALL; INSERT_SUBSET;
      EMPTY_SUBSET; IN_BALL] THEN
    MAP_EVERY EXPAND_TAC ["p1"; "q1"; "r1"] THEN
    REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {p1:real^2,q1,r1}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET] THEN MAP_EVERY EXPAND_TAC ["p1"; "q1"; "r1"] THEN
    SUBGOAL_THEN `moi_s3so_det (z0 + ep % (p - z0)) (z0 + ep % (q - z0)) (z0 + ep % (r - z0)) =
                  (ep * ep) * moi_s3so_det p q r` SUBST1_TAC THENL
     [REWRITE_TAC[moi_s3so_det; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[MOI_S3SO_COLLINEAR_DET];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p1:real^2,q1,r1} SUBSET holed_disk_model k` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `G:real^2->real^3`; `p1:real^2`; `q1:real^2`;
                 `r1:real^2`] MOI_S3SO_PL_SUBTRI2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^2` (X_CHOOSE_THEN `b1:real^2` (X_CHOOSE_THEN `c1:real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `h1:real^2->real^3`; `a1:real^2`; `b1:real^2`;
                 `c1:real^2`] MOI_S3SO_PL_SUBTRI2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^2` (X_CHOOSE_THEN `b2:real^2` (X_CHOOSE_THEN `c2:real^2`
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `h2:real^2->real^3`; `a2:real^2`; `b2:real^2`;
                 `c2:real^2`] MOI_S3SO_PL_SUBTRI2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a3:real^2` (X_CHOOSE_THEN `b3:real^2` (X_CHOOSE_THEN `c3:real^2`
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `convex hull {a3:real^2,b3,c3} SUBSET convex hull {a1,b1,c1}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {a2:real^2,b2,c2}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a3:real^2,b3,c3} SUBSET convex hull {p1,q1,r1}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {a1:real^2,b1,c1}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a3:real^2`; `b3:real^2`; `c3:real^2`; `l:real^2->real^3`; `y:real^3`;
                        `l1:real^2->real^3`; `y1:real^3`; `l2:real^2->real^3`;
                        `y2:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {p1:real^2,q1,r1}` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN holed_disk_model k /\ x IN ball(z0,d)` MP_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b c x:real^2. x IN a /\ a SUBSET b /\ b SUBSET c ==> x IN c`) THEN
      EXISTS_TAC `convex hull {a3:real^2,b3,c3}` THEN
      EXISTS_TAC `convex hull {p1:real^2,q1,r1}` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try can (find_term ((=) `l:real^2->real^3`)) (concl th) && is_forall(concl th)
      with Failure _ -> false)) THEN
    UNDISCH_TAC `convex hull {a3:real^2,b3,c3} SUBSET convex hull {a1,b1,c1}` THEN
    UNDISCH_TAC `(x:real^2) IN convex hull {a3,b3,c3}` THEN SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try can (find_term ((=) `l1:real^2->real^3`)) (concl th) && is_forall(concl th)
      with Failure _ -> false)) THEN
    UNDISCH_TAC `convex hull {a3:real^2,b3,c3} SUBSET convex hull {a2,b2,c2}` THEN
    UNDISCH_TAC `(x:real^2) IN convex hull {a3,b3,c3}` THEN SET_TAC[]]);;

let MOI_S3SO_CONST_INT = prove
 (`!(m:(real^3->bool)->bool) m' i i' k (G:real^2->real^3) G' (A:real^3->bool) A'
    (f:real^3->real^3) f' (g:real^3->real^3) g' U.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     FINITE m' /\ combinatorial_manifold 2 m' /\ moi_s3so_sided (UNIONS m') i' /\
     A SUBSET UNIONS m /\ A' SUBSET UNIONS m' /\
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     pl_homeomorphism (A,A') (f,f') /\ pl_homeomorphism (A,A') (g,g') /\
     moi_s3so_sp i i' A g /\ open U /\ ~(U INTER A = {}) /\
     (!x. x IN U INTER A ==> f x = g x)
     ==> moi_s3so_sp i i' A f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (holed_disk_model k,A')
                  ((f:real^3->real^3) o (G:real^2->real^3),
                   (G':real^3->real^2) o (f':real^3->real^3)) /\
                pl_homeomorphism (holed_disk_model k,A')
                  ((g:real^3->real^3) o (G:real^2->real^3),
                   (G':real^3->real^2) o (g':real^3->real^3))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A:real^3->bool`; `G:real^2->real^3`;
                 `G':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `A':real^3->bool`; `f:real^3->real^3`;
                 `f':real^3->real^3`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A':real^3->bool`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `(G':real^3->real^2) o (f':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A':real^3->bool`;
                 `(g:real^3->real^3) o (G:real^2->real^3)`;
                 `(G':real^3->real^2) o (g':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k:num`; `G:real^2->real^3`]
    MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bG:bool` (LABEL_TAC "sG")) THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k:num`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`] MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bF:bool` (LABEL_TAC "sF")) THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k:num`;
                 `(g:real^3->real^3) o (G:real^2->real^3)`] MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `bQ:bool` (LABEL_TAC "sQ")) THEN
  UNDISCH_TAC `~(U INTER A:real^3->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `G:real^2->real^3`; `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `(g:real^3->real^3) o (G:real^2->real^3)`; `U:real^3->bool`;
                 `(G':real^3->real^2) x0`] MOI_S3SO_TRI_NEAR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `v:real^2` (X_CHOOSE_THEN `w:real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `(u:real^2) IN convex hull {u,v,w} /\ v IN convex hull {u,v,w} /\
                w IN convex hull {u,v,w}` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN convex hull {u,v,w} ==> (G:real^2->real^3) x IN U INTER A`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (G:real^2->real^3) (convex hull {u,v,w}) SUBSET U` THEN
      UNDISCH_TAC `(x:real^2) IN convex hull {u,v,w}` THEN SET_TAC[];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) (G(u:real^2)) = g (G u) /\ f (G v) = g (G v) /\
                f (G w) = g (G w)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      try can (find_term ((=) `U INTER A:real^3->bool`)) (concl th) &&
          can (find_term ((=) `g:real^3->real^3`)) (concl th) with Failure _ -> false)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^2->real^3`; `G':real^3->real^2`; `l:real^2->real^3`; `y:real^3`;
                 `u:real^2`; `v:real^2`; `w:real^2`] MOI_S3SO_INV_AFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l3:real^3->real^2` (X_CHOOSE_THEN `y3:real^2` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_s3so_pos i' ((g:real^3->real^3) (G(u:real^2))) (g (G v)) (g (G w)) <=>
                moi_s3so_pos i (G u) (G v) (G w)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3so_sp i i' A (g:real^3->real^3)` THEN REWRITE_TAC[moi_s3so_sp] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `IMAGE (G:real^2->real^3) (convex hull {u,v,w}) =
                               convex hull {G u,G v,G w}`)] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_S3SO_AFF_BARY THEN
      MAP_EVERY EXISTS_TAC [`(l2:real^2->real^3) o (l3:real^3->real^2)`;
                            `(l2:real^2->real^3) y3 + y2`] THEN
      CONJ_TAC THENL [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?x:real^2. x IN convex hull {u,v,w} /\ (z:real^3) = G x`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN convex hull {(G:real^2->real^3) u,G v,G w}` THEN
        REWRITE_TAC[GSYM(ASSUME `IMAGE (G:real^2->real^3) (convex hull {u,v,w}) =
                                 convex hull {G u,G v,G w}`)] THEN
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^3) z = (l2:real^2->real^3) x + y2` SUBST1_TAC THENL
       [UNDISCH_TAC `(z:real^3) = G (x:real^2)` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) = (l3:real^3->real^2) z + y3` SUBST1_TAC THENL
       [SUBGOAL_THEN `(G':real^3->real^2) z = x` (SUBST1_TAC o SYM) THENL
         [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l2:real^2->real^3)`)] THEN
      VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`(g:real^3->real^3) o (G:real^2->real^3)`; `l2:real^2->real^3`;
                     `y2:real^3`; `u:real^2`; `v:real^2`; `w:real^2`] MOI_S3SO_AFF_NONCOL) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; o_THM]];
    ALL_TAC] THEN
  USE_THEN "sF" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l1:real^2->real^3`;
                                 `y1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sQ" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l2:real^2->real^3`;
                                 `y2:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sG" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l:real^2->real^3`;
                                 `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(f:real^3->real^3) (G(u:real^2)) = g (G u)`;
              ASSUME `(f:real^3->real^3) (G(v:real^2)) = g (G v)`;
              ASSUME `(f:real^3->real^3) (G(w:real^2)) = g (G w)`] THEN
  REWRITE_TAC[ASSUME `moi_s3so_pos i' ((g:real^3->real^3) (G(u:real^2))) (g (G v)) (g (G w)) <=>
                      moi_s3so_pos i (G u) (G v) (G w)`] THEN
  DISCH_THEN(LABEL_TAC "eG") THEN DISCH_THEN(LABEL_TAC "eQ") THEN
  DISCH_THEN(LABEL_TAC "eF") THEN
  SUBGOAL_THEN `bF:bool = bG` SUBST_ALL_TAC THENL
   [REMOVE_THEN "eG" MP_TAC THEN REMOVE_THEN "eQ" MP_TAC THEN REMOVE_THEN "eF" MP_TAC THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3SO_SP_CRIT THEN
  MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `k:num`;
                        `G:real^2->real^3`; `G':real^3->real^2`; `A':real^3->bool`;
                        `bG:bool`] THEN
  ASM_REWRITE_TAC[]);;

(* O3 CONST: the statement MOI_S3MT_SORIENT_CONST_TERM. *)

let MOI_S3SO_CONST = prove
 (MOI_S3MT_SORIENT_CONST_TERM,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "e'") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_s3so_sided s i /\ moi_s3so_sided s' i'` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3so_sided] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (let l = lhs(concl th) in is_comb l && fst(dest_const(rator l)) = "UNIONS")))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `i:real^3->bool`;
                 `i':real^3->bool`; `k:num`; `G:real^2->real^3`; `G':real^3->real^2`;
                 `A:real^3->bool`; `A':real^3->bool`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `g:real^3->real^3`; `g':real^3->real^3`; `U:real^3->bool`]
    MOI_S3SO_CONST_INT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s3so_sp; moi_s3so_pos]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_sp; moi_s3so_pos]);;

(* ------------------------------------------------------------------------- *)
(* Part 11: tools for DIR.  The edge rule for two flat triangles of the      *)
(* surface with a common edge (each inside a simplex of m, disjoint relative *)
(* interiors); side preservation forces equal sign constants; cyclic order  *)
(* facts on relative_frontier std_triangle.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_TRI_ADJ = prove
 (`!(m:(real^3->bool)->bool) i p q r1 r2 k1 k2.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     k1 IN m /\ k2 IN m /\
     convex hull {p,q,r1} SUBSET k1 /\ convex hull {p,q,r2} SUBSET k2 /\
     ~collinear {p,q,r1} /\ ~collinear {p,q,r2} /\
     relative_interior(convex hull {p,q,r1}) INTER
     relative_interior(convex hull {p,q,r2}) = {}
     ==> (moi_s3so_pos i p q r2 <=> ~moi_s3so_pos i p q r1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN k1 /\ q IN k1 /\ r1 IN k1 /\ p IN k2 /\ q IN k2 /\ r2 IN k2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{p:real^3,q,r1}`] HULL_SUBSET) THEN
    MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{p:real^3,q,r2}`] HULL_SUBSET) THEN
    UNDISCH_TAC `convex hull {p:real^3,q,r1} SUBSET k1` THEN
    UNDISCH_TAC `convex hull {p:real^3,q,r2} SUBSET k2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(?x:real^3. x IN relative_interior(convex hull {p,q,r1}) /\
                 x IN relative_interior(convex hull {p,q,r2}))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `k1:real^3->bool = k2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k2:real^3->bool`; `p:real^3`; `q:real^3`;
                   `r1:real^3`] MOI_S3SO_M_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
    MATCH_MP_TAC MOI_S3SO_IM_SAME THEN
    MAP_EVERY EXISTS_TAC [`UNIONS m:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN m ==> x SUBSET UNIONS m`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(k1:real^3->bool) = &2 /\ aff_dim(k2:real^3->bool) = &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3SO_M_DIM2 THEN
    EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^3 = q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3SO_NONCOL_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k1:real^3->bool`; `k2:real^3->bool`;
                 `p:real^3`; `q:real^3`] MOI_SCF_INTER_DIM1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(k1 INTER k2:real^3->bool) IN m` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k1 INTER k2:real^3->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `k1:real^3->bool`]
    MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `k2:real^3->bool`]
    MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S3SO_IM_ADJ THEN
  MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `c:real^3`;
                        `c':real^3`] THEN
  SUBGOAL_THEN `~collinear {a:real^3,b,c} /\ ~collinear {a:real^3,b,c'}` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^3 = c')` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(k1:real^3->bool = k2)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k1 INTER k2:real^3->bool = convex hull {a,b}` THEN
  UNDISCH_TAC `(k1:real^3->bool) = convex hull {a,b,c}` THEN
  UNDISCH_TAC `(k2:real^3->bool) = convex hull {a,b,c'}` THEN
  REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  ASM SET_TAC[]);;

(* Side preservation of f gives equal sign constants for G and f o G. *)

let MOI_S3SO_SP_SIGN_EQ = prove
 (`!(m:(real^3->bool)->bool) m' i i' k (G:real^2->real^3) G' (A:real^3->bool) A'
    (f:real^3->real^3) f' bG bF.
     moi_s3so_sided (UNIONS m) i /\ moi_s3so_sided (UNIONS m') i' /\
     A SUBSET UNIONS m /\ A' SUBSET UNIONS m' /\
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\ pl_homeomorphism (A,A') (f,f') /\
     moi_s3so_sp i i' A f /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G x = l x + y)
                  ==> ((moi_s3so_pos i (G u) (G v) (G w) <=> &0 < moi_s3so_det u v w) <=>
                       bG)) /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> f(G x) = l x + y)
                  ==> ((moi_s3so_pos i' (f(G u)) (f(G v)) (f(G w)) <=>
                        &0 < moi_s3so_det u v w) <=> bF))
     ==> (bF <=> bG)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sG") (LABEL_TAC "sF"))))))))) THEN
  SUBGOAL_THEN `pl_homeomorphism (holed_disk_model k,A')
                  ((f:real^3->real^3) o (G:real^2->real^3),
                   (G':real^3->real^2) o (f':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A:real^3->bool`; `G:real^2->real^3`;
                 `G':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k`; `A':real^3->bool`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `(G':real^3->real^2) o (f':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `G:real^2->real^3`; `(f:real^3->real^3) o (G:real^2->real^3)`;
                 `(f:real^3->real^3) o (G:real^2->real^3)`; `(:real^3)`;
                 `vec 0:real^2`] MOI_S3SO_TRI_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; MOI_S3KC_IN_HD; VEC_COMPONENT] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `v:real^2` (X_CHOOSE_THEN `w:real^2`
    (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`G:real^2->real^3`; `G':real^3->real^2`; `l:real^2->real^3`; `y:real^3`;
                 `u:real^2`; `v:real^2`; `w:real^2`] MOI_S3SO_INV_AFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l3:real^3->real^2` (X_CHOOSE_THEN `y3:real^2` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_s3so_pos i' ((f:real^3->real^3) (G(u:real^2))) (f (G v)) (f (G w)) <=>
                moi_s3so_pos i (G u) (G v) (G w)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3so_sp i i' A (f:real^3->real^3)` THEN REWRITE_TAC[moi_s3so_sp] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `IMAGE (G:real^2->real^3) (convex hull {u,v,w}) =
                               convex hull {G u,G v,G w}`)] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
      MATCH_MP_TAC MOI_S3SO_AFF_BARY THEN
      MAP_EVERY EXISTS_TAC [`(l1:real^2->real^3) o (l3:real^3->real^2)`;
                            `(l1:real^2->real^3) y3 + y1`] THEN
      CONJ_TAC THENL [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?x:real^2. x IN convex hull {u,v,w} /\ (z:real^3) = G x`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN convex hull {(G:real^2->real^3) u,G v,G w}` THEN
        REWRITE_TAC[GSYM(ASSUME `IMAGE (G:real^2->real^3) (convex hull {u,v,w}) =
                                 convex hull {G u,G v,G w}`)] THEN
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^3->real^3) z = (l1:real^2->real^3) x + y1` SUBST1_TAC THENL
       [UNDISCH_TAC `(z:real^3) = G (x:real^2)` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) = (l3:real^3->real^2) z + y3` SUBST1_TAC THENL
       [SUBGOAL_THEN `(G':real^3->real^2) z = x` (SUBST1_TAC o SYM) THENL
         [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l1:real^2->real^3)`)] THEN
      VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`(f:real^3->real^3) o (G:real^2->real^3)`; `l1:real^2->real^3`;
                     `y1:real^3`; `u:real^2`; `v:real^2`; `w:real^2`] MOI_S3SO_AFF_NONCOL) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; o_THM]];
    ALL_TAC] THEN
  USE_THEN "sF" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l1:real^2->real^3`;
                                 `y1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "sG" (MP_TAC o SPECL [`u:real^2`; `v:real^2`; `w:real^2`; `l:real^2->real^3`;
                                 `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `moi_s3so_pos i' ((f:real^3->real^3) (G(u:real^2))) (f (G v)) (f (G w)) <=>
                      moi_s3so_pos i (G u) (G v) (G w)`] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Part 12: rectangles.  The counterclockwise PL parametrization            *)
(* moi_s3so_rpsi a b of the boundary of interval[a,b] by                     *)
(* relative_frontier std_triangle (tau runs once around), its tau function   *)
(* moi_s3so_rtau, and the orientation rule: three points along a segment of *)
(* the boundary are in cyclic order iff the centre lies on the left.         *)
(* ------------------------------------------------------------------------- *)

(* The cyclic order of three reals is moi_s3ci_cyc3 of pc_moi_s33_circ.    *)

let MOI_S3SO_CYC_INC = prove
 (`!x y z. x < y /\ y < z ==> moi_s3ci_cyc3 x y z`,
  REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC);;

let MOI_S3SO_CYC_DEC = prove
 (`!x y z. z < y /\ y < x ==> ~moi_s3ci_cyc3 x y z`,
  REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC);;

let MOI_S3SO_AFF2 = prove
 (`!p1 q1 r1 p2 q2 r2.
     ?l y. linear l /\
           !x:real^2. vector[p1 * x$1 + q1 * x$2 + r1; p2 * x$1 + q2 * x$2 + r2]:real^2 =
                      l x + y`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `\x:real^2. vector[p1 * x$1 + q1 * x$2; p2 * x$1 + q2 * x$2]:real^2` THEN
  EXISTS_TAC `vector[r1; r2]:real^2` THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_S3SO_RF_RECT = prove
 (`!a b y:real^2.
     a$1 < b$1 /\ a$2 < b$2
     ==> (y IN relative_frontier(interval[a,b]) <=>
          (a$1 <= y$1 /\ y$1 <= b$1 /\ a$2 <= y$2 /\ y$2 <= b$2) /\
          (y$1 = a$1 \/ y$1 = b$1 \/ y$2 = a$2 \/ y$2 = b$2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior(interval[a:real^2,b]) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL] THEN
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN REAL_ARITH_TAC);;

let moi_s3so_rpsi = new_definition
 `moi_s3so_rpsi (a:real^2) (b:real^2) (x:real^2) =
    if x$2 = &0
    then (if x$1 <= &1 / &2 then vector[a$1 + (&2 * x$1) * (b$1 - a$1); a$2]:real^2
          else vector[b$1; a$2 + (&2 * x$1 - &1) * (b$2 - a$2)])
    else if x$1 = &0 then vector[a$1; a$2 + x$2 * (b$2 - a$2)]
    else vector[b$1 - x$2 * (b$1 - a$1); b$2]`;;

let moi_s3so_rtau = new_definition
 `moi_s3so_rtau (a:real^2) (b:real^2) (y:real^2) =
    if y$2 = a$2 then (y$1 - a$1) / (&4 * (b$1 - a$1))
    else if y$1 = b$1 then &1 / &4 + (y$2 - a$2) / (&4 * (b$2 - a$2))
    else if y$2 = b$2 then &1 / &2 + (b$1 - y$1) / (&4 * (b$1 - a$1))
    else &3 / &4 + (b$2 - y$2) / (&4 * (b$2 - a$2))`;;

(* The parametrization lands on the boundary and carries tau to rtau. *)

let MOI_S3SO_RPSI_RTAU = prove
 (`!a b x:real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ x IN relative_frontier std_triangle
     ==> moi_s3so_rpsi a b x IN relative_frontier(interval[a,b]) /\
         moi_s3so_rtau a b (moi_s3so_rpsi a b x) = moi_lsp_tau x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_LSP_STD_FRONTIER_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  ASM_SIMP_TAC[MOI_S3SO_RF_RECT] THEN
  SUBGOAL_THEN `&0 < (b:real^2)$1 - (a:real^2)$1 /\ &0 < (b:real^2)$2 - (a:real^2)$2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_rpsi; moi_s3so_rtau; moi_lsp_tau] THEN
  ASM_CASES_TAC `(x:real^2)$2 = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(x:real^2)$1 <= &1 / &2` THEN ASM_REWRITE_TAC[VECTOR_2] THENL
     [SUBGOAL_THEN `&0 <= (&2 * (x:real^2)$1) * ((b:real^2)$1 - (a:real^2)$1) /\
                    (&2 * x$1) * (b$1 - a$1) <= b$1 - a$1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(a + x) - a:real = x`] THEN
      UNDISCH_TAC `&0 < (b:real^2)$1 - (a:real^2)$1` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `&0 <= (&2 * (x:real^2)$1 - &1) * ((b:real^2)$2 - (a:real^2)$2) /\
                    (&2 * x$1 - &1) * (b$2 - a$2) <= b$2 - a$2` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `(a:real^2)$2 + (&2 * (x:real^2)$1 - &1) * ((b:real^2)$2 - a$2) = a$2` THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(x:real^2)$1 = &1 / &2` ASSUME_TAC THENL
         [UNDISCH_TAC `(a:real^2)$2 + (&2 * (x:real^2)$1 - &1) * ((b:real^2)$2 - a$2) = a$2` THEN
          UNDISCH_TAC `&0 < (b:real^2)$2 - (a:real^2)$2` THEN CONV_TAC REAL_FIELD;
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_ARITH `(a + x) - a:real = x`] THEN
        UNDISCH_TAC `&0 < (b:real^2)$2 - (a:real^2)$2` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^2)$1 = &0` THEN ASM_REWRITE_TAC[VECTOR_2] THENL
   [SUBGOAL_THEN `&0 < (x:real^2)$2 * ((b:real^2)$2 - (a:real^2)$2) /\
                  x$2 * (b$2 - a$2) <= b$2 - a$2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((a:real^2)$2 + (x:real^2)$2 * ((b:real^2)$2 - a$2) = a$2) /\ ~(a$1 = b$1)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(a:real^2)$2 + (x:real^2)$2 * ((b:real^2)$2 - a$2) = b$2` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(x:real^2)$2 = &1` ASSUME_TAC THENL
       [UNDISCH_TAC `(a:real^2)$2 + (x:real^2)$2 * ((b:real^2)$2 - a$2) = b$2` THEN
        UNDISCH_TAC `&0 < (b:real^2)$2 - (a:real^2)$2` THEN CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_REFL] THEN
        UNDISCH_TAC `&0 < (b:real^2)$1 - (a:real^2)$1` THEN CONV_TAC REAL_FIELD];
      UNDISCH_TAC `&0 < (b:real^2)$2 - (a:real^2)$2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$1 + x$2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (x:real^2)$2 * ((b:real^2)$1 - (a:real^2)$1) /\
                x$2 * (b$1 - a$1) < b$1 - a$1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((b:real^2)$2 = (a:real^2)$2) /\ ~(b$1 - (x:real^2)$2 * (b$1 - a$1) = b$1)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `b - (b - x):real = x`] THEN
  UNDISCH_TAC `&0 < (b:real^2)$1 - (a:real^2)$1` THEN CONV_TAC REAL_FIELD);;

let MOI_S3SO_STD_RF_SEGS = prove
 (`relative_frontier std_triangle =
   UNIONS {segment[vec 0,(&1 / &2) % basis 1:real^2], segment[(&1 / &2) % basis 1,basis 1],
           segment[basis 1,basis 2], segment[basis 2,vec 0]}`,
  SUBGOAL_THEN `~collinear {vec 0:real^2,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; moi_s3so_det; VECTOR_SUB_RZERO] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[std_triangle; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  SUBGOAL_THEN `segment[vec 0,(&1 / &2) % basis 1:real^2] UNION
                segment[(&1 / &2) % basis 1,basis 1] = segment[vec 0,basis 1]`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [MATCH_MP_TAC UNION_SEGMENT THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY; UNION_ASSOC]);;

(* Finishing tactic for the four segments: ring identities, contradictory  *)
(* branches, and the endpoint branches t = 0, t = 1.                        *)

let moi_s3so_seg_fin_tac =
  REWRITE_TAC[VECTOR_2] THEN REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC REAL_RING; ASM_REAL_ARITH_TAC;
         SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL
          [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC REAL_RING];
         SUBGOAL_THEN `t = &1` SUBST_ALL_TAC THENL
          [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC REAL_RING]];;

let MOI_S3SO_RPSI_SEGS = prove
 (`!a b:real^2.
     (!z. z IN segment[vec 0,(&1 / &2) % basis 1]
          ==> moi_s3so_rpsi a b z =
              vector[(&2 * (b$1 - a$1)) * z$1 + &0 * z$2 + a$1;
                     &0 * z$1 + &0 * z$2 + a$2]) /\
     (!z. z IN segment[(&1 / &2) % basis 1,basis 1]
          ==> moi_s3so_rpsi a b z =
              vector[&0 * z$1 + &0 * z$2 + b$1;
                     (&2 * (b$2 - a$2)) * z$1 + &0 * z$2 + (a$2 - (b$2 - a$2))]) /\
     (!z. z IN segment[basis 1,basis 2]
          ==> moi_s3so_rpsi a b z =
              vector[&0 * z$1 + --(b$1 - a$1) * z$2 + b$1;
                     &0 * z$1 + &0 * z$2 + b$2]) /\
     (!z. z IN segment[basis 2,vec 0]
          ==> moi_s3so_rpsi a b z =
              vector[&0 * z$1 + &0 * z$2 + a$1;
                     &0 * z$1 + (b$2 - a$2) * z$2 + a$2])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN REPEAT CONJ_TAC THEN
  X_GEN_TAC `z:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  REWRITE_TAC[moi_s3so_rpsi; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_LID; REAL_ADD_RID] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
  REPEAT COND_CASES_TAC THEN moi_s3so_seg_fin_tac);;

let MOI_S3SO_RPSI_PIECES = prove
 (`!a b:real^2.
     moi_s3so_rpsi a b continuous_on relative_frontier std_triangle /\
     pl_map_on (relative_frontier std_triangle) (moi_s3so_rpsi a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3SO_STD_RF_SEGS] THEN
  MATCH_MP_TAC MOI_REAL_PIECEWISE_AFFINE_UNIONS THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_SEGMENT] THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`] MOI_S3SO_RPSI_SEGS) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s") MP_TAC) ORELSE DISCH_THEN(LABEL_TAC "s")) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`&2 * ((b:real^2)$1 - (a:real^2)$1)`; `&0`; `(a:real^2)$1`; `&0`; `&0`;
                  `(a:real^2)$2`] MOI_S3SO_AFF2);
    MP_TAC(SPECL [`&0`; `&0`; `(b:real^2)$1`; `&2 * ((b:real^2)$2 - (a:real^2)$2)`; `&0`;
                  `(a:real^2)$2 - ((b:real^2)$2 - (a:real^2)$2)`] MOI_S3SO_AFF2);
    MP_TAC(SPECL [`&0`; `--((b:real^2)$1 - (a:real^2)$1)`; `(b:real^2)$1`; `&0`; `&0`;
                  `(b:real^2)$2`] MOI_S3SO_AFF2);
    MP_TAC(SPECL [`&0`; `&0`; `(a:real^2)$1`; `&0`; `(b:real^2)$2 - (a:real^2)$2`;
                  `(a:real^2)$2`] MOI_S3SO_AFF2)] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Circles.  A set homeomorphic to the unit circle that lies inside another *)
(* such set is all of it (a punctured circle is a line, and a circle does  *)
(* not embed in a line).  The same argument one dimension up is             *)
(* MOI_S4B_SPHERE_IN_SPHERE of pc_moi_s34_scellb (2-spheres).                *)

let MOI_S3SO_CIRC_CONVEX = prove
 (`!s:real^N->bool.
     convex s /\ bounded s /\ aff_dim s = &2
     ==> sphere(vec 0:real^2,&1) homeomorphic relative_frontier s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `s:real^N->bool`]
    HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS) THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL; AFF_DIM_CBALL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[DIMINDEX_2]);;

let MOI_S3SO_PL_CIRC = prove
 (`!J:real^N->bool. pl_sphere 1 J ==> sphere(vec 0:real^2,&1) homeomorphic J`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `relative_frontier(k:real^N->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_CIRC_CONVEX THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]]);;

let MOI_S3SO_CIRCLE_EQ = prove
 (`!K L:real^N->bool.
     sphere(vec 0:real^2,&1) homeomorphic K /\ sphere(vec 0:real^2,&1) homeomorphic L /\
     K SUBSET L
     ==> K = L`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET] THEN
  X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  UNDISCH_TAC `sphere(vec 0:real^2,&1) homeomorphic (L:real^N->bool)` THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^N` (X_CHOOSE_TAC `h':real^N->real^2`)) THEN
  SUBGOAL_THEN `(L DELETE (q:real^N)) homeomorphic (:real^1)` MP_TAC THENL
   [MATCH_MP_TAC(ISPECL [`L DELETE (q:real^N)`;
                          `sphere(vec 0:real^2,&1) DELETE (h':real^N->real^2) q`;
                          `(:real^1)`] HOMEOMORPHIC_TRANS) THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`h':real^N->real^2`; `h:real^2->real^N`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `sphere(vec 0:real^2,&1)`] THEN
      UNDISCH_TAC `homeomorphism (sphere(vec 0:real^2,&1),L) (h:real^2->real^N,h')` THEN
      REWRITE_TAC[GSYM HOMEOMORPHISM_SYM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (L,sphere(vec 0:real^2,&1)) (h':real^N->real^2,h)` THEN
      REWRITE_TAC[homeomorphism] THEN UNDISCH_TAC `(q:real^N) IN L` THEN SET_TAC[];
      MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `(:real^1)`; `(h':real^N->real^2) q`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
      REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; RELATIVE_FRONTIER_CBALL; AFF_DIM_CBALL;
                  AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1; DIMINDEX_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `homeomorphism (sphere(vec 0:real^2,&1),L) (h:real^2->real^N,h')` THEN
      REWRITE_TAC[homeomorphism] THEN UNDISCH_TAC `(q:real^N) IN L` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^N->real^1` (X_CHOOSE_TAC `phi':real^1->real^N`)) THEN
  UNDISCH_TAC `sphere(vec 0:real^2,&1) homeomorphic (K:real^N->bool)` THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^2->real^N` (X_CHOOSE_TAC `th':real^N->real^2`)) THEN
  SUBGOAL_THEN `IMAGE (th:real^2->real^N) (sphere(vec 0,&1)) SUBSET L DELETE q`
  ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (sphere(vec 0:real^2,&1),K) (th:real^2->real^N,th')` THEN
    REWRITE_TAC[homeomorphism] THEN
    UNDISCH_TAC `(K:real^N->bool) SUBSET L` THEN UNDISCH_TAC `~((q:real^N) IN K)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:real^N->real^1) o (th:real^2->real^N)) continuous_on
                sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[homeomorphism];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `L DELETE (q:real^N)` THEN
      ASM_MESON_TAC[homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE ((phi:real^N->real^1) o (th:real^2->real^N))
                           (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `&1`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1; DIMINDEX_2;
                    OPEN_IN_REFL] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(th:real^2->real^N) x IN L DELETE q /\ th y IN L DELETE q`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (th:real^2->real^N) (sphere(vec 0,&1)) SUBSET L DELETE q` THEN
      UNDISCH_TAC `(x:real^2) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `(y:real^2) IN sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(th:real^2->real^N) x = th y` ASSUME_TAC THENL
     [UNDISCH_TAC `homeomorphism (L DELETE q,(:real^1)) (phi:real^N->real^1,phi')` THEN
      REWRITE_TAC[homeomorphism] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(fun th ->
        ONCE_REWRITE_TAC[GSYM(MATCH_MP th
          (ASSUME `(th:real^2->real^N) x IN L DELETE q`))] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[MATCH_MP th (ASSUME `(th:real^2->real^N) y IN L DELETE q`)]);
      UNDISCH_TAC `homeomorphism (sphere(vec 0:real^2,&1),K) (th:real^2->real^N,th')` THEN
      REWRITE_TAC[homeomorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE ((phi:real^N->real^1) o (th:real^2->real^N))
                              (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE ((phi:real^N->real^1) o (th:real^2->real^N)) (sphere(vec 0,&1))`
         CLOPEN) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  UNDISCH_TAC `compact(IMAGE ((phi:real^N->real^1) o (th:real^2->real^N))
                             (sphere(vec 0,&1)))` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[COMPACT_IMP_BOUNDED; NOT_BOUNDED_UNIV]);;

let MOI_S3SO_STD_FACTS = prove
 (`convex std_triangle /\ bounded std_triangle /\ aff_dim std_triangle = &2 /\
   ~collinear {vec 0:real^2,basis 1,basis 2}`,
  SUBGOAL_THEN `~collinear {vec 0:real^2,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; moi_s3so_det; VECTOR_SUB_RZERO] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[std_triangle; CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL; FINITE_IMP_BOUNDED;
               FINITE_INSERT; FINITE_EMPTY; MOI_S3SO_NONCOL_DIM]);;

let MOI_S3SO_RECT_FACTS = prove
 (`!a b:real^2.
     a$1 < b$1 /\ a$2 < b$2
     ==> convex(interval[a,b]) /\ bounded(interval[a,b]) /\ aff_dim(interval[a,b]) = &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_INTERVAL; BOUNDED_INTERVAL] THEN
  REWRITE_TAC[GSYM DIMINDEX_2] THEN MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3SO_RPSI_PLH = prove
 (`!a b:real^2.
     a$1 < b$1 /\ a$2 < b$2
     ==> ?psi'. pl_homeomorphism (relative_frontier std_triangle,
                                  relative_frontier(interval[a,b]))
                                 (moi_s3so_rpsi a b,psi') /\
                (!y. y IN relative_frontier(interval[a,b])
                     ==> moi_lsp_tau (psi' y) = moi_s3so_rtau a b y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN relative_frontier std_triangle /\
                      y IN relative_frontier std_triangle /\
                      moi_s3so_rpsi a b x = moi_s3so_rpsi a b y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `x:real^2` MOI_LSP_TAU_RF) THEN MP_TAC(ISPEC `y:real^2` MOI_LSP_TAU_RF) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `x:real^2`] MOI_S3SO_RPSI_RTAU) THEN
    MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `y:real^2`] MOI_S3SO_RPSI_RTAU) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(relative_frontier std_triangle)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN REWRITE_TAC[MOI_S3SO_STD_FACTS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`] MOI_S3SO_RPSI_PIECES) THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (moi_s3so_rpsi a b) (relative_frontier std_triangle) =
                relative_frontier(interval[a,b])` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_CIRCLE_EQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `relative_frontier std_triangle`;
                           `IMAGE (moi_s3so_rpsi a b) (relative_frontier std_triangle)`]
                    HOMEOMORPHIC_TRANS) THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3SO_CIRC_CONVEX THEN REWRITE_TAC[MOI_S3SO_STD_FACTS];
        REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `moi_s3so_rpsi a b` THEN
        MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MOI_S3SO_CIRC_CONVEX THEN ASM_SIMP_TAC[MOI_S3SO_RECT_FACTS];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[MOI_S3SO_RPSI_RTAU]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier std_triangle`; `moi_s3so_rpsi a b`;
                 `relative_frontier(interval[a:real^2,b])`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^2` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[pl_homeomorphism] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier std_triangle`; `moi_s3so_rpsi a b`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^2->real^2) y IN relative_frontier std_triangle` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `(g:real^2->real^2) y`] MOI_S3SO_RPSI_RTAU) THEN
  ASM_SIMP_TAC[]);;

(* Segments of the boundary lie in one side. *)

let MOI_S3SO_RECT_SIDE = prove
 (`!a b v v':real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ segment[v,v'] SUBSET relative_frontier(interval[a,b])
     ==> (v$1 = a$1 /\ v'$1 = a$1) \/ (v$1 = b$1 /\ v'$1 = b$1) \/
         (v$2 = a$2 /\ v'$2 = a$2) \/ (v$2 = b$2 /\ v'$2 = b$2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `v IN relative_frontier(interval[a:real^2,b]) /\
                v' IN relative_frontier(interval[a,b]) /\
                midpoint(v,v') IN relative_frontier(interval[a,b])` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3SO_RF_RECT; midpoint; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* rtau along the four sides. *)

let MOI_S3SO_RTAU_SIDES = prove
 (`!a b y:real^2.
     a$1 < b$1 /\ a$2 < b$2
     ==> (y$2 = a$2 ==> moi_s3so_rtau a b y = (y$1 - a$1) / (&4 * (b$1 - a$1))) /\
         (y$1 = b$1 ==> moi_s3so_rtau a b y = &1 / &4 + (y$2 - a$2) / (&4 * (b$2 - a$2))) /\
         (y$2 = b$2 ==> moi_s3so_rtau a b y = &1 / &2 + (b$1 - y$1) / (&4 * (b$1 - a$1))) /\
         (y$1 = a$1 /\ ~(y$2 = a$2)
          ==> moi_s3so_rtau a b y = &3 / &4 + (b$2 - y$2) / (&4 * (b$2 - a$2))) /\
         (y$1 = a$1 /\ y$2 = a$2 ==> moi_s3so_rtau a b y = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (b:real^2)$1 - (a:real^2)$1 /\ &0 < (b:real^2)$2 - (a:real^2)$2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_rtau] THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY ASM_REAL_ARITH_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && can (term_match [] `(y:real^2)$i`) (lhs(concl th))))) THEN
  REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

(* The orientation rule: along a boundary segment, the ends and the        *)
(* midpoint are in cyclic rtau order iff the centre is on the left.         *)

let MOI_S3SO_RECT_CYC = prove
 (`!a b v v':real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ ~(v = v') /\
     segment[v,v'] SUBSET relative_frontier(interval[a,b])
     ==> (moi_s3ci_cyc3 (moi_s3so_rtau a b v) (moi_s3so_rtau a b (midpoint(v,v')))
                       (moi_s3so_rtau a b v') <=>
          &0 < moi_s3so_det v v' (midpoint(a,b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (b:real^2)$1 - (a:real^2)$1 /\ &0 < (b:real^2)$2 - (a:real^2)$2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v IN relative_frontier(interval[a:real^2,b]) /\
                v' IN relative_frontier(interval[a,b])` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3SO_RF_RECT] THEN DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC))
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `~((v:real^2)$1 = (v':real^2)$1 /\ v$2 = v'$2)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(v:real^2 = v')` THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`; `v:real^2`; `v':real^2`] MOI_S3SO_RECT_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m:real^2 = midpoint(v,v')` THEN
  SUBGOAL_THEN `(m:real^2)$1 = ((v:real^2)$1 + (v':real^2)$1) / &2 /\
                m$2 = (v$2 + v'$2) / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[midpoint; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_det; midpoint; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_ADD_COMPONENT] THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`] MOI_S3SO_RTAU_SIDES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "rs") THEN REWRITE_TAC[moi_s3ci_cyc3] THEN
  SUBGOAL_THEN `&0 < &4 * ((b:real^2)$1 - (a:real^2)$1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * ((b:real^2)$2 - (a:real^2)$2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [(* left side: v$1 = v'$1 = a$1 *)
    SUBGOAL_THEN `(m:real^2)$1 = (a:real^2)$1 /\ ~(m$2 = a$2)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(v'$1 - (v:real^2)$1) * (inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - v$2) -
      ((v':real^2)$2 - v$2) * (inv(&2) * (a$1 + b$1) - v$1) =
      (v$2 - v'$2) * (inv(&2) * (a$1 + b$1) - a$1)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2) * ((a:real^2)$1 + (b:real^2)$1) - a$1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP (CONJUNCT2 REAL_LT_MUL_EQ)
      (ASSUME `&0 < inv(&2) * ((a:real^2)$1 + (b:real^2)$1) - a$1`)] THEN
    USE_THEN "rs" (fun th ->
      let f y h = MP (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC y th))))) h in
      let g y h = MP (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC y th))))) h in
      REWRITE_TAC[f `m:real^2` (CONJ (ASSUME `(m:real^2)$1 = (a:real^2)$1`)
                                     (ASSUME `~((m:real^2)$2 = (a:real^2)$2)`))] THEN
      ASM_CASES_TAC `(v:real^2)$2 = (a:real^2)$2` THENL
       [SUBGOAL_THEN `~((v':real^2)$2 = (a:real^2)$2)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[g `v:real^2` (CONJ (ASSUME `(v:real^2)$1 = (a:real^2)$1`)
                                       (ASSUME `(v:real^2)$2 = (a:real^2)$2`));
                    f `v':real^2` (CONJ (ASSUME `(v':real^2)$1 = (a:real^2)$1`)
                                       (ASSUME `~((v':real^2)$2 = (a:real^2)$2)`))];
        ASM_CASES_TAC `(v':real^2)$2 = (a:real^2)$2` THENL
         [REWRITE_TAC[f `v:real^2` (CONJ (ASSUME `(v:real^2)$1 = (a:real^2)$1`)
                                         (ASSUME `~((v:real^2)$2 = (a:real^2)$2)`));
                      g `v':real^2` (CONJ (ASSUME `(v':real^2)$1 = (a:real^2)$1`)
                                         (ASSUME `(v':real^2)$2 = (a:real^2)$2`))];
          REWRITE_TAC[f `v:real^2` (CONJ (ASSUME `(v:real^2)$1 = (a:real^2)$1`)
                                         (ASSUME `~((v:real^2)$2 = (a:real^2)$2)`));
                      f `v':real^2` (CONJ (ASSUME `(v':real^2)$1 = (a:real^2)$1`)
                                         (ASSUME `~((v':real^2)$2 = (a:real^2)$2)`))]]]) THEN
    (SUBGOAL_THEN `&0 <= ((b:real^2)$2 - (v:real^2)$2) / (&4 * (b$2 - (a:real^2)$2)) /\
                   &0 <= (b$2 - (v':real^2)$2) / (&4 * (b$2 - a$2)) /\
                   &0 <= (b$2 - (m:real^2)$2) / (&4 * (b$2 - a$2))` STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[REAL_LT_LADD; (MATCH_MP REAL_LT_DIV2_EQ (ASSUME `&0 < &4 * ((b:real^2)$2 - (a:real^2)$2)`))] THEN
    ASM_REAL_ARITH_TAC;
    (* right side: v$1 = v'$1 = b$1 *)
    SUBGOAL_THEN `(m:real^2)$1 = (b:real^2)$1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(v'$1 - (v:real^2)$1) * (inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - v$2) -
      ((v':real^2)$2 - v$2) * (inv(&2) * (a$1 + b$1) - v$1) =
      (v'$2 - v$2) * (b$1 - inv(&2) * (a$1 + b$1))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (b:real^2)$1 - inv(&2) * ((a:real^2)$1 + b$1)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP (CONJUNCT2 REAL_LT_MUL_EQ)
      (ASSUME `&0 < (b:real^2)$1 - inv(&2) * ((a:real^2)$1 + b$1)`)] THEN
    USE_THEN "rs" (fun th ->
      let f y h = MP (CONJUNCT1 (CONJUNCT2 (SPEC y th))) h in
      REWRITE_TAC[f `v:real^2` (ASSUME `(v:real^2)$1 = (b:real^2)$1`);
                  f `m:real^2` (ASSUME `(m:real^2)$1 = (b:real^2)$1`);
                  f `v':real^2` (ASSUME `(v':real^2)$1 = (b:real^2)$1`)]) THEN
    REWRITE_TAC[REAL_LT_LADD; (MATCH_MP REAL_LT_DIV2_EQ (ASSUME `&0 < &4 * ((b:real^2)$2 - (a:real^2)$2)`))] THEN
    ASM_REAL_ARITH_TAC;
    (* bottom side: v$2 = v'$2 = a$2 *)
    SUBGOAL_THEN `(m:real^2)$2 = (a:real^2)$2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(v'$1 - (v:real^2)$1) * (inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - v$2) -
      ((v':real^2)$2 - v$2) * (inv(&2) * (a$1 + b$1) - v$1) =
      (v'$1 - v$1) * (inv(&2) * (a$2 + b$2) - a$2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - a$2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP (CONJUNCT2 REAL_LT_MUL_EQ)
      (ASSUME `&0 < inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - a$2`)] THEN
    USE_THEN "rs" (fun th ->
      let f y h = MP (CONJUNCT1 (SPEC y th)) h in
      REWRITE_TAC[f `v:real^2` (ASSUME `(v:real^2)$2 = (a:real^2)$2`);
                  f `m:real^2` (ASSUME `(m:real^2)$2 = (a:real^2)$2`);
                  f `v':real^2` (ASSUME `(v':real^2)$2 = (a:real^2)$2`)]) THEN
    REWRITE_TAC[(MATCH_MP REAL_LT_DIV2_EQ (ASSUME `&0 < &4 * ((b:real^2)$1 - (a:real^2)$1)`))] THEN
    ASM_REAL_ARITH_TAC;
    (* top side: v$2 = v'$2 = b$2 *)
    SUBGOAL_THEN `(m:real^2)$2 = (b:real^2)$2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(v'$1 - (v:real^2)$1) * (inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - v$2) -
      ((v':real^2)$2 - v$2) * (inv(&2) * (a$1 + b$1) - v$1) =
      (v$1 - v'$1) * (b$2 - inv(&2) * (a$2 + b$2))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (b:real^2)$2 - inv(&2) * ((a:real^2)$2 + b$2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP (CONJUNCT2 REAL_LT_MUL_EQ)
      (ASSUME `&0 < (b:real^2)$2 - inv(&2) * ((a:real^2)$2 + b$2)`)] THEN
    USE_THEN "rs" (fun th ->
      let f y h = MP (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (SPEC y th)))) h in
      REWRITE_TAC[f `v:real^2` (ASSUME `(v:real^2)$2 = (b:real^2)$2`);
                  f `m:real^2` (ASSUME `(m:real^2)$2 = (b:real^2)$2`);
                  f `v':real^2` (ASSUME `(v':real^2)$2 = (b:real^2)$2`)]) THEN
    REWRITE_TAC[REAL_LT_LADD; (MATCH_MP REAL_LT_DIV2_EQ (ASSUME `&0 < &4 * ((b:real^2)$1 - (a:real^2)$1)`))] THEN
    ASM_REAL_ARITH_TAC]);;

(* The model side of a frontier segment.  The determinant against the       *)
(* third vertex factors as P * K with K the signed distance of w from the  *)
(* side's line (positive towards the centre).                               *)

let MOI_S3SO_SMALL_T = prove
 (`!X Y1 Y2 Y3. &0 <= X /\ &0 < Y1 /\ &0 < Y2 /\ &0 < Y3
                ==> ?t. &0 < t /\ t <= &1 /\ t * X < Y1 /\ t * X < Y2 /\ t * X < Y3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`Y1:real`; `Y2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`e1:real`; `Y3:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / (X + e)` THEN
  SUBGOAL_THEN `&0 < X + e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `e / (X + e) * X < e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `x / y * z = (x * z) / y`; REAL_LT_LDIV_EQ] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e * e ==> e * X < e * X + e * e`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3SO_TX = prove
 (`!t X x y Y. &0 < t /\ X = abs x + abs y /\ t * X < Y
               ==> abs(t * x) < Y /\ abs(t * y) < Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  SUBGOAL_THEN `&0 <= t * abs x /\ &0 <= t * abs y /\ t * X = t * abs x + t * abs y`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LT_IMP_LE; REAL_ADD_LDISTRIB]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The point m + t (w - m) near the midpoint m of a side, for w on the     *)
(* centre side, lies in the open rectangle (y1, y2, y3 are the bounds).     *)

let moi_s3so_zbox_tac y1 y2 y3 =
  DISCH_THEN(LABEL_TAC "K") THEN
  ABBREV_TAC `m:real^2 = midpoint(v,v')` THEN
  SUBGOAL_THEN `(m:real^2)$1 = ((v:real^2)$1 + (v':real^2)$1) / &2 /\
                m$2 = (v$2 + v'$2) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[midpoint; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X = abs((w:real^2)$1 - (m:real^2)$1) + abs(w$2 - m$2)` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`X:real`; y1; y2; y3] MOI_S3SO_SMALL_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "K" (fun th -> ASSUME_TAC(MATCH_MP REAL_LT_MUL (CONJ (ASSUME `&0 < t`) th))) THEN
  EXISTS_TAC `(m:real^2) + t % (w - m)` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`t:real`; `X:real`; `(w:real^2)$1 - (m:real^2)$1`;
                `(w:real^2)$2 - (m:real^2)$2`] MOI_S3SO_TX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC y1 th) THEN MP_TAC(SPEC y2 th) THEN MP_TAC(SPEC y3 th)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;;

let MOI_S3SO_RECT_SIDE_DET = prove
 (`!a b v v' w:real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ ~(v = v') /\
     segment[v,v'] SUBSET relative_frontier(interval[a,b])
     ==> ?P K Kc. ~(P = &0) /\ &0 < Kc /\
                  moi_s3so_det v v' w = P * K /\
                  moi_s3so_det v v' (midpoint(a,b)) = P * Kc /\
                  (w IN interval[a,b] ==> &0 <= K) /\
                  (&0 < K ==> ?z. z IN convex hull {v,v',w} /\ z IN interval(a,b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `v IN relative_frontier(interval[a:real^2,b]) /\
                v' IN relative_frontier(interval[a,b])` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S3SO_RF_RECT] THEN DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC))
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `~((v:real^2)$1 = (v':real^2)$1 /\ v$2 = v'$2)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(v:real^2 = v')` THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> midpoint(v,v') + t % (w - midpoint(v,v')) IN convex hull {v:real^2,v',w}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM; midpoint] THEN
    MAP_EVERY EXISTS_TAC [`(&1 - t) / &2`; `(&1 - t) / &2`; `t:real`] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3so_det; midpoint; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_ADD_COMPONENT; IN_INTERVAL; DIMINDEX_2; FORALL_2] THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`; `v:real^2`; `v':real^2`] MOI_S3SO_RECT_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`(v:real^2)$2 - (v':real^2)$2`; `(w:real^2)$1 - (a:real^2)$1`;
                          `inv(&2) * ((a:real^2)$1 + (b:real^2)$1) - a$1`];
    MAP_EVERY EXISTS_TAC [`(v':real^2)$2 - (v:real^2)$2`; `(b:real^2)$1 - (w:real^2)$1`;
                          `(b:real^2)$1 - inv(&2) * ((a:real^2)$1 + b$1)`];
    MAP_EVERY EXISTS_TAC [`(v':real^2)$1 - (v:real^2)$1`; `(w:real^2)$2 - (a:real^2)$2`;
                          `inv(&2) * ((a:real^2)$2 + (b:real^2)$2) - a$2`];
    MAP_EVERY EXISTS_TAC [`(v:real^2)$1 - (v':real^2)$1`; `(b:real^2)$2 - (w:real^2)$2`;
                          `(b:real^2)$2 - inv(&2) * ((a:real^2)$2 + b$2)`]] THEN
  (REPEAT CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
     REAL_ARITH_TAC;
     ALL_TAC]) THENL
  [moi_s3so_zbox_tac `(b:real^2)$1 - (a:real^2)$1` `(m:real^2)$2 - (a:real^2)$2`
                     `(b:real^2)$2 - (m:real^2)$2`;
   moi_s3so_zbox_tac `(b:real^2)$1 - (a:real^2)$1` `(m:real^2)$2 - (a:real^2)$2`
                     `(b:real^2)$2 - (m:real^2)$2`;
   moi_s3so_zbox_tac `(b:real^2)$2 - (a:real^2)$2` `(m:real^2)$1 - (a:real^2)$1`
                     `(b:real^2)$1 - (m:real^2)$1`;
   moi_s3so_zbox_tac `(b:real^2)$2 - (a:real^2)$2` `(m:real^2)$1 - (a:real^2)$1`
                     `(b:real^2)$1 - (m:real^2)$1`]);;


let MOI_S3SO_RECT_OUT = prove
 (`!a b v v' w:real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ ~(v = v') /\
     segment[v,v'] SUBSET relative_frontier(interval[a,b]) /\
     w IN interval[a,b] /\ ~collinear {v,v',w}
     ==> (&0 < moi_s3so_det v v' w <=> &0 < moi_s3so_det v v' (midpoint(a,b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`; `v:real^2`; `v':real^2`; `w:real^2`]
    MOI_S3SO_RECT_SIDE_DET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(K = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {v:real^2,v',w}` THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ]);;

let MOI_S3SO_RECT_IN = prove
 (`!a b v v' w:real^2.
     a$1 < b$1 /\ a$2 < b$2 /\ ~(v = v') /\
     segment[v,v'] SUBSET relative_frontier(interval[a,b]) /\
     DISJOINT (convex hull {v,v',w}) (interval(a,b)) /\ ~collinear {v,v',w}
     ==> (&0 < moi_s3so_det v v' w <=> ~(&0 < moi_s3so_det v v' (midpoint(a,b))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`; `v:real^2`; `v':real^2`; `w:real^2`]
    MOI_S3SO_RECT_SIDE_DET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `Kc:real`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(&0 < K)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?z:real^2. z IN convex hull {v,v',w} /\ z IN interval(a,b)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (convex hull {v:real^2,v',w}) (interval(a,b))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(K = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {v:real^2,v',w}` THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P * K = --P * --K` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 13: the frontier circles of the holed disk model: the boundary      *)
(* of the outer rectangle moi_fsb_hq k (model inside, kap = T) and of the   *)
(* hole squares moi_fsb_hc i (model outside, kap = F); they are the         *)
(* components of the frontier.  A PL circle inside G(frontier) is the image *)
(* of one of them.  The orientation rule against the model side.            *)
(* ------------------------------------------------------------------------- *)

let moi_s3so_frect = new_definition
 `moi_s3so_frect k (a:real^2) (b:real^2) kap <=>
    (a = vec 0 /\ b = vector[&4 * &k + &4; &4] /\ kap) \/
    (?i. i < k /\ a = vector[&4 * &i + &2; &1] /\ b = vector[&4 * &i + &4; &3] /\ ~kap)`;;

let MOI_S3SO_FRECT_LT = prove
 (`!k a b kap. moi_s3so_frect k a b kap ==> a$1 < b$1 /\ a$2 < b$2`,
  REWRITE_TAC[moi_s3so_frect] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_2; VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_S3SO_MODEL_CIRCLES = prove
 (`!k. components(frontier(holed_disk_model k)) =
       relative_frontier(moi_fsb_hq k) INSERT
       {relative_frontier(moi_fsb_hc i) | i < k}`,
  GEN_TAC THEN
  SUBGOAL_THEN `frontier(holed_disk_model k) =
                UNIONS (relative_frontier(moi_fsb_hq k) INSERT
                        {relative_frontier(moi_fsb_hc i) | i < k})` SUBST1_TAC THENL
   [REWRITE_TAC[MOI_FSB_HD_FRONTIER; UNIONS_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5C_COMPONENTS_PARTITION THEN
  SUBGOAL_THEN `!a b:real^2. a$1 < b$1 /\ a$2 < b$2
                             ==> closed(relative_frontier(interval[a,b])) /\
                                 connected(relative_frontier(interval[a,b])) /\
                                 ~(relative_frontier(interval[a,b]) = {})`
  (LABEL_TAC "rc") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SO_RECT_FACTS) THEN
    SUBGOAL_THEN `sphere(vec 0:real^2,&1) homeomorphic relative_frontier(interval[a:real^2,b])`
    ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_S3SO_CIRC_CONVEX]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_RELATIVE_FRONTIER_BOUNDED];
      MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`;
                     `relative_frontier(interval[a:real^2,b])`] HOMEOMORPHIC_CONNECTEDNESS) THEN
      ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
      DISCH_TAC THEN
      UNDISCH_TAC `sphere(vec 0:real^2,&1) homeomorphic relative_frontier(interval[a:real^2,b])` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsb_hq; moi_fsb_hc] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
    REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN CONJ_TAC THEN
    TRY GEN_TAC THEN TRY DISCH_TAC THEN USE_THEN "rc" MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_2; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i < k ==> DISJOINT (relative_frontier(interval[vec 0:real^2,vector[&4 * &k + &4; &4]]))
                            (relative_frontier(interval[vector[&4 * &i + &2; &1]:real^2,
                                                        vector[&4 * &i + &4; &3]]))) /\
    (!i j. i < k /\ j < k /\ ~(i = j)
           ==> DISJOINT (relative_frontier(interval[vector[&4 * &i + &2; &1]:real^2,
                                                    vector[&4 * &i + &4; &3]]))
                        (relative_frontier(interval[vector[&4 * &j + &2; &1]:real^2,
                                                    vector[&4 * &j + &4; &3]])))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^2` THEN
    SIMP_TAC[MOI_S3SO_RF_RECT; VECTOR_2; VEC_COMPONENT;
             REAL_ARITH `&0 < &4 * &k + &4 /\ &0 < &4 /\ &4 * &i + &2 < &4 * &i + &4 /\ &1 < &3`]
    THENL
     [SUBGOAL_THEN `&4 * &i + &4 <= &4 * &k` MP_TAC THENL
       [UNDISCH_TAC `(i:num) < k` THEN
        REWRITE_TAC[REAL_ARITH `&4 * &i + &4 <= &4 * &k <=> &i + &1 <= &k`;
                    REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `&i + &1 <= &j \/ &j + &1 <= &i` MP_TAC THENL
       [UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[];
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_SIMP_TAC[];
    ASM_CASES_TAC `i:num = i'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i:num = i'`)) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let MOI_S3SO_FRECT_COMPONENT = prove
 (`!k a b kap. moi_s3so_frect k a b kap
               ==> relative_frontier(interval[a,b]) IN
                   components(frontier(holed_disk_model k))`,
  REWRITE_TAC[MOI_S3SO_MODEL_CIRCLES; moi_s3so_frect; moi_fsb_hq; moi_fsb_hc] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_S3SO_COMPONENT_FRECT = prove
 (`!k c. c IN components(frontier(holed_disk_model k))
         ==> ?a b kap. moi_s3so_frect k a b kap /\ c = relative_frontier(interval[a,b])`,
  REWRITE_TAC[MOI_S3SO_MODEL_CIRCLES; moi_s3so_frect; moi_fsb_hq; moi_fsb_hc;
              IN_INSERT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `vector[&4 * &k + &4; &4]:real^2`; `T`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`vector[&4 * &i + &2; &1]:real^2`;
                          `vector[&4 * &i + &4; &3]:real^2`; `F`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* A PL circle inside G(frontier) is the image of one frontier circle. *)

let MOI_S3SO_FRONT_CIRCLE = prove
 (`!k (G:real^2->real^N) G' A J.
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\ pl_sphere 1 J /\
     J SUBSET IMAGE G (frontier (holed_disk_model k))
     ==> ?a b kap. moi_s3so_frect k a b kap /\
                   IMAGE G (relative_frontier(interval[a,b])) = J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SO_PLH_FACTS) THEN
  SUBGOAL_THEN `frontier(holed_disk_model k) SUBSET holed_disk_model k` ASSUME_TAC THENL
   [MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET A` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `K = IMAGE (G':real^N->real^2) J` THEN
  SUBGOAL_THEN `K SUBSET frontier(holed_disk_model k)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) homeomorphic (J:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S3SO_PL_CIRC]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (J,K) (G':real^N->real^2,G)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`A:real^N->bool`; `holed_disk_model k`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
      ASM_MESON_TAC[pl_homeomorphism];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) homeomorphic (K:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `J:real^N->bool`; `K:real^2->bool`]
      HOMEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (K:real^2->bool) /\ ~(K = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`sphere(vec 0:real^2,&1)`; `K:real^2->bool`] HOMEOMORPHIC_CONNECTEDNESS) THEN
      ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
      DISCH_TAC THEN
      UNDISCH_TAC `sphere(vec 0:real^2,&1) homeomorphic (K:real^2->bool)` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^2` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `connected_component (frontier(holed_disk_model k)) x IN
                components(frontier(holed_disk_model k))` ASSUME_TAC THENL
   [REWRITE_TAC[components; IN_ELIM_THM] THEN EXISTS_TAC `x:real^2` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3SO_COMPONENT_FRECT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kap:bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(K:real^2->bool) SUBSET relative_frontier(interval[a,b])` ASSUME_TAC THENL
   [USE_THEN "cc" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^2->bool) = relative_frontier(interval[a,b])` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_CIRCLE_EQ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3SO_CIRC_CONVEX THEN
    ASM_MESON_TAC[MOI_S3SO_RECT_FACTS; MOI_S3SO_FRECT_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "K" THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> (f:real^N->real^N) x = x) ==> IMAGE f s = s`) THEN
  REWRITE_TAC[o_THM] THEN ASM SET_TAC[]);;

(* The orientation rule against the model side. *)

let MOI_S3SO_MODEL_SIDE = prove
 (`!k a b kap v v' w:real^2.
     moi_s3so_frect k a b kap /\ ~(v = v') /\
     segment[v,v'] SUBSET relative_frontier(interval[a,b]) /\
     convex hull {v,v',w} SUBSET holed_disk_model k /\ ~collinear {v,v',w}
     ==> (&0 < moi_s3so_det v v' w <=>
          (moi_s3ci_cyc3 (moi_s3so_rtau a b v) (moi_s3so_rtau a b (midpoint(v,v')))
                        (moi_s3so_rtau a b v') <=> kap))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SO_FRECT_LT) THEN
  ASM_SIMP_TAC[MOI_S3SO_RECT_CYC] THEN
  UNDISCH_TAC `moi_s3so_frect k a b kap` THEN REWRITE_TAC[moi_s3so_frect] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[ASSUME `kap:bool`] THEN
    MATCH_MP_TAC MOI_S3SO_RECT_OUT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^2) IN holed_disk_model k` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; HULL_INC; IN_INSERT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[holed_disk_model; IN_DIFF] THEN SIMP_TAC[];
    REWRITE_TAC[ASSUME `~kap`] THEN
    MATCH_MP_TAC MOI_S3SO_RECT_IN THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN holed_disk_model k` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[holed_disk_model; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `interval(vector[&4 * &i + &2; &1]:real^2,vector[&4 * &i + &4; &3])` THEN
    CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 14: the local configuration at a common circle.  At a frontier      *)
(* point of the model which is not a vertex of a triangulation, a unique    *)
(* boundary edge contains it, the frontier near it is that edge, and one    *)
(* triangle of the triangulation sits on the edge.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_BEDGE_LOCAL = prove
 (`!(t:(real^2->bool)->bool) k u.
     simplicial_complex t /\ UNIONS t = holed_disk_model k /\
     u IN frontier(holed_disk_model k) /\ ~({u} IN t)
     ==> ?v v' w. ~(v = v') /\ convex hull {v,v'} IN t /\
                  convex hull {v,v',w} IN t /\ ~collinear {v,v',w} /\
                  u IN segment(v,v') /\
                  segment[v,v'] SUBSET frontier(holed_disk_model k) /\
                  (?d. &0 < d /\
                       frontier(holed_disk_model k) INTER ball(u,d) SUBSET segment[v,v'])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `t:(real^2->bool)->bool`] MOI_S3KC_HD_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?e:real^2->bool. e IN moi_fsb_bedges t /\ u IN e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^2) IN frontier(holed_disk_model k)` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
      is_comb(lhs(concl th)) && fst(dest_const(rator(lhs(concl th)))) = "surface_boundary")) THEN
    REWRITE_TAC[MOI_FSB_SB_UNIONS; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `e:real^2->bool`] MOI_FSB_BEDGE_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `tr:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` (X_CHOOSE_THEN `v':real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `e:real^2->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "vert") (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `{v:real^2} IN t /\ {v'} IN t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "vert" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2) IN segment(v,v')` ASSUME_TAC THENL
   [REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                GSYM SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SEGMENT_CONVEX_HULL];
      DISCH_TAC THEN UNDISCH_TAC `~({u:real^2} IN t)` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~({u:real^2} IN t)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the triangle on the edge *)
  SUBGOAL_THEN `(e:real^2->bool) face_of tr` ASSUME_TAC THENL
   [SUBGOAL_THEN `e INTER tr = (e:real^2->bool)` (SUBST1_TAC o SYM) THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `tr:real^2->bool`] MOI_S3SO_VS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2) IN moi_fsa_vs tr /\ v' IN moi_fsa_vs tr` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^2) extreme_point_of e /\ v' extreme_point_of e` MP_TAC THENL
     [UNDISCH_TAC `moi_fsa_vs (e:real^2->bool) = {v,v'}` THEN
      REWRITE_TAC[moi_fsa_vs; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fsa_vs; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`e:real^2->bool`; `tr:real^2->bool`] EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_vs (tr:real^2->bool)`; `v:real^2`; `v':real^2`]
    MOI_S3SO_SIZE3_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex hull {v:real^2,v',w} = tr /\ ~affine_dependent {v:real^2,v',w}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull (moi_fsa_vs tr) = (tr:real^2->bool)` THEN
    UNDISCH_TAC `~affine_dependent (moi_fsa_vs (tr:real^2->bool))` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:real^2`; `v':real^2`; `w:real^2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `(e:real^2->bool) IN t` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
      is_comb(lhs(concl th)) && fst(dest_const(rator(lhs(concl th)))) = "surface_boundary")) THEN
    REWRITE_TAC[MOI_FSB_SB_UNIONS] THEN
    UNDISCH_TAC `(e:real^2->bool) IN moi_fsb_bedges t` THEN
    UNDISCH_TAC `e = convex hull {v:real^2,v'}` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the frontier near u is the edge *)
  ABBREV_TAC `O = UNIONS (moi_fsb_bedges t DELETE (e:real^2->bool))` THEN
  SUBGOAL_THEN `moi_fsb_bedges (t:(real^2->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (t:(real^2->bool)->bool) /\ (!s. s IN t ==> compact s /\ convex s) /\
    (!s s'. s IN t /\ s' IN t ==> (s INTER s') face_of s /\ (s INTER s') face_of s')`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (t:(real^2->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(O:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_DELETE_IMP THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `t:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `e':real^2->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      SUBGOAL_THEN `(e':real^2->bool) IN t` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^2) IN O)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_UNIONS; IN_DELETE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `e':real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^2->bool)->bool`; `e':real^2->bool`] MOI_FSB_BEDGE_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e INTER e':real^2->bool) face_of e /\ (e INTER e') face_of e'`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e INTER e':real^2->bool) = e` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e INTER e':real^2->bool`; `e:real^2->bool`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `relative_interior(convex hull {v:real^2,v'}) = segment(v,v')`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT]; ALL_TAC] THEN
      MP_TAC(ISPECL [`v:real^2`; `v':real^2`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      UNDISCH_TAC `(u:real^2) IN e'` THEN UNDISCH_TAC `(u:real^2) IN segment(v,v')` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^2->bool) face_of e'` ASSUME_TAC THENL
     [UNDISCH_TAC `(e INTER e':real^2->bool) face_of e'` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^2->bool`; `e':real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_SIMP_TAC[INT_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^2) DIFF O` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && fst(dest_const(rator(lhs(concl th)))) = "surface_boundary")) THEN
  REWRITE_TAC[MOI_FSB_SB_UNIONS] THEN
  SUBGOAL_THEN `UNIONS (moi_fsb_bedges t) = (e:real^2->bool) UNION O` SUBST1_TAC THENL
   [EXPAND_TAC "O" THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  UNDISCH_TAC `ball(u:real^2,d) SUBSET (:real^2) DIFF O` THEN
  UNDISCH_TAC `e = convex hull {v:real^2,v'}` THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN SET_TAC[]);;

(* The edge configuration of a refinement adapted to G at a frontier point *)
(* u of a frontier rectangle which is not a vertex of the refinement.       *)

let MOI_S3SO_PIECE_EDGE = prove
 (`!(m:(real^3->bool)->bool) k (G:real^2->real^3) t a b kap u.
     simplicial_complex t /\ UNIONS t = holed_disk_model k /\
     (!s. s IN t ==> ?l y. linear l /\ !x. x IN s ==> G x = l x + y) /\
     (!s. s IN t /\ ~(s = {}) ==> ?kk. kk IN m /\ IMAGE G s SUBSET kk) /\
     moi_s3so_frect k a b kap /\ u IN relative_frontier(interval[a,b]) /\ ~({u} IN t)
     ==> ?v v' w l y kk d.
           ~(v = v') /\ u IN segment(v,v') /\
           segment[v,v'] SUBSET relative_frontier(interval[a,b]) /\
           convex hull {v,v',w} IN t /\ ~collinear {v,v',w} /\
           linear l /\ (!x. x IN convex hull {v,v',w} ==> G x = l x + y) /\
           kk IN m /\ IMAGE G (convex hull {v,v',w}) SUBSET kk /\
           &0 < d /\ frontier(holed_disk_model k) INTER ball(u,d) SUBSET segment[v,v']`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "img")
    STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S3SO_FRECT_COMPONENT) THEN
  SUBGOAL_THEN `(u:real^2) IN frontier(holed_disk_model k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`t:(real^2->bool)->bool`; `k:num`; `u:real^2`] MOI_S3SO_BEDGE_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` (X_CHOOSE_THEN `v':real^2` (X_CHOOSE_THEN `w:real^2`
    STRIP_ASSUME_TAC))) THEN
  USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `convex hull {v:real^2,v',w} IN t`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "img" (MP_TAC o SPEC `convex hull {v:real^2,v',w}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:real^2`; `v':real^2`; `w:real^2`; `l:real^2->real^3`; `y:real^3`;
                        `kk:real^3->bool`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `frontier(holed_disk_model k)` THEN ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `u:real^2` THEN
  REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]);;

let MOI_S3SO_RF_INFINITE = prove
 (`!a b:real^2. a$1 < b$1 /\ a$2 < b$2 ==> INFINITE(relative_frontier(interval[a,b]))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(segment[a:real^2,vector[(b:real^2)$1; a$2]])` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `relative_frontier(interval[a:real^2,b])` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUBSET; MOI_S3SO_RF_RECT; IN_SEGMENT] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    SUBGOAL_THEN `&0 <= s * ((b:real^2)$1 - (a:real^2)$1) /\ s * (b$1 - a$1) <= b$1 - a$1`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[FINITE_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC]);;

(* Relative interior points of image triangles avoid the image of the       *)
(* frontier.                                                                 *)

let MOI_S3SO_IMG_RELINT_OFF = prove
 (`!k (G:real^2->real^3) G' A C J u v w l y.
     pl_homeomorphism (holed_disk_model k,A) (G,G') /\
     C SUBSET frontier(holed_disk_model k) /\ IMAGE G C = J /\
     ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k /\
     linear l /\ (!x. x IN convex hull {u,v,w} ==> G x = l x + y)
     ==> relative_interior(convex hull {G u,G v,G w}) SUBSET A DIFF J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SO_PLH_FACTS) THEN
  SUBGOAL_THEN `frontier(holed_disk_model k) SUBSET holed_disk_model k` ASSUME_TAC THENL
   [MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {(G:real^2->real^3) u,G v,G w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior(convex hull {u:real^2,v,w}) SUBSET
                interior(holed_disk_model k)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior(convex hull {u:real^2,v,w})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `s = t ==> (s:real^2->bool) SUBSET t`) THEN
      MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
      REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_SIMP_TAC[MOI_S3SO_NONCOL_DIM];
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^2->real^3`; `l:real^2->real^3`; `y:real^3`; `u:real^2`; `v:real^2`;
                 `w:real^2`; `q:real^3`] MOI_S3SO_AFF_RELINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^2) IN interior(holed_disk_model k)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN holed_disk_model k /\ ~(z IN frontier(holed_disk_model k))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `holed_disk_model k` INTERIOR_SUBSET) THEN
    REWRITE_TAC[frontier] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (G:real^2->real^3) C = J` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^2) = c` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try
      let v = fst(dest_forall(concl th)) in fst(dest_var v) = "x" &&
      length(fst(strip_forall(concl th))) = 2 with Failure _ -> false)) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 15: the local configuration at a generic point of the common       *)
(* frontier circle J of two embedded models.  Sub-segments of an edge,     *)
(* midpoints under affine maps, a short symmetric pair around a point of   *)
(* an open segment, continuity of the transition map along an edge, and    *)
(* the core sign computation (LC_CORE).                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_DET_SEG = prove
 (`!v v' w:real^2 a b.
     moi_s3so_det ((&1 - a) % v + a % v') ((&1 - b) % v + b % v') w =
     (b - a) * moi_s3so_det v v' w`,
  REWRITE_TAC[moi_s3so_det; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* Two distinct points of an edge of a triangle span a sub-triangle with   *)
(* the same third vertex.                                                   *)

let MOI_S3SO_SEG_SUBTRI = prove
 (`!v v' w x y:real^2.
     ~collinear {v,v',w} /\ x IN segment[v,v'] /\ y IN segment[v,v'] /\ ~(x = y)
     ==> ~collinear {x,y,w} /\ convex hull {x,y,w} SUBSET convex hull {v,v',w} /\
         segment[x,y] SUBSET segment[v,v']`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[x:real^2,y] SUBSET segment[v,v']` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_SEGMENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN segment[v,v']` THEN
    UNDISCH_TAC `(y:real^2) IN segment[v,v']` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(x:real^2 = y)` THEN UNDISCH_TAC `~collinear {v:real^2,v',w}` THEN
    ASM_REWRITE_TAC[MOI_S3SO_COLLINEAR_DET; MOI_S3SO_DET_SEG; REAL_ENTIRE] THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_SUB_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  SUBGOAL_THEN `segment[v:real^2,v'] SUBSET convex hull {v,v',w}` MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex:(real^2->bool)->bool`; `{v:real^2,v',w}`] HULL_SUBSET) THEN
  UNDISCH_TAC `(x:real^2) IN segment[v,v']` THEN
  UNDISCH_TAC `(y:real^2) IN segment[v,v']` THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN SET_TAC[]);;

(* A map affine on a set commutes with midpoints in the set. *)

let MOI_S3SO_AFF_MID = prove
 (`!(f:real^M->real^N) l y s a b.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\
     a IN s /\ b IN s /\ midpoint(a,b) IN s
     ==> f(midpoint(a,b)) = midpoint(f a,f b)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[midpoint] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;

(* Around a point of an open segment: two distinct close points of the     *)
(* closed segment with the given point as midpoint.                          *)

let MOI_S3SO_SEG_PAIR = prove
 (`!v v' u:real^N e.
     u IN segment(v,v') /\ &0 < e
     ==> ?x y. x IN segment[v,v'] /\ y IN segment[v,v'] /\ ~(x = y) /\
               midpoint(x,y) = u /\ dist(x,u) < e /\ dist(y,u) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(v' - v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:real`; `&1 - s`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `e / norm(v' - v:real^N)`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t * norm(v' - v:real^N) < e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(u:real^N) - t % (v' - v)`; `(u:real^N) + t % (v' - v)`] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `s - t:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    EXISTS_TAC `s + t:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    REWRITE_TAC[VECTOR_ARITH `u - t % d:real^N = u + t % d <=> t % d = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[dist; VECTOR_ARITH `(u - t % d) - u:real^N = --(t % d)`; NORM_NEG] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
    REWRITE_TAC[dist; VECTOR_ARITH `(u + t % d) - u:real^N = t % d`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`]]);;

(* A continuous map into a set whose part near the image point lies in a   *)
(* segment: points close to the base point go into the segment.            *)

let MOI_S3SO_CONT_SEG = prove
 (`!(H:real^M->real^N) S S2 F2 u u2 d2.
     H continuous_on S /\ u IN S /\ H u = u2 /\ &0 < d2 /\
     (!z. z IN S ==> H z IN F2) /\ F2 INTER ball(u2,d2) SUBSET S2
     ==> ?e. &0 < e /\ !z. z IN S /\ dist(z,u) < e ==> H z IN S2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(H:real^M->real^N) continuous_on S` THEN REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `d2:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(H:real^M->real^N) z IN F2 INTER ball(u2,d2)` MP_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN REMOVE_THEN "c" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `F2 INTER ball(u2:real^N,d2) SUBSET S2` THEN SET_TAC[]]);;

(* The core sign computation: an A1-triangle and an A2-triangle on a       *)
(* common short segment of J (images of model edges on the frontier        *)
(* circles) have opposite POS; with the sign constants and the side rule   *)
(* of the models this relates the two circle orientations of the segment.  *)

let MOI_S3SO_LC_CORE = prove
 (`!(m:(real^3->bool)->bool) i k1 k2 (G1:real^2->real^3) G1' (G2:real^2->real^3) G2'
    (A1:real^3->bool) A2 J a1 b1 kap1 a2 b2 kap2 bb1 bb2
    U0 U2 w1 (l1:real^2->real^3) y1 kk1 V0 V2 w2 (l2:real^2->real^3) y2 kk2.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     pl_homeomorphism (holed_disk_model k1,A1) (G1,G1') /\
     pl_homeomorphism (holed_disk_model k2,A2) (G2,G2') /\ A1 INTER A2 = J /\
     moi_s3so_frect k1 a1 b1 kap1 /\ IMAGE G1 (relative_frontier(interval[a1,b1])) = J /\
     moi_s3so_frect k2 a2 b2 kap2 /\ IMAGE G2 (relative_frontier(interval[a2,b2])) = J /\
     ~(U0 = U2) /\ segment[U0,U2] SUBSET relative_frontier(interval[a1,b1]) /\
     ~collinear {U0,U2,w1} /\ convex hull {U0,U2,w1} SUBSET holed_disk_model k1 /\
     linear l1 /\ (!x. x IN convex hull {U0,U2,w1} ==> G1 x = l1 x + y1) /\
     kk1 IN m /\ IMAGE G1 (convex hull {U0,U2,w1}) SUBSET kk1 /\
     ~(V0 = V2) /\ segment[V0,V2] SUBSET relative_frontier(interval[a2,b2]) /\
     ~collinear {V0,V2,w2} /\ convex hull {V0,V2,w2} SUBSET holed_disk_model k2 /\
     linear l2 /\ (!x. x IN convex hull {V0,V2,w2} ==> G2 x = l2 x + y2) /\
     kk2 IN m /\ IMAGE G2 (convex hull {V0,V2,w2}) SUBSET kk2 /\
     G2 V0 = G1 U0 /\ G2 V2 = G1 U2 /\
     ((moi_s3so_pos i (G1 U0) (G1 U2) (G1 w1) <=> &0 < moi_s3so_det U0 U2 w1) <=> bb1) /\
     ((moi_s3so_pos i (G2 V0) (G2 V2) (G2 w2) <=> &0 < moi_s3so_det V0 V2 w2) <=> bb2)
     ==> (moi_s3ci_cyc3 (moi_s3so_rtau a2 b2 V0) (moi_s3so_rtau a2 b2 (midpoint(V0,V2)))
                       (moi_s3so_rtau a2 b2 V2) <=>
          (moi_s3ci_cyc3 (moi_s3so_rtau a1 b1 U0) (moi_s3so_rtau a1 b1 (midpoint(U0,U2)))
                        (moi_s3so_rtau a1 b1 U2) <=>
           ~(kap1 <=> bb1 <=> kap2 <=> bb2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k1`; `A1:real^3->bool`; `G1:real^2->real^3`;
                 `G1':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k2`; `A2:real^3->bool`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier(interval[a1:real^2,b1]) SUBSET
                frontier(holed_disk_model k1) /\
                relative_frontier(interval[a2:real^2,b2]) SUBSET
                frontier(holed_disk_model k2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN
    MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(G1:real^2->real^3) U0,G1 U2,G1 w1} SUBSET kk1 /\
                ~collinear {(G1:real^2->real^3) U0,G1 U2,G1 w1} /\
                relative_interior(convex hull {(G1:real^2->real^3) U0,G1 U2,G1 w1})
                SUBSET A1 DIFF J` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`G1:real^2->real^3`; `l1:real^2->real^3`; `y1:real^3`;
                     `{U0:real^2,U2,w1}`] MOI_S3SO_AFF_IMAGE_HULL) THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
      MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `y1:real^3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {U0:real^2,U2,w1} SUBSET holed_disk_model k1` THEN
      UNDISCH_TAC `!x x'. x IN holed_disk_model k1 /\ x' IN holed_disk_model k1 /\
                          (G1:real^2->real^3) x = G1 x' ==> x = x'` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S3SO_IMG_RELINT_OFF THEN
      MAP_EVERY EXISTS_TAC [`k1:num`; `G1':real^3->real^2`;
                            `relative_frontier(interval[a1:real^2,b1])`;
                            `l1:real^2->real^3`; `y1:real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(G1:real^2->real^3) U0,G1 U2,(G2:real^2->real^3) w2}
                SUBSET kk2 /\
                ~collinear {(G1:real^2->real^3) U0,G1 U2,(G2:real^2->real^3) w2} /\
                relative_interior(convex hull {(G1:real^2->real^3) U0,G1 U2,
                                               (G2:real^2->real^3) w2})
                SUBSET A2 DIFF J` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(G2:real^2->real^3) V0 = (G1:real^2->real^3) U0`)) THEN
    SUBST1_TAC(SYM(ASSUME `(G2:real^2->real^3) V2 = (G1:real^2->real^3) U2`)) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`G2:real^2->real^3`; `l2:real^2->real^3`; `y2:real^3`;
                     `{V0:real^2,V2,w2}`] MOI_S3SO_AFF_IMAGE_HULL) THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3SO_AFF_NONCOL THEN
      MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `y2:real^3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {V0:real^2,V2,w2} SUBSET holed_disk_model k2` THEN
      UNDISCH_TAC `!x x'. x IN holed_disk_model k2 /\ x' IN holed_disk_model k2 /\
                          (G2:real^2->real^3) x = G2 x' ==> x = x'` THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S3SO_IMG_RELINT_OFF THEN
      MAP_EVERY EXISTS_TAC [`k2:num`; `G2':real^3->real^2`;
                            `relative_frontier(interval[a2:real^2,b2])`;
                            `l2:real^2->real^3`; `y2:real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:num`; `a1:real^2`; `b1:real^2`; `kap1:bool`; `U0:real^2`; `U2:real^2`;
                 `w1:real^2`] MOI_S3SO_MODEL_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k2:num`; `a2:real^2`; `b2:real^2`; `kap2:bool`; `V0:real^2`; `V2:real^2`;
                 `w2:real^2`] MOI_S3SO_MODEL_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `(G1:real^2->real^3) U0`;
                 `(G1:real^2->real^3) U2`; `(G1:real^2->real^3) w1`;
                 `(G2:real^2->real^3) w2`; `kk1:real^3->bool`; `kk2:real^3->bool`]
    MOI_S3SO_TRI_ADJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN
    UNDISCH_TAC `relative_interior(convex hull {(G1:real^2->real^3) U0,G1 U2,
                                                (G2:real^2->real^3) w2})
                 SUBSET A2 DIFF J` THEN
    UNDISCH_TAC `relative_interior(convex hull {(G1:real^2->real^3) U0,G1 U2,G1 w1})
                 SUBSET A1 DIFF J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(moi_s3so_pos i ((G2:real^2->real^3) V0) (G2 V2) (G2 w2) <=>
                &0 < moi_s3so_det V0 V2 w2) <=> bb2` THEN
  UNDISCH_TAC `(moi_s3so_pos i ((G1:real^2->real^3) U0) (G1 U2) (G1 w1) <=>
                &0 < moi_s3so_det U0 U2 w1) <=> bb1` THEN
  REWRITE_TAC[ASSUME `(G2:real^2->real^3) V0 = (G1:real^2->real^3) U0`;
              ASSUME `(G2:real^2->real^3) V2 = (G1:real^2->real^3) U2`] THEN
  CONV_TAC TAUT);;

(* The local configuration at a generic point of J: preimages off the    *)
(* vertices of the refinements, boundary edges on both sides, a short      *)
(* symmetric pair around the point, and the core sign computation.        *)

let MOI_S3SO_LOCAL_CONFIG = prove
 (`!(m:(real^3->bool)->bool) i k1 k2 (G1:real^2->real^3) G1' (G2:real^2->real^3) G2'
    (A1:real^3->bool) A2 J t1 t2 a1 b1 kap1 a2 b2 kap2 bb1 bb2.
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     A1 SUBSET UNIONS m /\ A2 SUBSET UNIONS m /\
     pl_homeomorphism (holed_disk_model k1,A1) (G1,G1') /\
     pl_homeomorphism (holed_disk_model k2,A2) (G2,G2') /\ A1 INTER A2 = J /\
     moi_s3so_frect k1 a1 b1 kap1 /\ IMAGE G1 (relative_frontier(interval[a1,b1])) = J /\
     moi_s3so_frect k2 a2 b2 kap2 /\ IMAGE G2 (relative_frontier(interval[a2,b2])) = J /\
     simplicial_complex t1 /\ UNIONS t1 = holed_disk_model k1 /\
     (!s. s IN t1 ==> ?l y. linear l /\ !x. x IN s ==> G1 x = l x + y) /\
     (!s. s IN t1 /\ ~(s = {}) ==> ?kk. kk IN m /\ IMAGE G1 s SUBSET kk) /\
     simplicial_complex t2 /\ UNIONS t2 = holed_disk_model k2 /\
     (!s. s IN t2 ==> ?l y. linear l /\ !x. x IN s ==> G2 x = l x + y) /\
     (!s. s IN t2 /\ ~(s = {}) ==> ?kk. kk IN m /\ IMAGE G2 s SUBSET kk) /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k1 /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G1 x = l x + y)
                  ==> ((moi_s3so_pos i (G1 u) (G1 v) (G1 w) <=> &0 < moi_s3so_det u v w) <=>
                       bb1)) /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k2 /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G2 x = l x + y)
                  ==> ((moi_s3so_pos i (G2 u) (G2 v) (G2 w) <=> &0 < moi_s3so_det u v w) <=>
                       bb2))
     ==> ?p0 p2. p0 IN J /\ p2 IN J /\ ~(p0 = p2) /\ midpoint(p0,p2) IN J /\
                 (moi_s3ci_cyc3 (moi_s3so_rtau a2 b2 (G2' p0))
                               (moi_s3so_rtau a2 b2 (G2' (midpoint(p0,p2))))
                               (moi_s3so_rtau a2 b2 (G2' p2)) <=>
                  (moi_s3ci_cyc3 (moi_s3so_rtau a1 b1 (G1' p0))
                                (moi_s3so_rtau a1 b1 (G1' (midpoint(p0,p2))))
                                (moi_s3so_rtau a1 b1 (G1' p2)) <=>
                   ~(kap1 <=> bb1 <=> kap2 <=> bb2)))`,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff1") (CONJUNCTS_THEN2 (LABEL_TAC "img1")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "aff2") (CONJUNCTS_THEN2 (LABEL_TAC "img2")
    (CONJUNCTS_THEN2 (LABEL_TAC "s1") (LABEL_TAC "s2"))))))))))))))))))))))) THEN
  (MP_TAC(ISPECL [`holed_disk_model k1`; `A1:real^3->bool`; `G1:real^2->real^3`;
                 `G1':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k2`; `A2:real^3->bool`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `relative_frontier(interval[a1:real^2,b1]) SUBSET frontier(holed_disk_model k1) /\
                relative_frontier(interval[a2:real^2,b2]) SUBSET frontier(holed_disk_model k2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN
    MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THENL
     [EXISTS_TAC `kap1:bool`; EXISTS_TAC `kap2:bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(holed_disk_model k1) SUBSET holed_disk_model k1 /\
                frontier(holed_disk_model k2) SUBSET holed_disk_model k2` STRIP_ASSUME_TAC
  THENL [MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]; ALL_TAC]) THEN
  (SUBGOAL_THEN `(J:real^3->bool) SUBSET A1 /\ J SUBSET A2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `INFINITE (J:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (G1:real^2->real^3) (relative_frontier(interval[a1,b1])) = J` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INFINITE_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3SO_RF_INFINITE THEN MATCH_MP_TAC MOI_S3SO_FRECT_LT THEN
      MAP_EVERY EXISTS_TAC [`k1:num`; `kap1:bool`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`!x x'. x IN holed_disk_model k1 /\ x' IN holed_disk_model k1 /\
                (G1:real^2->real^3) x = G1 x' ==> x = x'`;
        `relative_frontier(interval[a1:real^2,b1]) SUBSET frontier(holed_disk_model k1)`;
        `frontier(holed_disk_model k1) SUBSET holed_disk_model k1`] THEN
      SET_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `FINITE (IMAGE (G1:real^2->real^3) {u | {u} IN t1} UNION
                        IMAGE (G2:real^2->real^3) {u | {u} IN t2})` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[SET_RULE `{x:real^2} = {y} <=> x = y`] THEN
    MESON_TAC[simplicial_complex; ASSUME `simplicial_complex (t1:(real^2->bool)->bool)`;
              ASSUME `simplicial_complex (t2:(real^2->bool)->bool)`];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `?x0:real^3. x0 IN J /\ ~({(G1':real^3->real^2) x0} IN t1) /\ ~({(G2':real^3->real^2) x0} IN t2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J:real^3->bool`;
                   `IMAGE (G1:real^2->real^3) {u | {u} IN t1} UNION
                    IMAGE (G2:real^2->real^3) {u | {u} IN t2}`] INFINITE_DIFF_FINITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THENL
     [DISJ1_TAC THEN EXISTS_TAC `(G1':real^3->real^2) x` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN J` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET A1` THEN
      SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `(G2':real^3->real^2) x` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN J` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET A2` THEN
      SET_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!y. y IN J ==> (G1':real^3->real^2) y IN relative_frontier(interval[a1,b1]) /\
                                (G2':real^3->real^2) y IN relative_frontier(interval[a2,b2])`
  (LABEL_TAC "Jpre") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN J` THEN
      UNDISCH_TAC `IMAGE (G1:real^2->real^3) (relative_frontier(interval[a1,b1])) = J` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(c:real^2) IN holed_disk_model k1` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(c:real^2) IN relative_frontier(interval[a1,b1])`;
          `relative_frontier(interval[a1:real^2,b1]) SUBSET frontier(holed_disk_model k1)`;
          `frontier(holed_disk_model k1) SUBSET holed_disk_model k1`] THEN
        SET_TAC[];
        ASM_SIMP_TAC[]];
      UNDISCH_TAC `(y:real^3) IN J` THEN
      UNDISCH_TAC `IMAGE (G2:real^2->real^3) (relative_frontier(interval[a2,b2])) = J` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(c:real^2) IN holed_disk_model k2` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(c:real^2) IN relative_frontier(interval[a2,b2])`;
          `relative_frontier(interval[a2:real^2,b2]) SUBSET frontier(holed_disk_model k2)`;
          `frontier(holed_disk_model k2) SUBSET holed_disk_model k2`] THEN
        SET_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k1:num`; `G1:real^2->real^3`;
                 `t1:(real^2->bool)->bool`; `a1:real^2`; `b1:real^2`; `kap1:bool`;
                 `(G1':real^3->real^2) x0`] MOI_S3SO_PIECE_EDGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v1':real^2` (X_CHOOSE_THEN `w1:real^2`
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
    (X_CHOOSE_THEN `kk1:real^3->bool` (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)))))))) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `k2:num`; `G2:real^2->real^3`;
                 `t2:(real^2->bool)->bool`; `a2:real^2`; `b2:real^2`; `kap2:bool`;
                 `(G2':real^3->real^2) x0`] MOI_S3SO_PIECE_EDGE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^2` (X_CHOOSE_THEN `v2':real^2` (X_CHOOSE_THEN `w2:real^2`
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3`
    (X_CHOOSE_THEN `kk2:real^3->bool` (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)))))))) THEN
  (SUBGOAL_THEN `(G1:real^2->real^3) ((G1':real^3->real^2) x0) = x0 /\
                (G2:real^2->real^3) ((G2':real^3->real^2) x0) = x0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x0:real^3) IN A1 /\ x0 IN A2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x0:real^3) IN J` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET A1` THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET A2` THEN SET_TAC[];
      CONJ_TAC THENL
       [MATCH_MP_TAC(ASSUME `!y. y IN A1 ==> (G1:real^2->real^3) ((G1':real^3->real^2) y) = y`);
        MATCH_MP_TAC(ASSUME `!y. y IN A2 ==> (G2:real^2->real^3) ((G2':real^3->real^2) y) = y`)]
      THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `segment[v1:real^2,v1'] SUBSET holed_disk_model k1 /\
                convex hull {v1:real^2,v1',w1} SUBSET holed_disk_model k1 /\
                convex hull {v2:real^2,v2',w2} SUBSET holed_disk_model k2 /\
                segment[v1:real^2,v1'] SUBSET convex hull {v1,v1',w1} /\
                segment[v2:real^2,v2'] SUBSET convex hull {v2,v2',w2} /\
                (!z. z IN segment[v1,v1'] ==> (G1:real^2->real^3) z IN J)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`segment[v1:real^2,v1'] SUBSET relative_frontier(interval[a1,b1])`;
        `relative_frontier(interval[a1:real^2,b1]) SUBSET frontier(holed_disk_model k1)`;
        `frontier(holed_disk_model k1) SUBSET holed_disk_model k1`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`convex hull {v1:real^2,v1',w1} IN t1`;
                             `UNIONS t1 = holed_disk_model k1`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`convex hull {v2:real^2,v2',w2} IN t2`;
                             `UNIONS t2 = holed_disk_model k2`] THEN SET_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[v1:real^2,v1'] SUBSET relative_frontier(interval[a1,b1])`;
        `IMAGE (G1:real^2->real^3) (relative_frontier(interval[a1,b1])) = J`] THEN
      SET_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(G1:real^2->real^3) continuous_on holed_disk_model k1 /\
                (G2':real^3->real^2) continuous_on A2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (holed_disk_model k1,A1) (G1:real^2->real^3,G1')`) THEN
    MP_TAC(ASSUME `pl_homeomorphism (holed_disk_model k2,A2) (G2:real^2->real^3,G2')`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`(G2':real^3->real^2) o (G1:real^2->real^3)`; `segment[v1:real^2,v1']`;
                 `segment[v2:real^2,v2']`; `frontier(holed_disk_model k2)`;
                 `(G1':real^3->real^2) x0`; `(G2':real^3->real^2) x0`; `d2:real`]
    MOI_S3SO_CONT_SEG) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `holed_disk_model k1` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `A2:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!z. z IN segment[v1:real^2,v1'] ==> (G1:real^2->real^3) z IN J` THEN
        UNDISCH_TAC `(J:real^3->bool) SUBSET A2` THEN SET_TAC[]];
      MP_TAC(ISPECL [`v1:real^2`; `v1':real^2`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `(G1':real^3->real^2) x0 IN segment(v1,v1')` THEN SET_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(G1:real^2->real^3) z IN J` ASSUME_TAC THENL
       [MATCH_MP_TAC(ASSUME `!z. z IN segment[v1:real^2,v1'] ==> (G1:real^2->real^3) z IN J`)
        THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "Jpre" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(G1:real^2->real^3) z IN J`))) THEN
      UNDISCH_TAC `relative_frontier(interval[a2:real^2,b2]) SUBSET
                   frontier(holed_disk_model k2)` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs")))]) THEN
  (MP_TAC(ISPECL [`v1:real^2`; `v1':real^2`; `(G1':real^3->real^2) x0`; `e:real`]
    MOI_S3SO_SEG_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:real^2` (X_CHOOSE_THEN `U2:real^2` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `(G2':real^3->real^2) ((G1:real^2->real^3) U0) IN segment[v2,v2'] /\
                (G2':real^3->real^2) ((G1:real^2->real^3) U2) IN segment[v2,v2']`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "cs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `(G1:real^2->real^3) U0 IN J /\ (G1:real^2->real^3) U2 IN J /\
                (G1:real^2->real^3) U0 IN A2 /\ (G1:real^2->real^3) U2 IN A2 /\
                (U0:real^2) IN holed_disk_model k1 /\ (U2:real^2) IN holed_disk_model k1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`!z. z IN segment[v1:real^2,v1'] ==> (G1:real^2->real^3) z IN J`;
      `(J:real^3->bool) SUBSET A2`; `(U0:real^2) IN segment[v1,v1']`;
      `(U2:real^2) IN segment[v1,v1']`;
      `segment[v1:real^2,v1'] SUBSET holed_disk_model k1`] THEN
    SET_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~((G1:real^2->real^3) U0 = G1 U2) /\
                (G2:real^2->real^3) ((G2':real^3->real^2) ((G1:real^2->real^3) U0)) = G1 U0 /\
                (G2:real^2->real^3) ((G2':real^3->real^2) ((G1:real^2->real^3) U2)) = G1 U2 /\
                (G1':real^3->real^2) ((G1:real^2->real^3) U0) = U0 /\
                (G1':real^3->real^2) ((G1:real^2->real^3) U2) = U2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(U0:real^2 = U2)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(ASSUME `!x x'. x IN holed_disk_model k1 /\ x' IN holed_disk_model k1 /\
                                  (G1:real^2->real^3) x = G1 x' ==> x = x'`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!y. y IN A2 ==> (G2:real^2->real^3) ((G2':real^3->real^2) y) = y`)
      THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!y. y IN A2 ==> (G2:real^2->real^3) ((G2':real^3->real^2) y) = y`)
      THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!x. x IN holed_disk_model k1
                               ==> (G1':real^3->real^2) ((G1:real^2->real^3) x) = x`)
      THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!x. x IN holed_disk_model k1
                               ==> (G1':real^3->real^2) ((G1:real^2->real^3) x) = x`)
      THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `~((G2':real^3->real^2) ((G1:real^2->real^3) U0) = G2' (G1 U2))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `G2:real^2->real^3`) THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (ABBREV_TAC `V0 = (G2':real^3->real^2) ((G1:real^2->real^3) U0)` THEN
  ABBREV_TAC `V2 = (G2':real^3->real^2) ((G1:real^2->real^3) U2)`) THEN
  (MP_TAC(ISPECL [`v1:real^2`; `v1':real^2`; `w1:real^2`; `U0:real^2`; `U2:real^2`]
    MOI_S3SO_SEG_SUBTRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`v2:real^2`; `v2':real^2`; `w2:real^2`; `V0:real^2`; `V2:real^2`]
    MOI_S3SO_SEG_SUBTRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  (SUBGOAL_THEN `segment[U0:real^2,U2] SUBSET relative_frontier(interval[a1,b1]) /\
                convex hull {U0:real^2,U2,w1} SUBSET holed_disk_model k1 /\
                (!x. x IN convex hull {U0,U2,w1} ==> (G1:real^2->real^3) x = l1 x + y1) /\
                IMAGE (G1:real^2->real^3) (convex hull {U0,U2,w1}) SUBSET kk1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`segment[U0:real^2,U2] SUBSET segment[v1,v1']`;
      `convex hull {U0:real^2,U2,w1} SUBSET convex hull {v1,v1',w1}`;
      `segment[v1:real^2,v1'] SUBSET relative_frontier(interval[a1,b1])`;
      `convex hull {v1:real^2,v1',w1} SUBSET holed_disk_model k1`;
      `!x. x IN convex hull {v1:real^2,v1',w1} ==> (G1:real^2->real^3) x = l1 x + y1`;
      `IMAGE (G1:real^2->real^3) (convex hull {v1,v1',w1}) SUBSET kk1`] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `segment[V0:real^2,V2] SUBSET relative_frontier(interval[a2,b2]) /\
                convex hull {V0:real^2,V2,w2} SUBSET holed_disk_model k2 /\
                (!x. x IN convex hull {V0,V2,w2} ==> (G2:real^2->real^3) x = l2 x + y2) /\
                IMAGE (G2:real^2->real^3) (convex hull {V0,V2,w2}) SUBSET kk2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`segment[V0:real^2,V2] SUBSET segment[v2,v2']`;
      `convex hull {V0:real^2,V2,w2} SUBSET convex hull {v2,v2',w2}`;
      `segment[v2:real^2,v2'] SUBSET relative_frontier(interval[a2,b2])`;
      `convex hull {v2:real^2,v2',w2} SUBSET holed_disk_model k2`;
      `!x. x IN convex hull {v2:real^2,v2',w2} ==> (G2:real^2->real^3) x = l2 x + y2`;
      `IMAGE (G2:real^2->real^3) (convex hull {v2,v2',w2}) SUBSET kk2`] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `midpoint(U0:real^2,U2) IN convex hull {U0,U2,w1} /\
                midpoint(V0:real^2,V2) IN convex hull {V0,V2,w2}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U0:real^2`; `U2:real^2`] (CONJUNCT1 MIDPOINT_IN_SEGMENT));
      MP_TAC(ISPECL [`V0:real^2`; `V2:real^2`] (CONJUNCT1 MIDPOINT_IN_SEGMENT))] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^2) IN s ==> x IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(U0:real^2) IN convex hull {U0,U2,w1} /\ (U2:real^2) IN convex hull {U0,U2,w1} /\
                (V0:real^2) IN convex hull {V0,V2,w2} /\ (V2:real^2) IN convex hull {V0,V2,w2}`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC]) THEN
  (SUBGOAL_THEN `midpoint((G1:real^2->real^3) U0,G1 U2) = x0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G1:real^2->real^3`; `l1:real^2->real^3`; `y1:real^3`;
                   `convex hull {U0:real^2,U2,w1}`; `U0:real^2`; `U2:real^2`]
      MOI_S3SO_AFF_MID) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `midpoint(U0:real^2,U2) = (G1':real^3->real^2) x0`;
                ASSUME `(G1:real^2->real^3) ((G1':real^3->real^2) x0) = x0`] THEN
    MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `midpoint(V0:real^2,V2) = (G2':real^3->real^2) x0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G2:real^2->real^3`; `l2:real^2->real^3`; `y2:real^3`;
                   `convex hull {V0:real^2,V2,w2}`; `V0:real^2`; `V2:real^2`]
      MOI_S3SO_AFF_MID) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(G2:real^2->real^3) V0 = (G1:real^2->real^3) U0`;
                ASSUME `(G2:real^2->real^3) V2 = (G1:real^2->real^3) U2`;
                ASSUME `midpoint((G1:real^2->real^3) U0,G1 U2) = x0`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ASSUME `!x. x IN holed_disk_model k2
                             ==> (G2':real^3->real^2) ((G2:real^2->real^3) x) = x`) THEN
    UNDISCH_TAC `midpoint(V0:real^2,V2) IN convex hull {V0,V2,w2}` THEN
    UNDISCH_TAC `convex hull {V0:real^2,V2,w2} SUBSET holed_disk_model k2` THEN SET_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `(moi_s3so_pos i ((G1:real^2->real^3) U0) (G1 U2) (G1 w1) <=>
                 &0 < moi_s3so_det U0 U2 w1) <=> bb1` ASSUME_TAC THENL
   [USE_THEN "s1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `y1:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s3so_pos i ((G2:real^2->real^3) V0) (G2 V2) (G2 w2) <=>
                 &0 < moi_s3so_det V0 V2 w2) <=> bb2` ASSUME_TAC THENL
   [USE_THEN "s2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `y2:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (EXISTS_TAC `(G1:real^2->real^3) U0` THEN EXISTS_TAC `(G1:real^2->real^3) U2` THEN
  REWRITE_TAC[ASSUME `midpoint((G1:real^2->real^3) U0,G1 U2) = x0`] THEN
  REWRITE_TAC[ASSUME `(G2':real^3->real^2) ((G1:real^2->real^3) U0) = V0`;
              ASSUME `(G2':real^3->real^2) ((G1:real^2->real^3) U2) = V2`;
              ASSUME `(G1':real^3->real^2) ((G1:real^2->real^3) U0) = U0`;
              ASSUME `(G1':real^3->real^2) ((G1:real^2->real^3) U2) = U2`;
              SYM(ASSUME `midpoint(V0:real^2,V2) = (G2':real^3->real^2) x0`);
              SYM(ASSUME `midpoint(U0:real^2,U2) = (G1':real^3->real^2) x0`)] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k1:num`; `k2:num`;
                       `G1:real^2->real^3`; `G1':real^3->real^2`; `G2:real^2->real^3`;
                       `G2':real^3->real^2`; `A1:real^3->bool`; `A2:real^3->bool`;
                       `J:real^3->bool`; `a1:real^2`; `b1:real^2`; `kap1:bool`;
                       `a2:real^2`; `b2:real^2`; `kap2:bool`; `bb1:bool`; `bb2:bool`;
                       `U0:real^2`; `U2:real^2`; `w1:real^2`; `l1:real^2->real^3`;
                       `y1:real^3`; `kk1:real^3->bool`; `V0:real^2`; `V2:real^2`;
                       `w2:real^2`; `l2:real^2->real^3`; `y2:real^3`; `kk2:real^3->bool`]
    MOI_S3SO_LC_CORE) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC));;

(* ------------------------------------------------------------------------- *)
(* Part 16: the type of a transition circle map.  One triple of             *)
(* distinct points whose cyclic order is kept or flipped according to a     *)
(* boolean decides between CYCPRES and CYCREV (O1 of pc_moi_s33_circ).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_CYC_TOT = prove
 (`!x y z:real^2.
     x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
     z IN relative_frontier std_triangle /\ ~(x = y) /\ ~(y = z) /\ ~(x = z)
     ==> (moi_s3ci_cyc x y z \/ moi_s3ci_cyc z y x) /\
         ~(moi_s3ci_cyc x y z /\ moi_s3ci_cyc z y x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3ci_cyc; MOI_S3CI_CYC3_NOT_BOTH] THEN
  SUBGOAL_THEN `~(moi_lsp_tau x = moi_lsp_tau y) /\ ~(moi_lsp_tau y = moi_lsp_tau z) /\
                ~(moi_lsp_tau x = moi_lsp_tau z)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_S3CI_TAU_INJ]; REWRITE_TAC[moi_s3ci_cyc3] THEN REAL_ARITH_TAC]);;

let MOI_S3SO_TYPE = prove
 (`!(g:real^2->real^2) a b c e.
     g continuous_on relative_frontier std_triangle /\
     IMAGE g (relative_frontier std_triangle) = relative_frontier std_triangle /\
     (!x y. x IN relative_frontier std_triangle /\ y IN relative_frontier std_triangle /\
            g x = g y ==> x = y) /\
     a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\
     c IN relative_frontier std_triangle /\ ~(a = b) /\ ~(b = c) /\ ~(a = c) /\
     (moi_s3ci_cyc (g a) (g b) (g c) <=> (moi_s3ci_cyc a b c <=> e))
     ==> (e ==> moi_s3ci_cycpres g) /\ (~e ==> moi_s3ci_cycrev g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^2) a IN relative_frontier std_triangle /\
                g b IN relative_frontier std_triangle /\
                g c IN relative_frontier std_triangle /\
                ~(g a = g b) /\ ~(g b = g c) /\ ~(g a = g c)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s3ci_cyc ((g:real^2->real^2) a) (g b) (g c) <=>
               (moi_s3ci_cyc a b c <=> e)` THEN
  MP_TAC(SPEC `g:real^2->real^2` MOI_S3CI_DICHOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `g:real^2->real^2` MOI_S3CI_EXCL) THEN
  MP_TAC(SPECL [`a:real^2`; `b:real^2`; `c:real^2`] MOI_S3SO_CYC_TOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`(g:real^2->real^2) a`; `(g:real^2->real^2) b`; `(g:real^2->real^2) c`]
    MOI_S3SO_CYC_TOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(moi_s3ci_cyc a b c /\ moi_s3ci_cyc ((g:real^2->real^2) a) (g b) (g c)
     ==> moi_s3ci_cycpres g) /\
    (moi_s3ci_cyc c b a /\ moi_s3ci_cyc ((g:real^2->real^2) c) (g b) (g a)
     ==> moi_s3ci_cycpres g) /\
    (moi_s3ci_cycpres g /\ moi_s3ci_cyc a b c
     ==> moi_s3ci_cyc ((g:real^2->real^2) a) (g b) (g c)) /\
    (moi_s3ci_cycpres g /\ moi_s3ci_cyc c b a
     ==> moi_s3ci_cyc ((g:real^2->real^2) c) (g b) (g a))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN STRIP_TAC THENL
     [MATCH_MP_TAC MOI_S3CI_LOCAL_DEF THEN
      MAP_EVERY EXISTS_TAC [`a:real^2`; `b:real^2`; `c:real^2`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3CI_LOCAL_DEF THEN
      MAP_EVERY EXISTS_TAC [`c:real^2`; `b:real^2`; `a:real^2`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s3ci_cycpres (g:real^2->real^2)` THEN
      REWRITE_TAC[moi_s3ci_cycpres] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s3ci_cycpres (g:real^2->real^2)` THEN
      REWRITE_TAC[moi_s3ci_cycpres] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONV_TAC TAUT);;

(* The transition circle map of two embedded models along their common   *)
(* frontier circle J (parametrized through the frontier rectangles): its  *)
(* type is decided by the sign constants and the rectangle kinds.         *)

let MOI_S3SO_GAMMA = prove
 (`!(m:(real^3->bool)->bool) i k1 k2 (G1:real^2->real^3) G1' (G2:real^2->real^3) G2'
    (A1:real^3->bool) A2 J a1 b1 kap1 a2 b2 kap2 bb1 bb2
    (psi1':real^2->real^2) (psi2':real^2->real^2).
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     A1 SUBSET UNIONS m /\ A2 SUBSET UNIONS m /\
     pl_homeomorphism (holed_disk_model k1,A1) (G1,G1') /\
     pl_homeomorphism (holed_disk_model k2,A2) (G2,G2') /\ A1 INTER A2 = J /\
     moi_s3so_frect k1 a1 b1 kap1 /\ IMAGE G1 (relative_frontier(interval[a1,b1])) = J /\
     moi_s3so_frect k2 a2 b2 kap2 /\ IMAGE G2 (relative_frontier(interval[a2,b2])) = J /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k1 /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G1 x = l x + y)
                  ==> ((moi_s3so_pos i (G1 u) (G1 v) (G1 w) <=> &0 < moi_s3so_det u v w) <=>
                       bb1)) /\
     (!u v w l y. ~collinear {u,v,w} /\ convex hull {u,v,w} SUBSET holed_disk_model k2 /\
                  linear l /\ (!x. x IN convex hull {u,v,w} ==> G2 x = l x + y)
                  ==> ((moi_s3so_pos i (G2 u) (G2 v) (G2 w) <=> &0 < moi_s3so_det u v w) <=>
                       bb2)) /\
     pl_homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a1,b1]))
                      (moi_s3so_rpsi a1 b1,psi1') /\
     (!y. y IN relative_frontier(interval[a1,b1])
          ==> moi_lsp_tau (psi1' y) = moi_s3so_rtau a1 b1 y) /\
     pl_homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a2,b2]))
                      (moi_s3so_rpsi a2 b2,psi2') /\
     (!y. y IN relative_frontier(interval[a2,b2])
          ==> moi_lsp_tau (psi2' y) = moi_s3so_rtau a2 b2 y)
     ==> (~(kap1 <=> bb1 <=> kap2 <=> bb2)
          ==> moi_s3ci_cycpres (psi2' o G2' o G1 o moi_s3so_rpsi a1 b1)) /\
         ((kap1 <=> bb1 <=> kap2 <=> bb2)
          ==> moi_s3ci_cycrev (psi2' o G2' o G1 o moi_s3so_rpsi a1 b1))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^3->bool. k IN m ==> polytope k` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k1`; `A1:real^3->bool`; `G1:real^2->real^3`;
                 `G1':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k2`; `A2:real^3->bool`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC(CONJUNCT1(SPEC `k1:num` MOI_FSB_HD_POLY)) THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c1:(real^2->bool)->bool`; `m:(real^3->bool)->bool`; `G1:real^2->real^3`]
    MOI_S3SO_REFINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(CONJUNCT1(SPEC `k2:num` MOI_FSB_HD_POLY)) THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c2:(real^2->bool)->bool`; `m:(real^3->bool)->bool`; `G2:real^2->real^3`]
    MOI_S3SO_REFINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(real^2->bool)->bool` STRIP_ASSUME_TAC)) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k1:num`; `k2:num`;
                 `G1:real^2->real^3`; `G1':real^3->real^2`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`; `A1:real^3->bool`; `A2:real^3->bool`; `J:real^3->bool`;
                 `t1:(real^2->bool)->bool`; `t2:(real^2->bool)->bool`;
                 `a1:real^2`; `b1:real^2`; `kap1:bool`; `a2:real^2`; `b2:real^2`; `kap2:bool`;
                 `bb1:bool`; `bb2:bool`] MOI_S3SO_LOCAL_CONFIG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^3` (X_CHOOSE_THEN `p2:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))) THEN
  (SUBGOAL_THEN `relative_frontier(interval[a1:real^2,b1]) SUBSET holed_disk_model k1 /\
                relative_frontier(interval[a2:real^2,b2]) SUBSET holed_disk_model k2 /\
                (J:real^3->bool) SUBSET A1 /\ J SUBSET A2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier(holed_disk_model k1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THEN
        EXISTS_TAC `kap1:bool` THEN ASM_REWRITE_TAC[];
        MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier(holed_disk_model k2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THEN
        EXISTS_TAC `kap2:bool` THEN ASM_REWRITE_TAC[];
        MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]];
      UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN SET_TAC[];
      UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN SET_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a1,b1]))
                  (moi_s3so_rpsi a1 b1,psi1':real^2->real^2) /\
    homeomorphism (relative_frontier(interval[a1,b1]),J) (G1:real^2->real^3,G1') /\
    homeomorphism (J,relative_frontier(interval[a2,b2])) (G2':real^3->real^2,G2) /\
    homeomorphism (relative_frontier(interval[a2,b2]),relative_frontier std_triangle)
                  (psi2':real^2->real^2,moi_s3so_rpsi a2 b2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (relative_frontier std_triangle,
                     relative_frontier(interval[a1,b1])) (moi_s3so_rpsi a1 b1,psi1':real^2->real^2)` THEN
      SIMP_TAC[pl_homeomorphism];
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`holed_disk_model k1`; `A1:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pl_homeomorphism (holed_disk_model k1,A1) (G1:real^2->real^3,G1')` THEN
      SIMP_TAC[pl_homeomorphism];
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`holed_disk_model k2`; `A2:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pl_homeomorphism (holed_disk_model k2,A2) (G2:real^2->real^3,G2')` THEN
      SIMP_TAC[pl_homeomorphism];
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
      UNDISCH_TAC `pl_homeomorphism (relative_frontier std_triangle,
                     relative_frontier(interval[a2,b2])) (moi_s3so_rpsi a2 b2,psi2':real^2->real^2)` THEN
      SIMP_TAC[pl_homeomorphism]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                  ((psi2':real^2->real^2) o (G2':real^3->real^2) o (G1:real^2->real^3) o
                   moi_s3so_rpsi a1 b1,
                   (((psi1':real^2->real^2) o (G1':real^3->real^2)) o (G2:real^2->real^3)) o
                   moi_s3so_rpsi a2 b2)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier(interval[a2:real^2,b2])` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `J:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier(interval[a1:real^2,b1])` THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (ABBREV_TAC `gam = (psi2':real^2->real^2) o (G2':real^3->real^2) o (G1:real^2->real^3) o
                    moi_s3so_rpsi a1 b1` THEN
  ABBREV_TAC `gami = (((psi1':real^2->real^2) o (G1':real^3->real^2)) o
                      (G2:real^2->real^3)) o moi_s3so_rpsi a2 b2`) THEN
  (SUBGOAL_THEN `(gam:real^2->real^2) continuous_on relative_frontier std_triangle /\
                IMAGE gam (relative_frontier std_triangle) = relative_frontier std_triangle /\
                (!x y. x IN relative_frontier std_triangle /\
                       y IN relative_frontier std_triangle /\
                       gam x = gam y ==> x = y)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                  (gam:real^2->real^2,gami)` THEN
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `!y. y IN J
        ==> (psi1':real^2->real^2) ((G1':real^3->real^2) y) IN relative_frontier std_triangle /\
            moi_lsp_tau (psi1' (G1' y)) = moi_s3so_rtau a1 b1 (G1' y) /\
            moi_lsp_tau ((gam:real^2->real^2) (psi1' (G1' y))) =
            moi_s3so_rtau a2 b2 ((G2':real^3->real^2) y)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G1':real^3->real^2) y IN relative_frontier(interval[a1,b1]) /\
                  (G1:real^2->real^3) (G1' y) = y /\
                  (G2':real^3->real^2) y IN relative_frontier(interval[a2,b2])`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`homeomorphism (relative_frontier(interval[a1,b1]),J) (G1:real^2->real^3,G1')`;
        `homeomorphism (J,relative_frontier(interval[a2,b2])) (G2':real^3->real^2,G2)`;
        `(y:real^3) IN J`] THEN
      REWRITE_TAC[HOMEOMORPHISM] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi1':real^2->real^2) ((G1':real^3->real^2) y) IN
                  relative_frontier std_triangle /\
                  moi_s3so_rpsi a1 b1 (psi1' (G1' y)) = G1' y` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a1,b1]))
                       (moi_s3so_rpsi a1 b1,psi1':real^2->real^2)`;
        `(G1':real^3->real^2) y IN relative_frontier(interval[a1,b1])`] THEN
      REWRITE_TAC[HOMEOMORPHISM] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "gam" THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y. y IN relative_frontier(interval[a1,b1])
                              ==> moi_lsp_tau ((psi1':real^2->real^2) y) =
                                  moi_s3so_rtau a1 b1 y`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ASSUME `!y. y IN relative_frontier(interval[a2,b2])
                              ==> moi_lsp_tau ((psi2':real^2->real^2) y) =
                                  moi_s3so_rtau a2 b2 y`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `!y y'. y IN J /\ y' IN J /\
                       (psi1':real^2->real^2) ((G1':real^3->real^2) y) = psi1' (G1' y')
                       ==> y = y'` (LABEL_TAC "pinj") THENL
   [MAP_EVERY UNDISCH_TAC
     [`homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a1,b1]))
                     (moi_s3so_rpsi a1 b1,psi1':real^2->real^2)`;
      `homeomorphism (relative_frontier(interval[a1,b1]),J) (G1:real^2->real^3,G1')`] THEN
    REWRITE_TAC[HOMEOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p0:real^3 = midpoint(p0,p2)) /\ ~(midpoint(p0,p2) = p2)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT]; ALL_TAC]) THEN
  (USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p0:real^3) IN J`)) THEN
                            MP_TAC(MATCH_MP th (ASSUME `midpoint(p0:real^3,p2) IN J`)) THEN
                            MP_TAC(MATCH_MP th (ASSUME `(p2:real^3) IN J`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (SUBST1_TAC o SYM))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (SUBST1_TAC o SYM))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (SUBST1_TAC o SYM))) THEN
  DISCH_TAC) THEN
  (MP_TAC(ISPECL [`gam:real^2->real^2`; `(psi1':real^2->real^2) ((G1':real^3->real^2) p0)`;
                 `(psi1':real^2->real^2) ((G1':real^3->real^2) (midpoint(p0,p2)))`;
                 `(psi1':real^2->real^2) ((G1':real^3->real^2) p2)`;
                 `~(kap1 <=> bb1 <=> kap2 <=> bb2)`] MOI_S3SO_TYPE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN UNDISCH_TAC `~(p0:real^3 = midpoint(p0,p2))` THEN REWRITE_TAC[] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(midpoint(p0:real^3,p2) = p2)` THEN REWRITE_TAC[] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(p0:real^3 = p2)` THEN REWRITE_TAC[] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      PURE_REWRITE_TAC[moi_s3ci_cyc] THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* Part 17: DIR.  The transition circle maps of the two models in s          *)
(* and in s' have the same type (SP_SIGN_EQ, GAMMA), so the circle map      *)
(* j' o f2' o f1 o j (j = G1 o rpsi) is orientation preserving.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SO_TRANS_HOMEO = prove
 (`!(G1:real^2->real^N) G1' (G2:real^2->real^N) G2' (M1:real^2->bool) M2
    (A1:real^N->bool) A2 J C1 C2 (psi1:real^2->real^2) psi1' (psi2:real^2->real^2) psi2'.
     homeomorphism (M1,A1) (G1,G1') /\ homeomorphism (M2,A2) (G2,G2') /\
     C1 SUBSET M1 /\ C2 SUBSET M2 /\ J SUBSET A1 /\ J SUBSET A2 /\
     IMAGE G1 C1 = J /\ IMAGE G2 C2 = J /\
     homeomorphism (relative_frontier std_triangle,C1) (psi1,psi1') /\
     homeomorphism (relative_frontier std_triangle,C2) (psi2,psi2')
     ==> homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
           (psi2' o G2' o G1 o psi1,((psi1' o G1') o G2) o psi2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `C2:real^2->bool` THEN
  CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `J:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `C1:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`M1:real^2->bool`; `A1:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`M2:real^2->bool`; `A2:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

(* The pointwise identity behind q = gamma^-1 o gamma' on J. *)

let MOI_S3SO_PTWISE_ID = prove
 (`!(G2:real^2->real^N) G2' (f1:real^N->real^N) f2 f2'
    (psi2:real^2->real^2) psi2' (A2:real^N->bool) J J' C2 y.
     y IN J /\ IMAGE f1 J = J' /\ IMAGE f2 J = J' /\ J SUBSET A2 /\
     (!u. u IN A2 ==> f2' (f2 u) = u) /\
     IMAGE G2 C2 = J /\ (!c. c IN C2 ==> G2' (G2 c) = c) /\
     (!c. c IN C2 ==> psi2 (psi2' c) = c)
     ==> f2' (f1 y) IN J /\ G2 (psi2 (psi2' (G2' (f2' (f1 y))))) = f2' (f1 y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u:real^N. u IN J /\ (f1:real^N->real^N) y = f2 u` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f2:real^N->real^N) J = J'` THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^N) J = J'` THEN
    UNDISCH_TAC `(y:real^N) IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f2':real^N->real^N) (f1 (y:real^N)) = u` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?c. c IN C2 /\ (u:real^N) = (G2:real^2->real^N) c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (G2:real^2->real^N) C2 = J` THEN UNDISCH_TAC `(u:real^N) IN J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* DIR, internal form: side-preserving piece maps f1, f2 agreeing setwise *)
(* on the common frontier circle J give an orientation-preserving circle  *)
(* map j' o f2' o f1 o j for the parametrization j = G1 o rpsi.           *)

let MOI_S3SO_DIR_INT = prove
 (`!(m:(real^3->bool)->bool) (m':(real^3->bool)->bool) (i:real^3->bool) (i':real^3->bool)
    (A1:real^3->bool) (A2:real^3->bool) (A1':real^3->bool) (A2':real^3->bool)
    (J:real^3->bool) (J':real^3->bool) k1 k2
    (G1:real^2->real^3) (G1':real^3->real^2) (G2:real^2->real^3) (G2':real^3->real^2)
    (f1:real^3->real^3) (f1':real^3->real^3) (f2:real^3->real^3) (f2':real^3->real^3).
     FINITE m /\ combinatorial_manifold 2 m /\ moi_s3so_sided (UNIONS m) i /\
     FINITE m' /\ combinatorial_manifold 2 m' /\ moi_s3so_sided (UNIONS m') i' /\
     A1 SUBSET UNIONS m /\ A2 SUBSET UNIONS m /\ A1' SUBSET UNIONS m' /\ A2' SUBSET UNIONS m' /\
     pl_homeomorphism (holed_disk_model k1,A1) (G1,G1') /\
     pl_homeomorphism (holed_disk_model k2,A2) (G2,G2') /\
     A1 INTER A2 = J /\ A1' INTER A2' = J' /\ pl_sphere 1 J /\
     J SUBSET IMAGE G1 (frontier (holed_disk_model k1)) /\
     J SUBSET IMAGE G2 (frontier (holed_disk_model k2)) /\
     pl_homeomorphism (A1,A1') (f1,f1') /\ pl_homeomorphism (A2,A2') (f2,f2') /\
     IMAGE f1 J = J' /\ IMAGE f2 J = J' /\
     moi_s3so_sp i i' A1 f1 /\ moi_s3so_sp i i' A2 f2
     ==> ?(j:real^2->real^3) (j':real^3->real^2).
           pl_homeomorphism (relative_frontier std_triangle,J) (j,j') /\
           moi_s3ci_cycpres (j' o f2' o f1 o j)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k1`; `A1:real^3->bool`; `G1:real^2->real^3`;
                 `G1':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k2`; `A2:real^3->bool`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A1:real^3->bool`; `A1':real^3->bool`; `f1:real^3->real^3`;
                 `f1':real^3->real^3`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A2:real^3->bool`; `A2':real^3->bool`; `f2:real^3->real^3`;
                 `f2':real^3->real^3`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC(ISPECL [`k1:num`; `G1:real^2->real^3`; `G1':real^3->real^2`; `A1:real^3->bool`;
                 `J:real^3->bool`] MOI_S3SO_FRONT_CIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^2` (X_CHOOSE_THEN `b1:real^2`
    (X_CHOOSE_THEN `kap1:bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k2:num`; `G2:real^2->real^3`; `G2':real^3->real^2`; `A2:real^3->bool`;
                 `J:real^3->bool`] MOI_S3SO_FRONT_CIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^2` (X_CHOOSE_THEN `b2:real^2`
    (X_CHOOSE_THEN `kap2:bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(a1:real^2)$1 < (b1:real^2)$1 /\ a1$2 < b1$2 /\
                (a2:real^2)$1 < (b2:real^2)$1 /\ a2$2 < b2$2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`k1:num`; `a1:real^2`; `b1:real^2`; `kap1:bool`] MOI_S3SO_FRECT_LT) THEN
    MP_TAC(SPECL [`k2:num`; `a2:real^2`; `b2:real^2`; `kap2:bool`] MOI_S3SO_FRECT_LT) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^2`; `b1:real^2`] MOI_S3SO_RPSI_PLH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi1':real^2->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a2:real^2`; `b2:real^2`] MOI_S3SO_RPSI_PLH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi2':real^2->real^2` STRIP_ASSUME_TAC)) THEN
  (SUBGOAL_THEN `pl_homeomorphism (holed_disk_model k1,A1')
                  ((f1:real^3->real^3) o (G1:real^2->real^3),
                   (G1':real^3->real^2) o (f1':real^3->real^3)) /\
                pl_homeomorphism (holed_disk_model k2,A2')
                  ((f2:real^3->real^3) o (G2:real^2->real^3),
                   (G2':real^3->real^2) o (f2':real^3->real^3))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THENL
     [EXISTS_TAC `A1:real^3->bool`; EXISTS_TAC `A2:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`holed_disk_model k1`; `A1':real^3->bool`;
                 `(f1:real^3->real^3) o (G1:real^2->real^3)`;
                 `(G1':real^3->real^2) o (f1':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`holed_disk_model k2`; `A2':real^3->bool`;
                 `(f2:real^3->real^3) o (G2:real^2->real^3)`;
                 `(G2':real^3->real^2) o (f2':real^3->real^3)`] MOI_S3SO_PLH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k1:num`; `G1:real^2->real^3`]
    MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `bb1:bool`)] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k2:num`; `G2:real^2->real^3`]
    MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `bb2:bool`)] THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k1:num`;
                 `(f1:real^3->real^3) o (G1:real^2->real^3)`] MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb1':bool` (fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(REWRITE_RULE[o_THM] th))) THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k2:num`;
                 `(f2:real^3->real^3) o (G2:real^2->real^3)`] MOI_S3SO_MODEL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb2':bool` (fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(REWRITE_RULE[o_THM] th)))) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `i:real^3->bool`;
                 `i':real^3->bool`; `k1:num`; `G1:real^2->real^3`; `G1':real^3->real^2`;
                 `A1:real^3->bool`; `A1':real^3->bool`; `f1:real^3->real^3`;
                 `f1':real^3->real^3`; `bb1:bool`; `bb1':bool`] MOI_S3SO_SP_SIGN_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `i:real^3->bool`;
                 `i':real^3->bool`; `k2:num`; `G2:real^2->real^3`; `G2':real^3->real^2`;
                 `A2:real^3->bool`; `A2':real^3->bool`; `f2:real^3->real^3`;
                 `f2':real^3->real^3`; `bb2:bool`; `bb2':bool`] MOI_S3SO_SP_SIGN_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC]) THEN
  (MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `i:real^3->bool`; `k1:num`; `k2:num`;
                 `G1:real^2->real^3`; `G1':real^3->real^2`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`; `A1:real^3->bool`; `A2:real^3->bool`; `J:real^3->bool`;
                 `a1:real^2`; `b1:real^2`; `kap1:bool`; `a2:real^2`; `b2:real^2`; `kap2:bool`;
                 `bb1:bool`; `bb2:bool`; `psi1':real^2->real^2`; `psi2':real^2->real^2`]
    MOI_S3SO_GAMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`m':(real^3->bool)->bool`; `i':real^3->bool`; `k1:num`; `k2:num`;
                 `(f1:real^3->real^3) o (G1:real^2->real^3)`;
                 `(G1':real^3->real^2) o (f1':real^3->real^3)`;
                 `(f2:real^3->real^3) o (G2:real^2->real^3)`;
                 `(G2':real^3->real^2) o (f2':real^3->real^3)`;
                 `A1':real^3->bool`; `A2':real^3->bool`; `J':real^3->bool`;
                 `a1:real^2`; `b1:real^2`; `kap1:bool`; `a2:real^2`; `b2:real^2`; `kap2:bool`;
                 `bb1:bool`; `bb2:bool`; `psi1':real^2->real^2`; `psi2':real^2->real^2`]
    MOI_S3SO_GAMMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; STRIP_TAC]) THEN
  (SUBGOAL_THEN `relative_frontier(interval[a1:real^2,b1]) SUBSET holed_disk_model k1 /\
                relative_frontier(interval[a2:real^2,b2]) SUBSET holed_disk_model k2 /\
                (J:real^3->bool) SUBSET A1 /\ J SUBSET A2 /\
                (J':real^3->bool) SUBSET A1' /\ J' SUBSET A2'` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier(holed_disk_model k1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THEN
        EXISTS_TAC `kap1:bool` THEN ASM_REWRITE_TAC[];
        MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier(holed_disk_model k2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN MATCH_MP_TAC MOI_S3SO_FRECT_COMPONENT THEN
        EXISTS_TAC `kap2:bool` THEN ASM_REWRITE_TAC[];
        MESON_TAC[FRONTIER_SUBSET_CLOSED; MOI_FSB_HD_POLY; COMPACT_IMP_CLOSED]];
      UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN SET_TAC[];
      UNDISCH_TAC `(A1:real^3->bool) INTER A2 = J` THEN SET_TAC[];
      UNDISCH_TAC `(A1':real^3->bool) INTER A2' = J'` THEN SET_TAC[];
      UNDISCH_TAC `(A1':real^3->bool) INTER A2' = J'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (holed_disk_model k1,A1) (G1:real^2->real^3,G1') /\
    homeomorphism (holed_disk_model k2,A2) (G2:real^2->real^3,G2') /\
    homeomorphism (holed_disk_model k1,A1')
      ((f1:real^3->real^3) o (G1:real^2->real^3),(G1':real^3->real^2) o (f1':real^3->real^3)) /\
    homeomorphism (holed_disk_model k2,A2')
      ((f2:real^3->real^3) o (G2:real^2->real^3),(G2':real^3->real^2) o (f2':real^3->real^3)) /\
    homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a1,b1]))
      (moi_s3so_rpsi a1 b1,psi1':real^2->real^2) /\
    homeomorphism (relative_frontier std_triangle,relative_frontier(interval[a2,b2]))
      (moi_s3so_rpsi a2 b2,psi2':real^2->real^2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]);
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`G1:real^2->real^3`; `G1':real^3->real^2`; `G2:real^2->real^3`;
                 `G2':real^3->real^2`; `holed_disk_model k1`; `holed_disk_model k2`;
                 `A1:real^3->bool`; `A2:real^3->bool`; `J:real^3->bool`;
                 `relative_frontier(interval[a1:real^2,b1])`;
                 `relative_frontier(interval[a2:real^2,b2])`;
                 `moi_s3so_rpsi a1 b1`; `psi1':real^2->real^2`;
                 `moi_s3so_rpsi a2 b2`; `psi2':real^2->real^2`] MOI_S3SO_TRANS_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(f1:real^3->real^3) o (G1:real^2->real^3)`;
                 `(G1':real^3->real^2) o (f1':real^3->real^3)`;
                 `(f2:real^3->real^3) o (G2:real^2->real^3)`;
                 `(G2':real^3->real^2) o (f2':real^3->real^3)`;
                 `holed_disk_model k1`; `holed_disk_model k2`;
                 `A1':real^3->bool`; `A2':real^3->bool`; `J':real^3->bool`;
                 `relative_frontier(interval[a1:real^2,b1])`;
                 `relative_frontier(interval[a2:real^2,b2])`;
                 `moi_s3so_rpsi a1 b1`; `psi1':real^2->real^2`;
                 `moi_s3so_rpsi a2 b2`; `psi2':real^2->real^2`] MOI_S3SO_TRANS_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; DISCH_TAC]) THEN
  (ABBREV_TAC `gam = (psi2':real^2->real^2) o (G2':real^3->real^2) o (G1:real^2->real^3) o
                    moi_s3so_rpsi a1 b1` THEN
  ABBREV_TAC `gami = (((psi1':real^2->real^2) o (G1':real^3->real^2)) o
                      (G2:real^2->real^3)) o moi_s3so_rpsi a2 b2` THEN
  ABBREV_TAC `gam' = (psi2':real^2->real^2) o ((G2':real^3->real^2) o (f2':real^3->real^3)) o
                     ((f1:real^3->real^3) o (G1:real^2->real^3)) o moi_s3so_rpsi a1 b1` THEN
  ABBREV_TAC `gami' = (((psi1':real^2->real^2) o ((G1':real^3->real^2) o (f1':real^3->real^3))) o
                       ((f2:real^3->real^3) o (G2:real^2->real^3))) o moi_s3so_rpsi a2 b2`) THEN
  (SUBGOAL_THEN `(!x. x IN relative_frontier std_triangle
                     ==> (gam:real^2->real^2) x IN relative_frontier std_triangle /\
                         (gami:real^2->real^2) x IN relative_frontier std_triangle /\
                         gam (gami x) = x /\ gami (gam x) = x) /\
                (!x. x IN relative_frontier std_triangle
                     ==> (gam':real^2->real^2) x IN relative_frontier std_triangle)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                     (gam:real^2->real^2,gami)`;
      `homeomorphism (relative_frontier std_triangle,relative_frontier std_triangle)
                     (gam':real^2->real^2,gami')`] THEN
    REWRITE_TAC[HOMEOMORPHISM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3ci_cycpres ((gami:real^2->real^2) o (gam':real^2->real^2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`gam:real^2->real^2`; `gami:real^2->real^2`] MOI_S3CI_INVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`gam':real^2->real^2`; `gami:real^2->real^2`] MOI_S3CI_COMPOSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(kap1 <=> bb1 <=> kap2 <=> bb2) ==> moi_s3ci_cycpres (gam:real^2->real^2)`;
      `(kap1 <=> bb1 <=> kap2 <=> bb2) ==> moi_s3ci_cycrev (gam:real^2->real^2)`;
      `~(kap1 <=> bb1 <=> kap2 <=> bb2) ==> moi_s3ci_cycpres (gam':real^2->real^2)`;
      `(kap1 <=> bb1 <=> kap2 <=> bb2) ==> moi_s3ci_cycrev (gam':real^2->real^2)`] THEN
    CONV_TAC TAUT;
    ALL_TAC]) THEN
  (EXISTS_TAC `(G1:real^2->real^3) o moi_s3so_rpsi a1 b1` THEN
  EXISTS_TAC `(psi1':real^2->real^2) o (G1':real^3->real^2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier(interval[a1:real^2,b1])` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (G1:real^2->real^3) (relative_frontier(interval[a1,b1])) = J` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`holed_disk_model k1`; `A1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`relative_frontier(interval[a1:real^2,b1])`;
                         `psi1':real^2->real^2`] PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL) THEN
    UNDISCH_TAC `pl_homeomorphism (relative_frontier std_triangle,
                   relative_frontier(interval[a1,b1])) (moi_s3so_rpsi a1 b1,psi1':real^2->real^2)` THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`(gami:real^2->real^2) o (gam':real^2->real^2)`;
                 `((psi1':real^2->real^2) o (G1':real^3->real^2)) o (f2':real^3->real^3) o
                  (f1:real^3->real^3) o (G1:real^2->real^3) o moi_s3so_rpsi a1 b1`]
    MOI_S3CI_PTWISE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s3so_rpsi a1 b1 x IN relative_frontier(interval[a1:real^2,b1])`
    ASSUME_TAC THENL
     [UNDISCH_TAC `homeomorphism (relative_frontier std_triangle,
                     relative_frontier(interval[a1,b1])) (moi_s3so_rpsi a1 b1,psi1':real^2->real^2)` THEN
      REWRITE_TAC[HOMEOMORPHISM] THEN
      UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G1:real^2->real^3) (moi_s3so_rpsi a1 b1 x) IN J` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (G1:real^2->real^3) (relative_frontier(interval[a1,b1])) = J` THEN
      UNDISCH_TAC `moi_s3so_rpsi a1 b1 x IN relative_frontier(interval[a1:real^2,b1])` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G2:real^2->real^3`; `G2':real^3->real^2`; `f1:real^3->real^3`;
                   `f2:real^3->real^3`; `f2':real^3->real^3`; `moi_s3so_rpsi a2 b2`;
                   `psi2':real^2->real^2`; `A2:real^3->bool`; `J:real^3->bool`;
                   `J':real^3->bool`; `relative_frontier(interval[a2:real^2,b2])`;
                   `(G1:real^2->real^3) (moi_s3so_rpsi a1 b1 x)`] MOI_S3SO_PTWISE_ID) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [X_GEN_TAC `c:real^2` THEN DISCH_TAC THEN
        MATCH_MP_TAC(ASSUME `!x. x IN holed_disk_model k2
                                 ==> (G2':real^3->real^2) ((G2:real^2->real^3) x) = x`) THEN
        UNDISCH_TAC `relative_frontier(interval[a2:real^2,b2]) SUBSET holed_disk_model k2` THEN
        UNDISCH_TAC `(c:real^2) IN relative_frontier(interval[a2,b2])` THEN SET_TAC[];
        UNDISCH_TAC `homeomorphism (relative_frontier std_triangle,
                       relative_frontier(interval[a2,b2])) (moi_s3so_rpsi a2 b2,psi2':real^2->real^2)` THEN
        SIMP_TAC[HOMEOMORPHISM]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    EXPAND_TAC "gami" THEN EXPAND_TAC "gam'" THEN REWRITE_TAC[o_THM] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC]));;

(* O4 DIR: the statement MOI_S3MT_SORIENT_DIR_TERM. *)

let MOI_S3SO_DIR = prove
 (MOI_S3MT_SORIENT_DIR_TERM,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "e") (CONJUNCTS_THEN2 (LABEL_TAC "e'") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `moi_s3so_sided s i /\ moi_s3so_sided s' i'` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3so_sided] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (let l = lhs(concl th) in is_comb l && fst(dest_const(rator l)) = "UNIONS")))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m':(real^3->bool)->bool`; `i:real^3->bool`;
                 `i':real^3->bool`; `A1:real^3->bool`; `A2:real^3->bool`;
                 `A1':real^3->bool`; `A2':real^3->bool`; `J:real^3->bool`; `J':real^3->bool`;
                 `k1:num`; `k2:num`; `G1:real^2->real^3`; `G1':real^3->real^2`;
                 `G2:real^2->real^3`; `G2':real^3->real^2`; `f1:real^3->real^3`;
                 `f1':real^3->real^3`; `f2:real^3->real^3`; `f2':real^3->real^3`]
    MOI_S3SO_DIR_INT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s3so_sp; moi_s3so_pos]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3ci_cycpres; moi_s3ci_cyc; moi_s3ci_cyc3]);;

